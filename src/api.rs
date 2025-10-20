//! Integration API for One-Sided GS PVUGC

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{CurveGroup, AffineRepr};
use ark_groth16::{Proof as Groth16Proof, VerifyingKey as Groth16VK};
use ark_ff::One;

use crate::{
    RowBases, Arms, OneSidedCommitments,
    compute_groth16_target, build_row_bases_from_vk, arm_rows, decap_one_sided,
    DlrepBProof, DlrepTieProof,
};
pub use crate::ppe::{PvugcVk, validate_pvugc_vk_subgroups};
use crate::dlrep::{verify_b_msm, verify_tie_aggregated};

/// Complete PVUGC bundle
pub struct PvugcBundle<E: Pairing> {
    pub groth16_proof: Groth16Proof<E>,
    pub dlrep_b: DlrepBProof<E>,
    pub dlrep_tie: DlrepTieProof<E>,
    pub gs_commitments: OneSidedCommitments<E>,
}

/// Main API for one-sided PVUGC
pub struct OneSidedPvugc;

impl OneSidedPvugc {
    /// Setup and arm at deposit time
    /// Returns: (RowBases, Arms, R, K=R^ρ)
    pub fn setup_and_arm<E: Pairing>(
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
        rho: &E::ScalarField,
        gamma: Vec<Vec<E::ScalarField>>,
    ) -> (RowBases<E>, Arms<E>, PairingOutput<E>, PairingOutput<E>) {
        // Compute target R(vk, vault_utxo)
        let r = compute_groth16_target(vk, public_inputs);
        
        // Build row bases from PVUGC-VK wrapper + Groth16 VK
        let (y_bases, delta, _) = crate::build_one_sided_ppe(pvugc_vk, vk, public_inputs);
        let rows = build_row_bases_from_vk(&y_bases, delta, gamma);
        
        // Arm with ρ
        let arms = arm_rows(&rows, rho);
        
        // Compute K = R^ρ for address generation
        let k = Self::compute_r_to_rho(&r, rho);
        
        (rows, arms, r, k)
    }
    
    /// Verify complete bundle
    pub fn verify<E: Pairing>(
        bundle: &PvugcBundle<E>,
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
        gamma: &[Vec<E::ScalarField>],
    ) -> bool {
        
        // 0. Basic guards
        if !validate_pvugc_vk_subgroups(pvugc_vk) { 
            return false; 
        }
        
        // 1. Verify Groth16 proof (standard)
        use ark_groth16::Groth16;
        use ark_snark::SNARK;
        
        let groth16_valid = Groth16::<E>::verify(vk, public_inputs, &bundle.groth16_proof)
            .unwrap_or(false);
        
        if !groth16_valid {
            return false;
        }
        
        // 2. Verify DLREP_B against B' = B - β₂ - query[0]
        
        // Subtract BOTH constants (β₂ and query[0])
        let b_prime = (bundle.groth16_proof.b.into_group()
                     - pvugc_vk.beta_g2.into_group()
                     - pvugc_vk.b_g2_query[0].into_group()).into_affine();
        
        // Verify over b_g2_query[1..] only (variable part)
        let dlrep_b_ok = verify_b_msm::<E>(b_prime, &pvugc_vk.b_g2_query[1..], pvugc_vk.delta_g2, &bundle.dlrep_b);
        if !dlrep_b_ok { 
            return false; 
        }
        
        // 3. Verify aggregated same-scalar tie over G1
        use ark_ff::Zero;
        let a = bundle.groth16_proof.a;
        
        // Simple aggregation: sum of first limbs
        let mut x_agg = <E as Pairing>::G1::zero();
        for (c_limb0, _) in &bundle.gs_commitments.c_rows {
            x_agg += c_limb0.into_group();
        }
        let x_agg = x_agg.into_affine();
        
        let dlrep_tie_ok = verify_tie_aggregated::<E>(a, x_agg, &bundle.dlrep_tie);
        if !dlrep_tie_ok { 
            return false; 
        }
        
        // 4. Verify one-sided GS PPE equals R(vk,x)
        let r_target = compute_groth16_target(vk, public_inputs);
        
        // Build Y bases: [β] ∪ b_g2_query
        let mut y_bases = vec![pvugc_vk.beta_g2];
        y_bases.extend_from_slice(&pvugc_vk.b_g2_query);
        
        let rows: RowBases<E> = build_row_bases_from_vk(&y_bases, pvugc_vk.delta_g2, gamma.to_vec());
        
        // Initialize with ONE (multiplicative identity), not zero!
        let mut lhs = PairingOutput::<E>(One::one());
        for ((c_limb0, c_limb1), u_row) in bundle.gs_commitments.c_rows.iter().zip(&rows.u_rows) {
            lhs += E::pairing(*c_limb0, *u_row);
            lhs += E::pairing(*c_limb1, *u_row);
        }
        for (theta_limb0, theta_limb1) in &bundle.gs_commitments.theta {
            lhs += E::pairing(*theta_limb0, pvugc_vk.delta_g2);
            lhs += E::pairing(*theta_limb1, pvugc_vk.delta_g2);
        }
        
        // This provides e(+sA, δ) to cancel -sA in e(-C, δ)
        lhs += E::pairing(bundle.gs_commitments.c_delta.0, pvugc_vk.delta_g2);
        lhs += E::pairing(bundle.gs_commitments.c_delta.1, pvugc_vk.delta_g2);
        
        // Guard: LHS should not be identity
        if lhs == PairingOutput::<E>(One::one()) { 
            return false; 
        }
        
        // Check: LHS == R
        if lhs != r_target { 
            return false; 
        }
        
        true
    }
    
    /// Decapsulate to get K = R^ρ
    pub fn decapsulate<E: Pairing>(
        commitments: &OneSidedCommitments<E>,
        arms: &Arms<E>,
    ) -> PairingOutput<E> {
        decap_one_sided(commitments, arms)
    }
    
    /// Helper: Compute R^ρ
    pub fn compute_r_to_rho<E: Pairing>(
        r: &PairingOutput<E>,
        rho: &E::ScalarField,
    ) -> PairingOutput<E> {
        // R^ρ via exponentiation
        // PairingOutput doesn't have pow, so we use the .0 field
        use ark_ff::Field;
        use ark_ff::PrimeField;
        
        let r_to_rho = r.0.pow(&rho.into_bigint());
        PairingOutput(r_to_rho)
    }
}

