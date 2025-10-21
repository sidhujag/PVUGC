//! Integration API for One-Sided GS PVUGC

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{CurveGroup, AffineRepr};
use ark_groth16::{Proof as Groth16Proof, VerifyingKey as Groth16VK};
use ark_ff::One;

use crate::{
    OneSidedCommitments,
    compute_groth16_target,
    DlrepBProof, DlrepTieProof,
};
use crate::arming::{ColumnBases, ColumnArms, arm_columns};
pub use crate::ppe::{PvugcVk, validate_pvugc_vk_subgroups};
use crate::dlrep::{verify_b_msm, verify_tie_aggregated};
use crate::ppe::validate_groth16_vk_subgroups;
use crate::poce::{PoceColumnProof, prove_poce_column, verify_poce_column, verify_poce_b};
use ark_std::rand::RngCore;

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
    /// Canonical setup and arming (formerly setup_and_arm_columns)
    /// Returns: (ColumnBases, ColumnArms, R, K=R^ρ)
    pub fn setup_and_arm<E: Pairing>(
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
        rho: &E::ScalarField,
    ) -> (ColumnBases<E>, ColumnArms<E>, PairingOutput<E>, PairingOutput<E>) {
        let r = compute_groth16_target(vk, public_inputs);
        let mut y_cols = vec![pvugc_vk.beta_g2];
        y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
        let bases = ColumnBases { y_cols, delta: pvugc_vk.delta_g2 };
        let col_arms = arm_columns(&bases, rho);
        let k = Self::compute_r_to_rho(&r, rho);
        (bases, col_arms, r, k)
    }

    /// Produce PoCE-A attestation for column arming (arm-time)
    /// 
    /// Proves that all column arms share the same ρ and ciphertext is key-committed
    /// to K = Poseidon2(ser(R^ρ)|ctx|GSdig)
    pub fn attest_column_arming<E: Pairing, R: RngCore>(
        bases: &ColumnBases<E>,
        col_arms: &ColumnArms<E>,
        t_i: &E::G1Affine,           // T_i = s_i G
        rho: &E::ScalarField,        // ρ_i (secret)
        s_i: &E::ScalarField,        // s_i (secret)
        ctx_hash: &[u8],             // Context hash
        gs_digest: &[u8],            // GS instance digest
        rng: &mut R,
    ) -> PoceColumnProof<E> {
        prove_poce_column::<E, R>(
            &bases.y_cols,
            &bases.delta,
            &col_arms.y_cols_rho,
            &col_arms.delta_rho,
            t_i,
            rho,
            s_i,
            ctx_hash,
            gs_digest,
            rng,
        )
    }

    /// Verify PoCE-A attestation for column arming (arm-time)
    pub fn verify_column_arming<E: Pairing>(
        bases: &ColumnBases<E>,
        col_arms: &ColumnArms<E>,
        t_i: &E::G1Affine,           // T_i = s_i G
        proof: &PoceColumnProof<E>,
        ctx_hash: &[u8],             // Context hash
        gs_digest: &[u8],            // GS instance digest
    ) -> bool {
        verify_poce_column::<E>(
            &bases.y_cols,
            &bases.delta,
            &col_arms.y_cols_rho,
            &col_arms.delta_rho,
            t_i,
            proof,
            ctx_hash,
            gs_digest,
        )
    }

    /// Verify PoCE-B key-commitment (decap-time, decapper-local)
    /// 
    /// Verifies that ciphertext is key-committed to the derived key
    pub fn verify_key_commitment<E: Pairing>(
        derived_m: &PairingOutput<E>,  // R^ρ derived from attestation
        ctx_hash: &[u8],              // Context hash
        gs_digest: &[u8],             // GS instance digest
        ct_i: &[u8],                  // Ciphertext
        tau_i: &[u8],                 // Key-commitment tag
    ) -> bool {
        verify_poce_b::<E>(derived_m, ctx_hash, gs_digest, ct_i, tau_i)
    }
    
    /// Verify complete bundle
    pub fn verify<E: Pairing>(
        bundle: &PvugcBundle<E>,
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
    ) -> bool {
        
        // 0. Basic guards
        if !validate_pvugc_vk_subgroups(pvugc_vk) { 
            return false; 
        }
        if !validate_groth16_vk_subgroups(vk) {
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
        
        // 2. Verify DLREP_B against B' = B - β₂ - Y_0, variables are b_g2_query[1..]
        let b_prime = (bundle.groth16_proof.b.into_group()
                     - pvugc_vk.beta_g2.into_group()
                     - pvugc_vk.b_g2_query[0].into_group()).into_affine();
        
        // Verify over b_g2_query[1..] only (variable part)
        let dlrep_b_ok = verify_b_msm::<E>(b_prime, &pvugc_vk.b_g2_query[1..], pvugc_vk.delta_g2, &bundle.dlrep_b);
        if !dlrep_b_ok { 
            return false; 
        }
        
        // 3. Verify aggregated same-scalar tie over G1 (tie over x_b_cols[0])
        use ark_ff::Zero;
        let a = bundle.groth16_proof.a;
        
        // Simple aggregation: sum of first limbs
        let mut x_agg = <E as Pairing>::G1::zero();
        for (c_limb0, _) in &bundle.gs_commitments.x_b_cols {
            x_agg += c_limb0.into_group();
        }
        let x_agg = x_agg.into_affine();
        
        let dlrep_tie_ok = verify_tie_aggregated::<E>(a, x_agg, &bundle.dlrep_tie);
        if !dlrep_tie_ok { 
            return false; 
        }
        
        // 4. Verify PPE equals R(vk,x) using direct column pairing
        let r_target = compute_groth16_target(vk, public_inputs);
        
        // Columns: [β₂, b_g2_query[0], b_g2_query[1..]] (δ supplied via Θ = C + sA)
        let mut y_cols = vec![pvugc_vk.beta_g2];
        y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
        if bundle.gs_commitments.x_b_cols.len() != y_cols.len() { return false; }
        if bundle.gs_commitments.theta.is_empty() { return false; }
        
        let mut lhs = PairingOutput::<E>(One::one());
        for ((x0, x1), y) in bundle.gs_commitments.x_b_cols.iter().zip(&y_cols) {
            lhs += E::pairing(*x0, *y);
            lhs += E::pairing(*x1, *y);
        }
        for (t0, t1) in &bundle.gs_commitments.theta {
            lhs += E::pairing(*t0, pvugc_vk.delta_g2);
            lhs += E::pairing(*t1, pvugc_vk.delta_g2);
        }
        let (c0, c1) = bundle.gs_commitments.theta_delta_cancel;
        lhs += E::pairing(c0, pvugc_vk.delta_g2);
        lhs += E::pairing(c1, pvugc_vk.delta_g2);
        
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
        col_arms: &ColumnArms<E>,
    ) -> PairingOutput<E> {
        crate::decap::decap(commitments, col_arms)
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


