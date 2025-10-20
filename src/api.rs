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
use crate::ppe::{validate_gamma_structure, derive_gamma_rademacher};
use crate::ppe::validate_groth16_vk_subgroups;
use crate::poce::{PoceAcrossProof, prove_poce_across, verify_poce_across};
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

    /// Produce PoCE-A attestation over all armed rows (deposit-time helper)
    pub fn attest_arming<E: Pairing, R: RngCore>(
        rows: &RowBases<E>,
        arms: &Arms<E>,
        rho: &E::ScalarField,
        rng: &mut R,
    ) -> PoceAcrossProof<E> {
        // Concatenate U and W sides
        let mut all_bases = rows.u_rows.clone();
        all_bases.extend(rows.w_rows.clone());
        let mut all_arms = arms.u_rows_rho.clone();
        all_arms.extend(arms.w_rows_rho.clone());
        prove_poce_across::<E, R>(&all_bases, &all_arms, rho, rng)
    }

    /// Verify PoCE-A attestation for an arming record
    pub fn verify_arming<E: Pairing>(
        rows: &RowBases<E>,
        arms: &Arms<E>,
        proof: &PoceAcrossProof<E>,
    ) -> bool {
        let mut all_bases = rows.u_rows.clone();
        all_bases.extend(rows.w_rows.clone());
        let mut all_arms = arms.u_rows_rho.clone();
        all_arms.extend(arms.w_rows_rho.clone());
        verify_poce_across::<E>(&all_bases, &all_arms, proof)
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
        // Gamma structure sanity (at least one non-zero per row; rectangular shape)
        if gamma.is_empty() || gamma[0].is_empty() {
            return false;
        }
        // min_nonzero_per_row = 1; columns coverage not enforced in prototype; no rank test here
        if !validate_gamma_structure::<E>(gamma, 1, false, false) {
            return false;
        }
        // Canonicalize Γ: derive deterministically from vk/pvugc_vk and insist on equality
        let canonical_gamma = derive_gamma_rademacher::<E>(pvugc_vk, vk, gamma.len());
        if *gamma != canonical_gamma {
            return false;
        }
        // Reject duplicate rows in Γ to avoid degenerate ties
        for i in 0..gamma.len() {
            for j in (i+1)..gamma.len() {
                if gamma[i] == gamma[j] { return false; }
            }
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
        // Length checks to avoid silent truncation in zips
        if bundle.gs_commitments.c_rows.len() != rows.u_rows.len() {
            return false;
        }
        // δ-side is single-row in current build path; allow any theta length ≥ 1
        if bundle.gs_commitments.theta.is_empty() {
            return false;
        }
        
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

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G2Affine};
    use ark_std::{UniformRand, rand::{SeedableRng, rngs::StdRng}};
    use ark_ec::CurveGroup;

    type E = Bls12_381;

    #[test]
    fn test_api_poce_arming_accepts_valid() {
        let mut rng = StdRng::seed_from_u64(123);

        // Simple Y bases and +δ
        let y_bases: Vec<G2Affine> = vec![G2Affine::rand(&mut rng), G2Affine::rand(&mut rng)];
        let delta: G2Affine = G2Affine::rand(&mut rng);

        // Identity 2x2 Γ
        let gamma = vec![
            vec![Fr::from(1u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(1u64)],
        ];

        // Build statement-only rows and arm them with ρ
        let rows: RowBases<E> = build_row_bases_from_vk(&y_bases, delta, gamma);
        let rho = Fr::rand(&mut rng);
        let arms: Arms<E> = arm_rows(&rows, &rho);

        // PoCE-A attest + verify via API helpers
        let proof = OneSidedPvugc::attest_arming(&rows, &arms, &rho, &mut rng);
        assert!(OneSidedPvugc::verify_arming(&rows, &arms, &proof));
    }

    #[test]
    fn test_api_poce_arming_rejects_mixed_rho() {
        let mut rng = StdRng::seed_from_u64(321);

        let y_bases: Vec<G2Affine> = vec![G2Affine::rand(&mut rng), G2Affine::rand(&mut rng)];
        let delta: G2Affine = G2Affine::rand(&mut rng);
        let gamma = vec![
            vec![Fr::from(1u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(1u64)],
        ];

        let rows: RowBases<E> = build_row_bases_from_vk(&y_bases, delta, gamma);
        let rho = Fr::rand(&mut rng);
        let arms_good: Arms<E> = arm_rows(&rows, &rho);

        // Create a bad arms set with one row armed using a different ρ₂
        let rho2 = Fr::rand(&mut rng);
        let mut arms_bad = arms_good.clone();
        let bad_u0 = (rows.u_rows[0].into_group() * rho2).into_affine();
        arms_bad.u_rows_rho[0] = bad_u0;

        // Attempt to attest with rho over inconsistent arms → verifier must reject
        let proof_bad = OneSidedPvugc::attest_arming(&rows, &arms_bad, &rho, &mut rng);
        assert!(!OneSidedPvugc::verify_arming(&rows, &arms_bad, &proof_bad));
    }
}

