//! Integration API for One-Sided GS PVUGC

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::One;
use ark_groth16::{Proof as Groth16Proof, VerifyingKey as Groth16VK};

use crate::arming::{arm_columns, ColumnArms, ColumnBases};
use crate::dlrep::{verify_b_msm, verify_ties_per_column};
use crate::error::{Error, Result as PvugcResult};
use crate::poce::{prove_poce_column, verify_poce_column, PoceColumnProof};
use crate::ppe::validate_groth16_vk_subgroups;
pub use crate::ppe::{validate_pvugc_vk_subgroups, PvugcVk};
use crate::{compute_groth16_target, DlrepBProof, DlrepPerColumnTies, OneSidedCommitments};
use ark_std::rand::RngCore;

/// Complete PVUGC bundle
pub struct PvugcBundle<E: Pairing> {
    pub groth16_proof: Groth16Proof<E>,
    pub dlrep_b: DlrepBProof<E>,
    pub dlrep_ties: DlrepPerColumnTies<E>,
    pub gs_commitments: OneSidedCommitments<E>,
}

/// Optional verification limits
pub struct VerifyLimits {
    /// Maximum allowed number of B-columns (length of b_g2_query)
    pub max_b_columns: Option<usize>,
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
    ) -> PvugcResult<(
        ColumnBases<E>,
        ColumnArms<E>,
        PairingOutput<E>,
        PairingOutput<E>,
    )> {
        if !validate_pvugc_vk_subgroups(pvugc_vk) {
            return Err(Error::InvalidSubgroup);
        }
        if !validate_groth16_vk_subgroups(vk) {
            return Err(Error::InvalidSubgroup);
        }

        let r = compute_groth16_target(vk, public_inputs)?;
        let mut y_cols = vec![pvugc_vk.beta_g2];
        y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
        let bases = ColumnBases {
            y_cols,
            delta: pvugc_vk.delta_g2,
        };
        let col_arms = arm_columns(&bases, rho)?;
        let k = Self::compute_r_to_rho(&r, rho);
        Ok((bases, col_arms, r, k))
    }

    /// Produce PoCE-A attestation for column arming (arm-time)
    ///
    /// Proves that all column arms share the same ρ and ciphertext is key-committed
    /// to K derived from R^ρ via DEM-SHA256 KDF binding ctx_hash and GS digest
    pub fn attest_column_arming<E: Pairing, R: RngCore + rand_core::CryptoRng>(
        bases: &ColumnBases<E>,
        col_arms: &ColumnArms<E>,
        t_i: &E::G1Affine,    // T_i = s_i G
        rho: &E::ScalarField, // ρ_i (secret)
        s_i: &E::ScalarField, // s_i (secret)
        ctx_hash: &[u8],      // Context hash
        gs_digest: &[u8],     // GS instance digest
        ct_i: &[u8],          // Ciphertext bytes (published)
        tau_i: &[u8],         // Key-commitment tag bytes (published)
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
            ct_i,
            tau_i,
            rng,
        )
    }

    /// Verify PoCE-A attestation for column arming (arm-time)
    pub fn verify_column_arming<E: Pairing>(
        bases: &ColumnBases<E>,
        col_arms: &ColumnArms<E>,
        t_i: &E::G1Affine, // T_i = s_i G
        proof: &PoceColumnProof<E>,
        ctx_hash: &[u8],  // Context hash
        gs_digest: &[u8], // GS instance digest
        ct_i: &[u8],      // Ciphertext bytes (published)
        tau_i: &[u8],     // Key-commitment tag bytes (published)
    ) -> bool {
        // Length guard before zipping (prevents silent truncation if caller messes up)
        if bases.y_cols.len() != col_arms.y_cols_rho.len() {
            return false;
        }

        // Subgroup and identity checks for arms
        // For Y-columns: if base is identity, arm MUST be identity; otherwise, arm must be non-identity and in subgroup
        // For δ arm: MUST be non-identity and in subgroup
        {
            use ark_ec::PrimeGroup;
            use ark_ff::PrimeField;
            let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
            let is_good_g2 = |g: &E::G2Affine| {
                if g.is_zero() {
                    return false;
                }
                (g.into_group().mul_bigint(order)).into_affine().is_zero()
            };
            for (y_base, d_arm) in bases.y_cols.iter().zip(col_arms.y_cols_rho.iter()) {
                if y_base.is_zero() {
                    if !d_arm.is_zero() {
                        return false;
                    }
                } else {
                    if !is_good_g2(d_arm) {
                        return false;
                    }
                }
            }
            if col_arms.delta_rho.is_zero() {
                return false;
            }
            if !is_good_g2(&col_arms.delta_rho) {
                return false;
            }
        }

        verify_poce_column::<E>(
            &bases.y_cols,
            &bases.delta,
            &col_arms.y_cols_rho,
            &col_arms.delta_rho,
            t_i,
            proof,
            ctx_hash,
            gs_digest,
            ct_i,
            tau_i,
        )
    }

    /// Verify PoCE-B key-commitment (decap-time, decapper-local)
    ///
    /// Verifies that ciphertext is key-committed to the derived key using DEM-SHA256
    pub fn verify_key_commitment<E: Pairing>(
        derived_m: &PairingOutput<E>, // R^ρ derived from attestation
        ctx_hash: &[u8],              // Context hash
        gs_digest: &[u8],             // GS instance digest
        ct_i: &[u8],                  // Ciphertext
        tau_i: &[u8],                 // Key-commitment tag
    ) -> bool {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        // Combine ctx_hash and gs_digest to form AD_core for DEM-SHA256
        let mut ad_core = Vec::new();
        ad_core.extend_from_slice(ctx_hash);
        ad_core.extend_from_slice(gs_digest);
        
        // Ensure tau_i is 32 bytes
        if tau_i.len() != 32 {
            return false;
        }
        let mut tau_array = [0u8; 32];
        tau_array.copy_from_slice(tau_i);
        
        crate::ct::verify_key_commitment(&k_bytes, &ad_core, ct_i, &tau_array)
    }

    /// Compute PoCE-B key-commitment tag for a ciphertext (deposit-time helper)
    ///
    /// τ = SHA-256("PVUGC/DEM-SHA256/tag" || K || AD_core || ct), where K is derived from R^ρ
    pub fn compute_key_commitment_tag_for_ciphertext<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ctx_hash: &[u8],
        gs_digest: &[u8],
        ciphertext: &[u8],
    ) -> Vec<u8> {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        // Combine ctx_hash and gs_digest to form AD_core for DEM-SHA256
        let mut ad_core = Vec::new();
        ad_core.extend_from_slice(ctx_hash);
        ad_core.extend_from_slice(gs_digest);
        
        let tau = crate::ct::compute_key_commitment_tag(&k_bytes, &ad_core, ciphertext);
        tau.to_vec()
    }

    /// Verify complete bundle
    pub fn verify<E: Pairing>(
        bundle: &PvugcBundle<E>,
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
    ) -> bool {
        Self::verify_with_limits(
            bundle,
            pvugc_vk,
            vk,
            public_inputs,
            &VerifyLimits {
                max_b_columns: None,
            },
        )
    }

    /// Verify with optional limits (e.g., N_max to mitigate DoS)
    pub fn verify_with_limits<E: Pairing>(
        bundle: &PvugcBundle<E>,
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
        limits: &VerifyLimits,
    ) -> bool {
        // 0. Basic guards
        if !validate_pvugc_vk_subgroups(pvugc_vk) {
            return false;
        }
        if !validate_groth16_vk_subgroups(vk) {
            return false;
        }
        if let Some(n_max) = limits.max_b_columns {
            if pvugc_vk.b_g2_query.len() > n_max {
                return false;
            }
        }

        // 1. Verify Groth16 proof (standard)
        use ark_groth16::Groth16;
        use ark_snark::SNARK;

        let groth16_valid =
            Groth16::<E>::verify(vk, public_inputs, &bundle.groth16_proof).unwrap_or(false);

        if !groth16_valid {
            return false;
        }

        // 2. Verify DLREP_B against B' = B - β₂ - Y_0, variables are b_g2_query[1..]
        let b_query: &[E::G2Affine] = &pvugc_vk.b_g2_query;
        let (first_b_col, variable_b_cols) = match b_query.split_first() {
            Some(split) => split,
            None => return false,
        };

        let b_prime = (bundle.groth16_proof.b.into_group()
            - pvugc_vk.beta_g2.into_group()
            - first_b_col.into_group())
        .into_affine();

        // Verify over b_g2_query[1..] only (variable part)
        let dlrep_b_ok = verify_b_msm::<E>(
            b_prime,
            variable_b_cols,
            pvugc_vk.delta_g2,
            &bundle.dlrep_b,
        );
        if !dlrep_b_ok {
            return false;
        }

        // 3. Verify per-column same-scalar ties over G1 for variable columns only
        let a = bundle.groth16_proof.a;
        // x_cols for variable B-columns align with b_g2_query[1..] → start from index 2
        let mut x_cols: Vec<E::G1Affine> =
            Vec::with_capacity(bundle.gs_commitments.x_b_cols.len().saturating_sub(2));
        for (i, (x0, _)) in bundle.gs_commitments.x_b_cols.iter().enumerate() {
            if i >= 2 {
                x_cols.push(*x0);
            }
        }
        let ties_ok =
            verify_ties_per_column::<E>(a, &x_cols, &bundle.dlrep_ties, bundle.dlrep_b.commitment);
        if !ties_ok {
            return false;
        }

        // 4. Subgroup/identity checks on commitments (allow zero limbs, enforce subgroup when non-zero)
        {
            use ark_ec::PrimeGroup;
            use ark_ff::PrimeField;
            let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
            let is_good_g1 = |g: &E::G1Affine| {
                if g.is_zero() {
                    return true;
                }
                (g.into_group().mul_bigint(order)).into_affine().is_zero()
            };
            for (x0, x1) in &bundle.gs_commitments.x_b_cols {
                if !is_good_g1(x0) || !is_good_g1(x1) {
                    return false;
                }
            }
            for (t0, t1) in &bundle.gs_commitments.theta {
                if !is_good_g1(t0) || !is_good_g1(t1) {
                    return false;
                }
            }
            let (c0, c1) = bundle.gs_commitments.theta_delta_cancel;
            if !is_good_g1(&c0) || !is_good_g1(&c1) {
                return false;
            }
        }

        // 5. Verify PPE equals R(vk,x) using direct column pairing
        let r_target = match compute_groth16_target(vk, public_inputs) {
            Ok(r) => r,
            Err(_) => return false,
        };
        // Guard: R must not be identity
        if crate::ct::gt_eq_ct::<E>(&r_target, &PairingOutput::<E>(One::one())) {
            return false;
        }

        // Columns: [β₂, b_g2_query[0], b_g2_query[1..]] (δ supplied via Θ = C + sA)
        let mut y_cols = vec![pvugc_vk.beta_g2];
        y_cols.push(*first_b_col);
        y_cols.extend_from_slice(variable_b_cols);
        if bundle.gs_commitments.x_b_cols.len() != y_cols.len() {
            return false;
        }
        if bundle.gs_commitments.theta.is_empty() {
            return false;
        }

        let mut lhs = PairingOutput::<E>(One::one());
        // Fixed-shape pairing schedule derived from pinned column counts
        let num_cols = y_cols.len();
        for i in 0..num_cols {
            let (x0, x1) = bundle.gs_commitments.x_b_cols[i];
            let y = y_cols[i];
            lhs += E::pairing(x0, y);
            lhs += E::pairing(x1, y);
        }
        let num_theta = bundle.gs_commitments.theta.len();
        for i in 0..num_theta {
            let (t0, t1) = bundle.gs_commitments.theta[i];
            lhs += E::pairing(t0, pvugc_vk.delta_g2);
            lhs += E::pairing(t1, pvugc_vk.delta_g2);
        }
        let (c0, c1) = bundle.gs_commitments.theta_delta_cancel;
        lhs += E::pairing(c0, pvugc_vk.delta_g2);
        lhs += E::pairing(c1, pvugc_vk.delta_g2);

        // Guard: LHS should not be identity (constant-time compare)
        if crate::ct::gt_eq_ct::<E>(&lhs, &PairingOutput::<E>(One::one())) {
            return false;
        }

        // Check: LHS == R (constant-time compare)
        if !crate::ct::gt_eq_ct::<E>(&lhs, &r_target) {
            return false;
        }

        true
    }

    /// Decapsulate to get K = R^ρ
    pub fn decapsulate<E: Pairing>(
        commitments: &OneSidedCommitments<E>,
        col_arms: &ColumnArms<E>,
    ) -> PvugcResult<PairingOutput<E>> {
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

    /// Encrypt using derived key K (PairingOutput) with DEM-SHA256
    /// Per spec §8: ct_i = (s_i || h_i) ⊕ SHA-256("PVUGC/DEM-SHA256/keystream" || K_i || AD_core)
    ///
    /// Returns: (ciphertext) encrypted plaintext
    pub fn encrypt_with_key_dem<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ad_core: &[u8],
        plaintext: &[u8],
    ) -> core::result::Result<Vec<u8>, String> {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        let dem = crate::ct::DemP2::new(&k_bytes, ad_core);
        Ok(dem.encrypt(plaintext))
    }

    /// Decrypt using derived key K (PairingOutput) with DEM-SHA256
    /// Per spec §8: pt = ct ⊕ SHA-256("PVUGC/DEM-SHA256/keystream" || K_i || AD_core)
    pub fn decrypt_with_key_dem<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ad_core: &[u8],
        ciphertext: &[u8],
    ) -> core::result::Result<Vec<u8>, String> {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        let dem = crate::ct::DemP2::new(&k_bytes, ad_core);
        Ok(dem.decrypt(ciphertext))
    }

    /// Compute key-commitment tag τ_i per spec §8:286 (DEM-SHA256)
    pub fn compute_key_commitment_tag_dem<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ad_core: &[u8],
        ciphertext: &[u8],
    ) -> [u8; 32] {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        crate::ct::compute_key_commitment_tag(&k_bytes, ad_core, ciphertext)
    }

    /// Verify key-commitment tag (PoCE-B check)
    pub fn verify_key_commitment_dem<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ad_core: &[u8],
        ciphertext: &[u8],
        tau_i: &[u8; 32],
    ) -> bool {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        crate::ct::verify_key_commitment(&k_bytes, ad_core, ciphertext, tau_i)
    }
}
