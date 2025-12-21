//! Integration API for One-Sided GS PVUGC

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::One;
use ark_groth16::{Proof as Groth16Proof, VerifyingKey as Groth16VK};

use crate::adaptor_ve::{prove_adaptor_ve, verify_adaptor_ve, AdaptorVeProof};
use crate::arming::{arm_columns, ColumnArms, ColumnBases};
use crate::ct::{serialize_gt, DemP2};
use crate::error::{Error, Result as PvugcResult};
use crate::poce::{prove_poce_column, verify_poce_column, PoceColumnProof};
use crate::ppe::validate_groth16_vk_subgroups;
pub use crate::ppe::{validate_pvugc_vk_subgroups, PvugcVk};
use crate::{compute_baked_target, OneSidedCommitments};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::ops::Neg;

/// Complete PVUGC bundle
pub struct PvugcBundle<E: Pairing> {
    pub groth16_proof: Groth16Proof<E>,
    pub gs_commitments: OneSidedCommitments<E>,
}

#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ColumnArmingAttestation<E: Pairing> {
    pub poce: PoceColumnProof<E>,
    pub ve: AdaptorVeProof,
}

impl<E: Pairing> ColumnArmingAttestation<E> {
    fn new(poce: PoceColumnProof<E>, ve: AdaptorVeProof) -> Self {
        Self { poce, ve }
    }
}

fn num_instance_variables<E: Pairing>(vk: &Groth16VK<E>) -> usize {
    vk.gamma_abc_g1.len()
}

fn split_statement_only_bases<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> PvugcResult<(E::G2Affine, Vec<E::G2Affine>)> {
    use ark_ec::CurveGroup;

    let total_instance = num_instance_variables(vk);
    if total_instance == 0 {
        return Err(Error::MismatchedSizes);
    }
    let expected_inputs = total_instance.saturating_sub(1);
    if public_inputs.len() != expected_inputs {
        return Err(Error::PublicInputLength {
            expected: expected_inputs,
            actual: public_inputs.len(),
        });
    }

    // Need: b_g2_query[0] + one entry per assignment variable.
    let required_bases = 1 + total_instance;
    if pvugc_vk.b_g2_query.len() < required_bases {
        return Err(Error::MismatchedSizes);
    }

    let mut aggregate = pvugc_vk.beta_g2.into_group();
    aggregate += pvugc_vk.b_g2_query[0].into_group();

    for (idx, public_val) in public_inputs.iter().enumerate() {
        let base = pvugc_vk
            .b_g2_query
            .get(1 + idx)
            .ok_or(Error::MismatchedSizes)?;
        aggregate += base.into_group() * public_val;
    }

    let witness_bases: Vec<E::G2Affine> = pvugc_vk
        .b_g2_query
        .iter()
        .skip(total_instance)
        .cloned()
        .collect();

    Ok((aggregate.into_affine(), witness_bases))
}

/// Defensive audit for *published* statement-only bases used by arming/decap.
///
/// This catches practical footguns that do **not** require solving DLP:
/// - identity bases (degenerate)
/// - duplicates / negated duplicates (publicly known linear relations)
/// - y_col == ±delta (publicly known linear relation with the δ leg)
fn audit_statement_only_bases_for_publication<E: Pairing>(bases: &ColumnBases<E>) -> PvugcResult<()> {
    // Always require subgroup validity and non-zero delta.
    bases.validate_subgroups()?;

    if bases.y_cols.is_empty() {
        return Err(Error::MismatchedSizes);
    }
    // NOTE: It is common for Groth16 `b_g2_query` to contain identity points for columns that
    // never appear in the B-polynomials. These witness columns are safe to publish as identities
    // (they arm to identity and contribute nothing).
    //
    // However, the *public aggregated leg* (index 0) being identity is a much stronger and
    // unexpected degeneracy for statement binding, so we fail-closed on that case.
    if bases.y_cols[0].is_zero() {
        return Err(Error::Crypto("zero_public_y_col".to_string()));
    }

    let delta = bases.delta;
    if delta.is_zero() {
        return Err(Error::ZeroDelta);
    }
    let delta_neg = delta.into_group().neg().into_affine();

    let hash_g2 = |g: &E::G2Affine| -> [u8; 32] {
        let mut buf = Vec::new();
        g.serialize_compressed(&mut buf).expect("serialize");
        Sha256::digest(&buf).into()
    };

    let delta_h = hash_g2(&delta);
    let delta_neg_h = hash_g2(&delta_neg);

    let mut seen: HashSet<[u8; 32]> = HashSet::new();
    let mut seen_neg: HashSet<[u8; 32]> = HashSet::new();

    for (idx, y) in bases.y_cols.iter().enumerate() {
        // Skip identity witness columns (idx >= 1). Multiple zeros are fine and expected.
        if idx != 0 && y.is_zero() {
            continue;
        }

        let h = hash_g2(y);
        if h == delta_h || h == delta_neg_h {
            return Err(Error::Crypto(format!("y_col_eq_pm_delta_at_index_{}", idx)));
        }
        if !seen.insert(h) {
            return Err(Error::Crypto(format!("duplicate_y_col_at_index_{}", idx)));
        }
        // Also ban y_i == -y_j (publicly known relation).
        let y_neg = y.into_group().neg().into_affine();
        let h_neg = hash_g2(&y_neg);
        if seen_neg.contains(&h) {
            return Err(Error::Crypto(format!("negated_duplicate_y_col_at_index_{}", idx)));
        }
        seen_neg.insert(h_neg);
    }

    Ok(())
}

/// Optional verification limits
pub struct VerifyLimits {
    /// Maximum allowed number of B-columns (length of b_g2_query)
    pub max_b_columns: Option<usize>,
    /// Maximum allowed number of theta rows (δ-side rows)
    pub max_theta_rows: Option<usize>,
    /// Maximum allowed total pairing budget for PPE verify
    /// total_pairings = 2*|X_B| + 2*|theta| + 2 (for canceller limbs)
    pub max_total_pairings: Option<usize>,
}

/// Recommended default for total pairing budget per verification (spec §6 size bound)
pub const DEFAULT_MAX_TOTAL_PAIRINGS: usize = 96;
/// Recommended default maximum for B-columns (statement-only Y columns)
pub const DEFAULT_MAX_B_COLUMNS: usize = 24;
/// Recommended default maximum for theta rows (δ-side rows)
pub const DEFAULT_MAX_THETA_ROWS: usize = 22;

/// Main API for one-sided PVUGC
///
/// SECURITY WARNING: To prevent "Full Span" mix-and-match attacks, this scheme MUST
/// be used with a "Lean CRS" that does not contain raw Powers of Tau.
pub struct OneSidedPvugc;

impl OneSidedPvugc {
    /// Construct statement-only column bases with aggregated public leg.
    pub fn build_column_bases<E: Pairing>(
        pvugc_vk: &PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
    ) -> PvugcResult<ColumnBases<E>> {
        let (public_leg, witness_cols) = split_statement_only_bases(pvugc_vk, vk, public_inputs)?;
        let mut y_cols = Vec::with_capacity(1 + witness_cols.len());
        y_cols.push(public_leg);
        y_cols.extend(witness_cols);
        Ok(ColumnBases {
            y_cols,
            delta: pvugc_vk.delta_g2,
        })
    }

    /// Canonical setup and arming (formerly setup_and_arm_columns)
    /// Returns: (ColumnBases, ColumnArms, R_baked, K=R_baked^ρ)
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

        // Use BAKED target computation
        let r_baked = compute_baked_target(vk, pvugc_vk, public_inputs)?;

        // Early guard: R must not be identity (spec §6/§7)
        if crate::ct::gt_eq_ct::<E>(&r_baked, &PairingOutput::<E>(One::one())) {
            return Err(Error::Crypto("R_is_identity".to_string()));
        }
        let bases = Self::build_column_bases(pvugc_vk, vk, public_inputs)?;
        // Strict publication audit: prevent trivial linear relations / degeneracy.
        audit_statement_only_bases_for_publication(&bases)?;
        let col_arms = arm_columns(&bases, rho)?;
        let k = Self::compute_r_to_rho(&r_baked, rho);
        Ok((bases, col_arms, r_baked, k))
    }

    /// Produce PoCE-A attestation for column arming (arm-time)
    ///
    /// Proves that all column arms share the same ρ and ciphertext is key-committed
    /// to K derived from R^ρ via Poseidon-based DEM binding ctx_hash and GS digest
    pub fn attest_column_arming<E: Pairing, R: RngCore + rand_core::CryptoRng>(
        bases: &ColumnBases<E>,
        col_arms: &ColumnArms<E>,
        t_i: &E::G1Affine,               // T_i = s_i G
        rho: &E::ScalarField,            // ρ_i (secret)
        s_i: &E::ScalarField,            // s_i (secret)
        expected_key: &PairingOutput<E>, // R^ρ derived during setup
        ad_core: &[u8],                  // Serialized AD_core (for digest)
        ctx_hash: &[u8],                 // Context hash
        gs_digest: &[u8],                // GS instance digest
        ct_i: &[u8],                     // Ciphertext bytes (published)
        tau_i: &[u8],                    // Key-commitment tag bytes (published)
        rng: &mut R,
        skip_ve: bool, // Skip expensive VE circuit for isolated testing
    ) -> PvugcResult<ColumnArmingAttestation<E>> {
        let poce = prove_poce_column::<E, R>(
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
        );

        let ve = if skip_ve {
            // For security tests: skip expensive VE circuit, use dummy proof
            AdaptorVeProof::dummy()
        } else {
            // For E2E tests: run full VE circuit
            let key_bytes = serialize_gt::<E>(&expected_key.0);
            let dem = DemP2::new(&key_bytes, ad_core);
            let plaintext = dem.decrypt(ct_i);
            prove_adaptor_ve(&key_bytes, ad_core, ct_i, tau_i, &plaintext)?
        };

        Ok(ColumnArmingAttestation::new(poce, ve))
    }

    /// Verify PoCE-A attestation for column arming (arm-time)
    pub fn verify_column_arming<E: Pairing>(
        bases: &ColumnBases<E>,
        col_arms: &ColumnArms<E>,
        t_i: &E::G1Affine, // T_i = s_i G
        attestation: &ColumnArmingAttestation<E>,
        ad_core: &[u8],
        ctx_hash: &[u8],  // Context hash
        gs_digest: &[u8], // GS instance digest
        ct_i: &[u8],      // Ciphertext bytes (published)
        tau_i: &[u8],     // Key-commitment tag bytes (published)
        skip_ve: bool,    // Skip VE verification for isolated testing
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

        let poce_ok = verify_poce_column::<E>(
            &bases.y_cols,
            &bases.delta,
            &col_arms.y_cols_rho,
            &col_arms.delta_rho,
            t_i,
            &attestation.poce,
            ctx_hash,
            gs_digest,
            ct_i,
            tau_i,
        );
        if !poce_ok {
            return false;
        }

        if skip_ve {
            // For security tests: skip VE verification
            true
        } else {
            // For E2E tests: full VE verification
            verify_adaptor_ve(&attestation.ve, ad_core, ct_i, tau_i)
        }
    }

    /// Verify DEM tag (decap-time, decapper-local)
    ///
    /// Verifies that ciphertext tag matches derived key using DEM-Poseidon
    pub fn verify_key_commitment<E: Pairing>(
        derived_m: &PairingOutput<E>, // R^ρ derived from attestation
        ctx_hash: &[u8],              // Context hash
        gs_digest: &[u8],             // GS instance digest
        ct_i: &[u8],                  // Ciphertext
        tau_i: &[u8],                 // Key-commitment tag
    ) -> bool {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        // Combine ctx_hash and gs_digest to form AD_core for DEM-Poseidon
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

    /// Compute DEM tag for a ciphertext (deposit-time helper)
    ///
    /// τ = Poseidon("PVUGC/DEM/tag" || K || ad_digest || ct), where K is derived from R^ρ
    pub fn compute_key_commitment_tag_for_ciphertext<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ctx_hash: &[u8],
        gs_digest: &[u8],
        ciphertext: &[u8],
    ) -> Vec<u8> {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        // Combine ctx_hash and gs_digest to form AD_core for DEM-Poseidon
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
                max_b_columns: Some(DEFAULT_MAX_B_COLUMNS),
                max_theta_rows: Some(DEFAULT_MAX_THETA_ROWS),
                // Enforce safe default pairing budget to mitigate DoS by oversized attestations
                max_total_pairings: Some(DEFAULT_MAX_TOTAL_PAIRINGS),
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

        let (public_b_leg, witness_bases) =
            match split_statement_only_bases(pvugc_vk, vk, public_inputs) {
                Ok(split) => split,
                Err(_) => return false,
            };

        // 2. Subgroup/identity checks on commitments (allow zero limbs, enforce subgroup when non-zero)
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

        // 3. Verify PPE equals R_baked(vk,x) using direct column pairing
        // Use BAKED target computation
        let r_baked = match compute_baked_target(vk, pvugc_vk, public_inputs) {
            Ok(r) => r,
            Err(_) => return false,
        };

        // Guard: R must not be identity
        if crate::ct::gt_eq_ct::<E>(&r_baked, &PairingOutput::<E>(One::one())) {
            return false;
        }

        // Columns: [B_pub(vk,x), witness-only Y_j] (δ supplied via Θ = C + sA)
        let mut y_cols = Vec::with_capacity(1 + witness_bases.len());
        y_cols.push(public_b_leg);
        y_cols.extend_from_slice(&witness_bases);
        if bundle.gs_commitments.x_b_cols.len() != y_cols.len() {
            return false;
        }
        if bundle.gs_commitments.theta.is_empty() {
            return false;
        }

        // Optional DoS limits: enforce theta rows and total pairing budget
        if let Some(max_theta) = limits.max_theta_rows {
            if bundle.gs_commitments.theta.len() > max_theta {
                return false;
            }
        }
        if let Some(max_pairings) = limits.max_total_pairings {
            // total_pairings = 2*|X_B| + 2*|theta| + 2 (for canceller limbs)
            let num_cols = y_cols.len();
            let num_theta = bundle.gs_commitments.theta.len();
            let total_pairings = 2usize
                .saturating_mul(num_cols)
                .saturating_add(2usize.saturating_mul(num_theta))
                .saturating_add(2);
            if total_pairings > max_pairings {
                return false;
            }
        }

        // Structural exclusion: γ₂ must not appear among statement-only bases
        // (y_cols = {β₂} ∪ b_g2_query). Reject if any Y equals vk.gamma_g2.
        for y in &y_cols {
            if *y == vk.gamma_g2 {
                return false;
            }
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

        // Check: LHS == R_baked (constant-time compare)
        if !crate::ct::gt_eq_ct::<E>(&lhs, &r_baked) {
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

    /// Encrypt using derived key K (PairingOutput) with DEM-Poseidon.
    /// Per spec §8: keystream = Poseidon("PVUGC/DEM/keystream" || K_i || ad_digest || counter_le)
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

    /// Decrypt using derived key K (PairingOutput) with DEM-Poseidon
    /// Per spec §8: pt = ct ⊕ Poseidon("PVUGC/DEM/keystream" || K_i || ad_digest || counter_le)
    pub fn decrypt_with_key_dem<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ad_core: &[u8],
        ciphertext: &[u8],
    ) -> core::result::Result<Vec<u8>, String> {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        let dem = crate::ct::DemP2::new(&k_bytes, ad_core);
        Ok(dem.decrypt(ciphertext))
    }

    /// Compute key-commitment tag τ_i per spec §8:286 (DEM-Poseidon)
    pub fn compute_key_commitment_tag_dem<E: Pairing>(
        derived_m: &PairingOutput<E>,
        ad_core: &[u8],
        ciphertext: &[u8],
    ) -> [u8; 32] {
        let k_bytes = crate::ct::serialize_gt::<E>(&derived_m.0);
        crate::ct::compute_key_commitment_tag(&k_bytes, ad_core, ciphertext)
    }

    /// Verify DEM tag (key-commitment check)
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

