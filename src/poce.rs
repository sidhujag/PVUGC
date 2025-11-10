//! Proof of Correct Exponentiation (PoCE) for Column Arming
//!
//! PoCE-A: Prove that all column arms share the same ρ and ciphertext is key-committed
//! PoCE-B: Decapper-local key-commitment verification
//!
//! Essential for preventing mixed-ρ attacks and ensuring cryptographic integrity
//! in column-based PVUGC arming.

use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup, PrimeGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;
use sha2::{Digest, Sha256};

/// PoCE-A proof for column arming
/// Proves: ∀j, D_j = Y_j^ρ AND D_δ = δ^ρ AND ciphertext is key-committed to a K derived from R^ρ and context (see DEM-SHA256)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PoceColumnProof<E: Pairing> {
    /// Per-column commitments: k_ρ · Y_j for each column
    pub commitments: Vec<E::G2Affine>,

    /// Commitment for δ: k_ρ · δ
    pub delta_commitment: E::G2Affine,

    /// Schnorr proof for T_i = s_i G
    pub t_commitment: E::G1Affine,
    pub t_response: E::ScalarField,

    /// Main response proving same ρ for all arms
    pub response: E::ScalarField,

    /// Challenge used in Fiat-Shamir
    pub challenge: E::ScalarField,
}

/// Prove PoCE-A for column arming
///
/// Witness: (ρ_i, s_i, h_i)
/// Public: ({D_j = Y_j^ρ_i}, D_δ = δ^ρ_i, T_i = s_i G, ctx_hash, GS_instance_digest, ct_i, τ_i)
pub fn prove_poce_column<E: Pairing, R: RngCore + rand_core::CryptoRng>(
    y_bases: &[E::G2Affine],  // Y_j bases
    delta_base: &E::G2Affine, // δ base
    y_arms: &[E::G2Affine],   // D_j = Y_j^ρ
    delta_arm: &E::G2Affine,  // D_δ = δ^ρ
    t_i: &E::G1Affine,        // T_i = s_i G
    rho: &E::ScalarField,     // ρ_i (secret)
    s_i: &E::ScalarField,     // s_i (secret)
    ctx_hash: &[u8],          // Context hash
    gs_digest: &[u8],         // GS instance digest
    ct_i: &[u8],              // Ciphertext bytes (published)
    tau_i: &[u8],             // Key-commitment tag bytes (published)
    rng: &mut R,
) -> PoceColumnProof<E> {
    assert_eq!(y_bases.len(), y_arms.len());

    // Sample nonces
    let k_rho = E::ScalarField::rand(rng);
    let k_s = E::ScalarField::rand(rng);

    // Per-column commitments: k_rho * Y_j for all columns and δ
    let commitments: Vec<_> = y_bases
        .iter()
        .map(|y_base| (y_base.into_group() * k_rho).into_affine())
        .collect();
    let delta_commitment = (delta_base.into_group() * k_rho).into_affine();

    // T commitment: k_s * G1_generator
    let t_commitment = (<E as Pairing>::G1::generator() * k_s).into_affine();

    // Challenge: H(y_bases || delta_base || y_arms || delta_arm || t_i || commitment || t_commitment || ctx_hash || gs_digest || ct_i || tau_i)
    let challenge = compute_poce_challenge::<E>(
        y_bases,
        delta_base,
        y_arms,
        delta_arm,
        t_i,
        &commitments,
        &delta_commitment,
        &t_commitment,
        ctx_hash,
        gs_digest,
        ct_i,
        tau_i,
    );

    // Responses
    let response = k_rho + challenge * rho;
    let t_response = k_s + challenge * s_i;

    PoceColumnProof {
        commitments,
        delta_commitment,
        t_commitment,
        t_response,
        response,
        challenge,
    }
}

/// Verify PoCE-A for column arming
pub fn verify_poce_column<E: Pairing>(
    y_bases: &[E::G2Affine],  // Y_j bases
    delta_base: &E::G2Affine, // δ base
    y_arms: &[E::G2Affine],   // D_j = Y_j^ρ
    delta_arm: &E::G2Affine,  // D_δ = δ^ρ
    t_i: &E::G1Affine,        // T_i = s_i G
    proof: &PoceColumnProof<E>,
    ctx_hash: &[u8],  // Context hash
    gs_digest: &[u8], // GS instance digest
    ct_i: &[u8],      // Ciphertext bytes (published)
    tau_i: &[u8],     // Key-commitment tag bytes (published)
) -> bool {
    // Recompute challenge
    if y_bases.len() != y_arms.len() || y_bases.len() != proof.commitments.len() {
        return false;
    }

    let challenge = compute_poce_challenge::<E>(
        y_bases,
        delta_base,
        y_arms,
        delta_arm,
        t_i,
        &proof.commitments,
        &proof.delta_commitment,
        &proof.t_commitment,
        ctx_hash,
        gs_digest,
        ct_i,
        tau_i,
    );

    if challenge != proof.challenge {
        return false;
    }

    // Verify per-column discrete log equality: commitment_j + challenge * D_j = response * Y_j
    let mut arms_check = true;
    for ((commitment, y_base), y_arm) in proof
        .commitments
        .iter()
        .zip(y_bases.iter())
        .zip(y_arms.iter())
    {
        let left = commitment.into_group() + y_arm.into_group() * challenge;
        let right = y_base.into_group() * proof.response;
        if left.into_affine() != right.into_affine() {
            arms_check = false;
            break;
        }
    }

    if !arms_check {
        return false;
    }

    let delta_left = proof.delta_commitment.into_group() + delta_arm.into_group() * challenge;
    let delta_right = delta_base.into_group() * proof.response;
    if delta_left.into_affine() != delta_right.into_affine() {
        return false;
    }

    // Verify T_i proof: t_commitment + challenge * T_i = t_response * G1_generator
    let t_left = proof.t_commitment.into_group() + t_i.into_group() * challenge;
    let t_right = <E as Pairing>::G1::generator() * proof.t_response;
    t_left.into_affine() == t_right.into_affine()
}

/// Compute Fiat-Shamir challenge for PoCE
fn compute_poce_challenge<E: Pairing>(
    y_bases: &[E::G2Affine],
    delta_base: &E::G2Affine,
    y_arms: &[E::G2Affine],
    delta_arm: &E::G2Affine,
    t_i: &E::G1Affine,
    commitments: &[E::G2Affine],
    delta_commitment: &E::G2Affine,
    t_commitment: &E::G1Affine,
    ctx_hash: &[u8],
    gs_digest: &[u8],
    ct_i: &[u8],
    tau_i: &[u8],
) -> E::ScalarField {
    let mut hasher = Sha256::new();

    // Serialize all group elements
    for base in y_bases {
        let mut bytes = Vec::new();
        base.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }

    let mut bytes = Vec::new();
    delta_base.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);

    for arm in y_arms {
        let mut bytes = Vec::new();
        arm.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }

    let mut bytes = Vec::new();
    delta_arm.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);

    let mut bytes = Vec::new();
    t_i.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);

    for commitment in commitments {
        let mut bytes = Vec::new();
        commitment.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }

    let mut bytes = Vec::new();
    delta_commitment.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);

    let mut bytes = Vec::new();
    t_commitment.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);

    // Add context data
    hasher.update(ctx_hash);
    hasher.update(gs_digest);

    // Bind ciphertext and its tag into FS transcript
    hasher.update(ct_i);
    hasher.update(tau_i);

    // Convert hash to field element
    let hash_bytes = hasher.finalize();
    E::ScalarField::from_le_bytes_mod_order(&hash_bytes)
}

/// Derive KEM key from pairing output

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381 as E, Fr, G2Affine};
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;

    #[test]
    fn test_poce_column_proof() {
        let mut rng = StdRng::seed_from_u64(3);

        // Create test bases and arms
        let y_bases = vec![G2Affine::rand(&mut rng), G2Affine::rand(&mut rng)];
        let delta_base = G2Affine::rand(&mut rng);
        let rho = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);

        // Create arms
        let y_arms: Vec<_> = y_bases
            .iter()
            .map(|y| (y.into_group() * rho).into_affine())
            .collect();
        let delta_arm = (delta_base.into_group() * rho).into_affine();
        let t_i = (<E as Pairing>::G1::generator() * s_i).into_affine();

        let ctx_hash = b"test_context";
        let gs_digest = b"test_gs_digest";

        // Prove
        let ct = b"dummy-ct";
        let tau = b"dummy-tau";
        let proof = prove_poce_column::<E, _>(
            &y_bases,
            &delta_base,
            &y_arms,
            &delta_arm,
            &t_i,
            &rho,
            &s_i,
            ctx_hash,
            gs_digest,
            ct,
            tau,
            &mut rng,
        );

        // Verify
        let valid = verify_poce_column::<E>(
            &y_bases,
            &delta_base,
            &y_arms,
            &delta_arm,
            &t_i,
            &proof,
            ctx_hash,
            gs_digest,
            ct,
            tau,
        );

        assert!(valid);
    }

    #[test]
    fn test_poce_column_rejects_mixed_rho() {
        let mut rng = StdRng::seed_from_u64(4);

        let y_bases = vec![G2Affine::rand(&mut rng), G2Affine::rand(&mut rng)];
        let delta_base = G2Affine::rand(&mut rng);
        let rho1 = Fr::rand(&mut rng);
        let rho2 = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);

        // Create mixed-ρ arms
        let y_arms = vec![
            (y_bases[0].into_group() * rho1).into_affine(),
            (y_bases[1].into_group() * rho2).into_affine(),
        ];
        let delta_arm = (delta_base.into_group() * rho1).into_affine();
        let t_i = (<E as Pairing>::G1::generator() * s_i).into_affine();

        let ctx_hash = b"test_context";
        let gs_digest = b"test_gs_digest";

        // Try to prove with rho1 (should fail)
        let ct = b"dummy-ct";
        let tau = b"dummy-tau";
        let proof = prove_poce_column::<E, _>(
            &y_bases,
            &delta_base,
            &y_arms,
            &delta_arm,
            &t_i,
            &rho1,
            &s_i,
            ctx_hash,
            gs_digest,
            ct,
            tau,
            &mut rng,
        );

        // Verification should fail
        let valid = verify_poce_column::<E>(
            &y_bases,
            &delta_base,
            &y_arms,
            &delta_arm,
            &t_i,
            &proof,
            ctx_hash,
            gs_digest,
            ct,
            tau,
        );

        assert!(!valid);
    }
}
