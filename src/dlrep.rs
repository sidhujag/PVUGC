//! Discrete Log Representation (DLREP) Proofs
//!
//! Schnorr-style proofs for:
//! 1. B = Σ b_j·Y_j (multi-base DLREP in G₂)
//! 2. X^(B)_j = A^b_j (same-scalar ties across groups)

use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{PrimeField, UniformRand};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::RngCore;
use sha2::{Digest, Sha256};

/// Per-column same-scalar ties: for each j, prove X_j = b_j · A
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DlrepPerColumnTies<E: Pairing> {
    /// Commitments T_j = k_j · A for each column j ≥ 2 (variable B-columns)
    pub commitments_g1: Vec<E::G1Affine>,

    /// Responses z_j = k_j + c_j · b_j for each column
    pub responses: Vec<E::ScalarField>,
}

/// Proof that B = Σ b_j·Y_j (aggregated multi-base Schnorr)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DlrepBProof<E: Pairing> {
    /// Commitment: T = Σ k_j·Y_j
    pub commitment: E::G2Affine,

    /// Responses: z_j = k_j + c·b_j
    pub responses: Vec<E::ScalarField>,
}

/// Prove B = Σ b_j·Y_j (multi-base DLREP)
pub fn prove_b_msm<E: Pairing, R: RngCore + rand_core::CryptoRng>(
    b_prime: E::G2Affine,        // B - β - Y_0 (public target)
    y_bases: &[E::G2Affine],     // Y_1, ..., Y_N
    delta_g2: E::G2Affine,       // δ for s term
    b_coeffs: &[E::ScalarField], // b_1, ..., b_N (secret)
    s: E::ScalarField,           // Secret randomness
    rng: &mut R,
) -> DlrepBProof<E> {
    let n = b_coeffs.len();

    // Sample nonces
    let mut nonces = Vec::with_capacity(n + 1);
    for _ in 0..=n {
        nonces.push(E::ScalarField::rand(rng));
    }

    // Commitment: T = k_s·δ + Σ k_j·Y_j
    let mut commitment = delta_g2.into_group() * nonces[0];
    for (k_j, y_j) in nonces[1..].iter().zip(y_bases) {
        commitment += y_j.into_group() * k_j;
    }
    let commitment = commitment.into_affine();

    // Challenge: c = H(context || bases || target || commitment)
    let challenge = compute_dlrep_challenge::<E>(&y_bases, &delta_g2, &b_prime, &commitment);

    // Responses: z_s = k_s + c·s, z_j = k_j + c·b_j
    let mut responses = Vec::with_capacity(n + 1);
    responses.push(nonces[0] + challenge * s);
    for (k_j, b_j) in nonces[1..].iter().zip(b_coeffs) {
        responses.push(*k_j + challenge * b_j);
    }

    DlrepBProof {
        commitment,
        responses,
    }
}

/// Verify B = Σ b_j·Y_j
pub fn verify_b_msm<E: Pairing>(
    b_prime: E::G2Affine,
    y_bases: &[E::G2Affine],
    delta_g2: E::G2Affine,
    proof: &DlrepBProof<E>,
) -> bool {
    // Basic length check: expect one response for s plus one per y_base
    if proof.responses.len() != y_bases.len() + 1 {
        return false;
    }
    // Recompute challenge
    let challenge = compute_dlrep_challenge::<E>(&y_bases, &delta_g2, &b_prime, &proof.commitment);

    // Verify: Σ z_j·Y_j = T + c·B'
    let mut lhs = delta_g2.into_group() * proof.responses[0];
    for (z_j, y_j) in proof.responses[1..].iter().zip(y_bases) {
        lhs += y_j.into_group() * z_j;
    }

    let rhs: E::G2 = proof.commitment.into_group() + b_prime.into_group() * challenge;

    lhs.into_affine() == rhs.into_affine()
}

/// Prove per-column same-scalar ties: ∀j, X_j = b_j · A
///
/// Inputs:
/// - a: base in G1 (A)
/// - x_cols: first limbs X_j in G1 for variable columns (aligned with b_coeffs)
/// - b_coeffs: coefficients b_j used in B decomposition (secret)
pub fn prove_ties_per_column<E: Pairing, R: RngCore + rand_core::CryptoRng>(
    a: E::G1Affine,
    x_cols: &[E::G1Affine],
    b_coeffs: &[E::ScalarField],
    b_commitment: E::G2Affine,
    rng: &mut R,
) -> DlrepPerColumnTies<E> {
    assert_eq!(x_cols.len(), b_coeffs.len());

    let mut commitments_g1 = Vec::with_capacity(b_coeffs.len());
    let mut responses = Vec::with_capacity(b_coeffs.len());

    for (x_j, b_j) in x_cols.iter().zip(b_coeffs.iter()) {
        let k_j = E::ScalarField::rand(rng);
        let t_j = (a.into_group() * k_j).into_affine();
        let c_j = compute_tie_col_challenge::<E>(&a, x_j, &t_j, &b_commitment);
        let z_j = k_j + c_j * b_j;
        commitments_g1.push(t_j);
        responses.push(z_j);
    }

    DlrepPerColumnTies {
        commitments_g1,
        responses,
    }
}

/// Verify per-column same-scalar ties
pub fn verify_ties_per_column<E: Pairing>(
    a: E::G1Affine,
    x_cols: &[E::G1Affine],
    proof: &DlrepPerColumnTies<E>,
    b_commitment: E::G2Affine,
) -> bool {
    if x_cols.len() != proof.commitments_g1.len() || x_cols.len() != proof.responses.len() {
        return false;
    }

    for i in 0..x_cols.len() {
        let x_j = x_cols[i];
        let t_j = proof.commitments_g1[i];
        let z_j = proof.responses[i];
        let c_j = compute_tie_col_challenge::<E>(&a, &x_j, &t_j, &b_commitment);

        // Check: z_j · A = T_j + c_j · X_j
        let lhs = (a.into_group() * z_j).into_affine();
        let rhs: <E as Pairing>::G1 = t_j.into_group() + x_j.into_group() * c_j;
        if lhs != rhs.into_affine() {
            return false;
        }
    }

    true
}

/// Compute Fiat-Shamir challenge for DLREP
fn compute_dlrep_challenge<E: Pairing>(
    y_bases: &[E::G2Affine],
    delta: &E::G2Affine,
    target: &E::G2Affine,
    commitment: &E::G2Affine,
) -> E::ScalarField {
    let mut hasher = Sha256::new();
    hasher.update(b"PVUGC_DLREP_B");

    for y in y_bases {
        let mut bytes = Vec::new();
        y.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }

    let mut bytes = Vec::new();
    delta.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    target.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    commitment.serialize_compressed(&mut bytes).unwrap();

    E::ScalarField::from_le_bytes_mod_order(&hasher.finalize())
}

/// Compute Fiat-Shamir challenge for per-column tie
fn compute_tie_col_challenge<E: Pairing>(
    a: &E::G1Affine,
    x_j: &E::G1Affine,
    commitment: &E::G1Affine,
    b_commitment: &E::G2Affine,
) -> E::ScalarField {
    let mut hasher = Sha256::new();
    hasher.update(b"PVUGC_TIE_COL");

    let mut bytes = Vec::new();
    a.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    x_j.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    commitment.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    // Bind to B-proof commitment to prevent mix-and-match across transcripts
    b_commitment.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);

    E::ScalarField::from_le_bytes_mod_order(&hasher.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;

    type E = Bls12_381;

    #[test]
    fn test_dlrep_b_proof() {
        let mut rng = StdRng::seed_from_u64(1);

        // Setup
        let y_bases = vec![G2Affine::rand(&mut rng), G2Affine::rand(&mut rng)];
        let delta_g2 = G2Affine::rand(&mut rng);

        let b_coeffs = vec![Fr::from(2u64), Fr::from(3u64)];
        let s = Fr::from(7u64);

        // Compute B' = s·δ + Σ b_j·Y_j
        let mut b_prime = delta_g2.into_group() * s;
        for (b_j, y_j) in b_coeffs.iter().zip(&y_bases) {
            b_prime += y_j.into_group() * b_j;
        }
        let b_prime = b_prime.into_affine();

        // Prove
        let proof: DlrepBProof<E> =
            prove_b_msm(b_prime, &y_bases, delta_g2, &b_coeffs, s, &mut rng);

        // Verify
        let valid = verify_b_msm(b_prime, &y_bases, delta_g2, &proof);

        assert!(valid);
    }

    #[test]
    fn test_per_column_ties_detect_delta_redistribution() {
        let mut rng = StdRng::seed_from_u64(2);

        type E = Bls12_381;
        // Base A and coefficients
        let a = G1Affine::rand(&mut rng);
        let b1 = Fr::from(7u64);
        let b2 = Fr::from(11u64);

        // Original per-column X's
        let x1 = (a.into_group() * b1).into_affine();
        let x2 = (a.into_group() * b2).into_affine();

        // Prove per-column ties (bind to a random B-commitment for this unit test)
        let b_commitment = G2Affine::rand(&mut rng);
        let ties = prove_ties_per_column::<E, _>(a, &[x1, x2], &[b1, b2], b_commitment, &mut rng);
        assert!(verify_ties_per_column::<E>(
            a,
            &[x1, x2],
            &ties,
            b_commitment
        ));

        // Apply equal/opposite delta that preserves the aggregate
        let delta = Fr::from(5u64);
        let x1_prime = (x1.into_group() + a.into_group() * delta).into_affine();
        let x2_prime = (x2.into_group() - a.into_group() * delta).into_affine();

        // Per-column ties must fail on modified columns
        assert!(!verify_ties_per_column::<E>(
            a,
            &[x1_prime, x2_prime],
            &ties,
            b_commitment
        ));
    }
}
