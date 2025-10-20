//! Discrete Log Representation (DLREP) Proofs
//!
//! Schnorr-style proofs for:
//! 1. B = Σ b_j·Y_j (multi-base DLREP in G₂)
//! 2. X^(B)_j = A^b_j (same-scalar ties across groups)

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_ff::{UniformRand, PrimeField};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_std::rand::RngCore;
use sha2::{Sha256, Digest};

/// Proof that B = Σ b_j·Y_j (aggregated multi-base Schnorr)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DlrepBProof<E: Pairing> {
    /// Commitment: T = Σ k_j·Y_j
    pub commitment: E::G2Affine,
    
    /// Responses: z_j = k_j + c·b_j
    pub responses: Vec<E::ScalarField>,
}

/// Proof that aggregated tie: Σ r_j·X^(B)_j = (Σ r_j·b_j)·A
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct DlrepTieProof<E: Pairing> {
    /// Commitment in G₁: T_A = k·A
    pub commitment_g1: E::G1Affine,
    
    /// Response: z = k + c·(Σ r_j·b_j)
    pub response: E::ScalarField,
}

/// Prove B = Σ b_j·Y_j (multi-base DLREP)
pub fn prove_b_msm<E: Pairing, R: RngCore>(
    b_prime: E::G2Affine,  // B - β - Y_0 (public target)
    y_bases: &[E::G2Affine],  // Y_1, ..., Y_N
    delta_g2: E::G2Affine,  // δ for s term
    b_coeffs: &[E::ScalarField],  // b_1, ..., b_N (secret)
    s: E::ScalarField,  // Secret randomness
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
    // Recompute challenge
    let challenge = compute_dlrep_challenge::<E>(&y_bases, &delta_g2, &b_prime, &proof.commitment);
    
    // Verify: Σ z_j·Y_j = T + c·B'
    let mut lhs = delta_g2.into_group() * proof.responses[0];
    for (z_j, y_j) in proof.responses[1..].iter().zip(y_bases) {
        lhs += y_j.into_group() * z_j;
    }
    
    let rhs: E::G2 = proof.commitment.into_group() 
            + b_prime.into_group() * challenge;
    
    lhs.into_affine() == rhs.into_affine()
}

/// Prove aggregated same-scalar tie: X_agg = u_agg·A
/// where X_agg = Σ r_j·X^(B)_j, u_agg = Σ r_j·b_j
pub fn prove_tie_aggregated<E: Pairing, R: RngCore>(
    a: E::G1Affine,
    x_agg: E::G1Affine,  // Aggregated X^(B)
    u_agg: E::ScalarField,  // Aggregated coefficient
    rng: &mut R,
) -> DlrepTieProof<E> {
    // Sample nonce
    let k = E::ScalarField::rand(rng);
    
    // Commitment: T = k·A
    let commitment_g1 = (a.into_group() * k).into_affine();
    
    // Challenge
    let challenge = compute_tie_challenge::<E>(&a, &x_agg, &commitment_g1);
    
    // Response: z = k + c·u_agg
    let response = k + challenge * u_agg;
    
    DlrepTieProof {
        commitment_g1,
        response,
    }
}

/// Verify aggregated tie
pub fn verify_tie_aggregated<E: Pairing>(
    a: E::G1Affine,
    x_agg: E::G1Affine,
    proof: &DlrepTieProof<E>,
) -> bool {
    let challenge = compute_tie_challenge::<E>(&a, &x_agg, &proof.commitment_g1);
    
    // Verify: z·A = T + c·X_agg
    let lhs = (a.into_group() * proof.response).into_affine();
    let rhs: E::G1 = proof.commitment_g1.into_group() + x_agg.into_group() * challenge;
    
    lhs == rhs.into_affine()
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

/// Compute Fiat-Shamir challenge for tie proof
fn compute_tie_challenge<E: Pairing>(
    a: &E::G1Affine,
    x_agg: &E::G1Affine,
    commitment: &E::G1Affine,
) -> E::ScalarField {
    let mut hasher = Sha256::new();
    hasher.update(b"PVUGC_TIE_AGG");
    
    let mut bytes = Vec::new();
    a.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    x_agg.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    commitment.serialize_compressed(&mut bytes).unwrap();
    
    E::ScalarField::from_le_bytes_mod_order(&hasher.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
    use ark_std::test_rng;
    
    type E = Bls12_381;
    
    #[test]
    fn test_dlrep_b_proof() {
        let mut rng = test_rng();
        
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
        let proof: DlrepBProof<E> = prove_b_msm(b_prime, &y_bases, delta_g2, &b_coeffs, s, &mut rng);
        
        // Verify
        let valid = verify_b_msm(b_prime, &y_bases, delta_g2, &proof);
        
        assert!(valid);
    }
    
    #[test]
    fn test_tie_proof() {
        let mut rng = test_rng();
        
        let a = G1Affine::rand(&mut rng);
        let u_agg = Fr::from(5u64);
        
        // X_agg = u_agg·A
        let x_agg = (a.into_group() * u_agg).into_affine();
        
        // Prove
        let proof: DlrepTieProof<E> = prove_tie_aggregated(a, x_agg, u_agg, &mut rng);
        
        // Verify
        let valid = verify_tie_aggregated(a, x_agg, &proof);
        
        assert!(valid);
    }
}

