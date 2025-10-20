//! Proof of Correct Exponentiation (PoCE) Across Multiple Arms
//!
//! Proves that all armed bases share the same ρ:
//! D_j = U_j^ρ for all j, and W_a = δ^ρ

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_ff::{UniformRand, PrimeField};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_std::rand::RngCore;
use sha2::{Sha256, Digest};

/// Proof that same ρ used for all arms
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PoceAcrossProof<E: Pairing> {
    /// Commitments for each base
    pub commitments: Vec<E::G2Affine>,
    
    /// Single response (same ρ for all)
    pub response: E::ScalarField,
}

/// Prove that D_j = U_j^ρ for all j with same ρ
///
/// This is a multi-base Schnorr proof in G₂
pub fn prove_poce_across<E: Pairing, R: RngCore>(
    bases: &[E::G2Affine],  // U_j, W_a
    arms: &[E::G2Affine],   // U_j^ρ, W_a^ρ
    rho: &E::ScalarField,   // The exponent (secret)
    rng: &mut R,
) -> PoceAcrossProof<E> {
    assert_eq!(bases.len(), arms.len());
    
    // Sample nonce
    let k = E::ScalarField::rand(rng);
    
    // Commitments: T_j = k·U_j for each base
    let commitments: Vec<E::G2Affine> = bases
        .iter()
        .map(|u| (u.into_group() * k).into_affine())
        .collect();
    
    // Challenge: c = H(bases || arms || commitments)
    let challenge = compute_poce_challenge::<E>(bases, arms, &commitments);
    
    // Response: z = k + c·ρ
    let response = k + challenge * rho;
    
    PoceAcrossProof {
        commitments,
        response,
    }
}

/// Verify PoCE-Across
///
/// Checks: z·U_j = T_j + c·D_j for all j
pub fn verify_poce_across<E: Pairing>(
    bases: &[E::G2Affine],
    arms: &[E::G2Affine],
    proof: &PoceAcrossProof<E>,
) -> bool {
    if bases.len() != arms.len() || bases.len() != proof.commitments.len() {
        return false;
    }
    
    let challenge = compute_poce_challenge::<E>(bases, arms, &proof.commitments);
    
    // Verify each: z·U_j = T_j + c·D_j
    for ((u_j, d_j), t_j) in bases.iter().zip(arms).zip(&proof.commitments) {
        let lhs = (u_j.into_group() * proof.response).into_affine();
        let rhs: E::G2 = t_j.into_group() + d_j.into_group() * challenge;
        
        if lhs != rhs.into_affine() {
            return false;
        }
    }
    
    true
}

/// Compute Fiat-Shamir challenge for PoCE
fn compute_poce_challenge<E: Pairing>(
    bases: &[E::G2Affine],
    arms: &[E::G2Affine],
    commitments: &[E::G2Affine],
) -> E::ScalarField {
    let mut hasher = Sha256::new();
    hasher.update(b"PVUGC_POCE_ACROSS");
    
    for u in bases {
        let mut bytes = Vec::new();
        u.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }
    
    for d in arms {
        let mut bytes = Vec::new();
        d.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }
    
    for t in commitments {
        let mut bytes = Vec::new();
        t.serialize_compressed(&mut bytes).unwrap();
        hasher.update(&bytes);
    }
    
    E::ScalarField::from_le_bytes_mod_order(&hasher.finalize())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G2Affine};
    use ark_std::test_rng;
    
    type E = Bls12_381;
    
    #[test]
    fn test_poce_across() {
        let mut rng = test_rng();
        
        // Create bases
        let bases = vec![G2Affine::rand(&mut rng); 3];
        
        // Arm with ρ
        let rho = Fr::rand(&mut rng);
        let arms: Vec<_> = bases
            .iter()
            .map(|u| (u.into_group() * rho).into_affine())
            .collect();
        
        // Prove
        let proof: PoceAcrossProof<E> = prove_poce_across(&bases, &arms, &rho, &mut rng);
        
        // Verify
        let valid = verify_poce_across(&bases, &arms, &proof);
        
        assert!(valid);
    }
    
    #[test]
    fn test_poce_fails_different_rho() {
        let mut rng = test_rng();
        
        let bases = vec![G2Affine::rand(&mut rng); 3];
        
        // Arm first two with ρ₁
        let rho1 = Fr::rand(&mut rng);
        let mut arms: Vec<_> = bases[..2]
            .iter()
            .map(|u| (u.into_group() * rho1).into_affine())
            .collect();
        
        // Arm third with different ρ₂
        let rho2 = Fr::rand(&mut rng);
        arms.push((bases[2].into_group() * rho2).into_affine());
        
        // Try to prove with ρ₁
        let proof: PoceAcrossProof<E> = prove_poce_across(&bases, &arms, &rho1, &mut rng);
        
        // Should fail (third element uses different ρ)
        let valid = verify_poce_across(&bases, &arms, &proof);
        
        assert!(!valid);
    }
}

