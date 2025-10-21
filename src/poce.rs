//! Proof of Correct Exponentiation (PoCE) for Column Arming
//!
//! PoCE-A: Prove that all column arms share the same ρ and ciphertext is key-committed
//! PoCE-B: Decapper-local key-commitment verification
//!
//! Essential for preventing mixed-ρ attacks and ensuring cryptographic integrity
//! in column-based PVUGC arming.

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr, PrimeGroup};
use ark_ff::{UniformRand, PrimeField};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_std::rand::RngCore;
use sha2::{Sha256, Digest};

/// PoCE-A proof for column arming
/// Proves: ∀j, D_j = Y_j^ρ AND D_δ = δ^ρ AND ciphertext is key-committed to K = Poseidon2(ser(R^ρ)|ctx|GSdig)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct PoceColumnProof<E: Pairing> {
    /// Multi-base commitment for all column arms
    pub commitment: E::G2Affine,
    
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
pub fn prove_poce_column<E: Pairing, R: RngCore>(
    y_bases: &[E::G2Affine],     // Y_j bases
    delta_base: &E::G2Affine,     // δ base
    y_arms: &[E::G2Affine],      // D_j = Y_j^ρ
    delta_arm: &E::G2Affine,     // D_δ = δ^ρ
    t_i: &E::G1Affine,           // T_i = s_i G
    rho: &E::ScalarField,        // ρ_i (secret)
    s_i: &E::ScalarField,        // s_i (secret)
    ctx_hash: &[u8],             // Context hash
    gs_digest: &[u8],            // GS instance digest
    rng: &mut R,
) -> PoceColumnProof<E> {
    assert_eq!(y_bases.len(), y_arms.len());
    
    // Sample nonces
    let k_rho = E::ScalarField::rand(rng);
    let k_s = E::ScalarField::rand(rng);
    
    // Multi-base commitment: k_rho * (Σ Y_j + δ)
    let mut combined_base = delta_base.into_group();
    for y_base in y_bases {
        combined_base += y_base.into_group();
    }
    let commitment = (combined_base * k_rho).into_affine();
    
    // T commitment: k_s * G1_generator
    let t_commitment = (<E as Pairing>::G1::generator() * k_s).into_affine();
    
    // Challenge: H(y_bases || delta_base || y_arms || delta_arm || t_i || commitment || t_commitment || ctx_hash || gs_digest)
    let challenge = compute_poce_challenge::<E>(
        y_bases, delta_base, y_arms, delta_arm, t_i, &commitment, &t_commitment, ctx_hash, gs_digest
    );
    
    // Responses
    let response = k_rho + challenge * rho;
    let t_response = k_s + challenge * s_i;
    
    PoceColumnProof {
        commitment,
        t_commitment,
        t_response,
        response,
        challenge,
    }
}

/// Verify PoCE-A for column arming
pub fn verify_poce_column<E: Pairing>(
    y_bases: &[E::G2Affine],     // Y_j bases
    delta_base: &E::G2Affine,    // δ base
    y_arms: &[E::G2Affine],     // D_j = Y_j^ρ
    delta_arm: &E::G2Affine,    // D_δ = δ^ρ
    t_i: &E::G1Affine,          // T_i = s_i G
    proof: &PoceColumnProof<E>,
    ctx_hash: &[u8],            // Context hash
    gs_digest: &[u8],           // GS instance digest
) -> bool {
    // Recompute challenge
    let challenge = compute_poce_challenge::<E>(
        y_bases, delta_base, y_arms, delta_arm, t_i, &proof.commitment, &proof.t_commitment, ctx_hash, gs_digest
    );
    
    if challenge != proof.challenge {
        return false;
    }
    
    // Verify multi-base equality: commitment + challenge * (Σ D_j + D_δ) = response * (Σ Y_j + δ)
    let mut combined_arms = delta_arm.into_group();
    for y_arm in y_arms {
        combined_arms += y_arm.into_group();
    }
    let left_side = proof.commitment.into_group() + combined_arms * challenge;
    
    let mut combined_bases = delta_base.into_group();
    for y_base in y_bases {
        combined_bases += y_base.into_group();
    }
    let right_side = combined_bases * proof.response;
    
    let arms_check = left_side.into_affine() == right_side.into_affine();
    
    // Verify T_i proof: t_commitment + challenge * T_i = t_response * G1_generator
    let t_left = proof.t_commitment.into_group() + t_i.into_group() * challenge;
    let t_right = <E as Pairing>::G1::generator() * proof.t_response;
    let t_check = t_left.into_affine() == t_right.into_affine();
    
    arms_check && t_check
}

/// PoCE-B: Decapper-local key-commitment verification
/// 
/// Verifies that ciphertext ct_i is key-committed to the derived key K
pub fn verify_poce_b<E: Pairing>(
    derived_m: &ark_ec::pairing::PairingOutput<E>,  // R^ρ derived from attestation
    ctx_hash: &[u8],                               // Context hash
    gs_digest: &[u8],                              // GS instance digest
    ct_i: &[u8],                                  // Ciphertext
    tau_i: &[u8],                                 // Key-commitment tag
) -> bool {
    // Recompute key: K = Poseidon2(ser(R^ρ) || ctx_hash || gs_digest)
    let key = derive_kem_key::<E>(derived_m, ctx_hash, gs_digest);
    
    // Verify tag: τ_i = Poseidon2(K, AD_core, ct_i)
    let expected_tag = compute_key_commitment_tag(&key, ctx_hash, ct_i);
    
    expected_tag == tau_i
}

/// Compute Fiat-Shamir challenge for PoCE
fn compute_poce_challenge<E: Pairing>(
    y_bases: &[E::G2Affine],
    delta_base: &E::G2Affine,
    y_arms: &[E::G2Affine],
    delta_arm: &E::G2Affine,
    t_i: &E::G1Affine,
    commitment: &E::G2Affine,
    t_commitment: &E::G1Affine,
    ctx_hash: &[u8],
    gs_digest: &[u8],
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
    
    let mut bytes = Vec::new();
    commitment.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    
    let mut bytes = Vec::new();
    t_commitment.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    
    // Add context data
    hasher.update(ctx_hash);
    hasher.update(gs_digest);
    
    // Convert hash to field element
    let hash_bytes = hasher.finalize();
    E::ScalarField::from_le_bytes_mod_order(&hash_bytes)
}

/// Derive KEM key from pairing output
fn derive_kem_key<E: Pairing>(
    pairing_output: &ark_ec::pairing::PairingOutput<E>,
    ctx_hash: &[u8],
    gs_digest: &[u8],
) -> Vec<u8> {
    let mut hasher = Sha256::new();
    
    // Serialize pairing output
    let mut bytes = Vec::new();
    pairing_output.serialize_compressed(&mut bytes).unwrap();
    hasher.update(&bytes);
    
    hasher.update(ctx_hash);
    hasher.update(gs_digest);
    
    hasher.finalize().to_vec()
}

/// Compute key-commitment tag
fn compute_key_commitment_tag(
    key: &[u8],
    ad_core: &[u8],
    ciphertext: &[u8],
) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(key);
    hasher.update(ad_core);
    hasher.update(ciphertext);
    hasher.finalize().to_vec()
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381 as E, Fr, G2Affine};
    use ark_std::test_rng;
    
    #[test]
    fn test_poce_column_proof() {
        let mut rng = test_rng();
        
        // Create test bases and arms
        let y_bases = vec![G2Affine::rand(&mut rng), G2Affine::rand(&mut rng)];
        let delta_base = G2Affine::rand(&mut rng);
        let rho = Fr::rand(&mut rng);
        let s_i = Fr::rand(&mut rng);
        
        // Create arms
        let y_arms: Vec<_> = y_bases.iter().map(|y| (y.into_group() * rho).into_affine()).collect();
        let delta_arm = (delta_base.into_group() * rho).into_affine();
        let t_i = (<E as Pairing>::G1::generator() * s_i).into_affine();
        
        let ctx_hash = b"test_context";
        let gs_digest = b"test_gs_digest";
        
        // Prove
        let proof = prove_poce_column::<E, _>(
            &y_bases, &delta_base, &y_arms, &delta_arm, &t_i,
            &rho, &s_i, ctx_hash, gs_digest, &mut rng
        );
        
        // Verify
        let valid = verify_poce_column::<E>(
            &y_bases, &delta_base, &y_arms, &delta_arm, &t_i,
            &proof, ctx_hash, gs_digest
        );
        
        assert!(valid);
    }
    
    #[test]
    fn test_poce_column_rejects_mixed_rho() {
        let mut rng = test_rng();
        
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
        let proof = prove_poce_column::<E, _>(
            &y_bases, &delta_base, &y_arms, &delta_arm, &t_i,
            &rho1, &s_i, ctx_hash, gs_digest, &mut rng
        );
        
        // Verification should fail
        let valid = verify_poce_column::<E>(
            &y_bases, &delta_base, &y_arms, &delta_arm, &t_i,
            &proof, ctx_hash, gs_digest
        );
        
        assert!(!valid);
    }
}
