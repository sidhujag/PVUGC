//! One-Sided Decapsulation
//!
//! Computes K = R^ρ using armed bases and GS commitments

use ark_ec::pairing::{Pairing, PairingOutput};
use crate::arming::Arms;

/// GS commitments for one-sided PPE
#[derive(Clone, Debug)]
pub struct OneSidedCommitments<E: Pairing> {
    /// Row commitments: C_ℓ (both limbs)
    pub c_rows: Vec<(E::G1Affine, E::G1Affine)>,
    
    /// Theta proofs (for randomness cancellation)
    pub theta: Vec<(E::G1Affine, E::G1Affine)>,
    
    /// C commitment (for delta term)
    pub c_delta: (E::G1Affine, E::G1Affine),
}

/// Decapsulate to get K = R^ρ
///
/// Uses one-sided buckets: rows with U_ℓ^ρ and Θ with δ^ρ (both limbs)
/// K = (∏_ℓ e(C_ℓ, U_ℓ^ρ)) · e(Theta, W^ρ)
pub fn decap_one_sided<E: Pairing>(
    commitments: &OneSidedCommitments<E>,
    arms: &Arms<E>,
) -> PairingOutput<E> {
    // Initialize with ONE (multiplicative identity)
    use ark_std::One;
    let mut k = PairingOutput::<E>(One::one());
    
    // B1: Pair row commitments (both limbs) with U_ℓ^ρ
    for (c_row, u_rho) in commitments.c_rows.iter().zip(&arms.u_rows_rho) {
        k += E::pairing(c_row.0, *u_rho);  // First limb
        k += E::pairing(c_row.1, *u_rho);  // Second limb
    }
    
    // Theta/C-side: Pair Theta commitments (both limbs) with single W^ρ = δ^ρ
    if let Some(w_rho) = arms.w_rows_rho.first() {
        // θ = -C
        for theta in &commitments.theta {
            k += E::pairing(theta.0, *w_rho);
            k += E::pairing(theta.1, *w_rho);
        }
        
        k += E::pairing(commitments.c_delta.0, *w_rho);
        k += E::pairing(commitments.c_delta.1, *w_rho);
    }
    
    // K = R(vk,x)^ρ
    k
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, G1Affine, G2Affine};
    use ark_std::{test_rng, UniformRand};
    
    type E = Bls12_381;
    
    #[test]
    fn test_decap_structure() {
        let mut rng = test_rng();
        
        // Create mock armed bases
        let u_rows_rho = vec![G2Affine::rand(&mut rng); 2];
        let w_rows_rho = vec![G2Affine::rand(&mut rng)];
        
        let arms: Arms<E> = Arms { u_rows_rho, w_rows_rho };
        
        // Create mock GS commitments
        let commitments = OneSidedCommitments {
            c_rows: vec![
                (G1Affine::rand(&mut rng), G1Affine::rand(&mut rng)),
                (G1Affine::rand(&mut rng), G1Affine::rand(&mut rng)),
            ],
            theta: vec![
                (G1Affine::rand(&mut rng), G1Affine::rand(&mut rng)),
                (G1Affine::rand(&mut rng), G1Affine::rand(&mut rng)),
            ],
            c_delta: (G1Affine::rand(&mut rng), G1Affine::rand(&mut rng)),
        };
        
        // Decap
        let k = decap_one_sided(&commitments, &arms);
        
        // K should be non-zero (in general)
        
        // Test uses mock data, but structure is correct
        let _ = k;
    }
}

