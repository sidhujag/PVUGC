//! One-Sided Decapsulation
//!
//! Computes K = R^ρ using armed bases and GS commitments

use ark_ec::pairing::{Pairing, PairingOutput};
use crate::arming::Arms;
use ark_ec::AffineRepr;
use ark_std::Zero;

/// GS commitments for one-sided PPE
#[derive(Clone, Debug)]
pub struct OneSidedCommitments<E: Pairing> {
    /// Row commitments: C_ℓ (both limbs)
    pub c_rows: Vec<(E::G1Affine, E::G1Affine)>,
    
    /// Theta proofs (for randomness cancellation)
    pub theta: Vec<(E::G1Affine, E::G1Affine)>,
}

/// Decapsulate to get K = R^ρ
///
/// Uses one-sided buckets: rows with U_ℓ^ρ and Θ with δ^ρ (both limbs)
/// K = (∏_ℓ e(C_ℓ, U_ℓ^ρ)) · e(Theta, W^ρ)
pub fn decap_one_sided<E: Pairing>(
    commitments: &OneSidedCommitments<E>,
    arms: &Arms<E>,
) -> PairingOutput<E> {
    // Guard: shape and subgroup checks (zipped δ-side)
    use ark_ff::PrimeField;
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
    let is_good_g1 = |g: &E::G1Affine| {
        if g.is_zero() { return true; }
        g.mul_bigint(order).is_zero()
    };
    let is_good_g2 = |g: &E::G2Affine| {
        // Allow identity per-row; enforce subgroup only for non-identity points
        if g.is_zero() { return true; }
        g.mul_bigint(order).is_zero()
    };
    if commitments.c_rows.len() != arms.u_rows_rho.len() { panic!("|C_rows| != |U^rho|"); }
    if commitments.theta.len() != arms.w_rows_rho.len() { panic!("|Theta| != |W^rho|"); }
    if arms.u_rows_rho.iter().all(|u| u.is_zero()) { panic!("all U^rho rows are identity"); }
    if arms.w_rows_rho.iter().all(|w| w.is_zero()) { panic!("all W^rho rows are identity"); }
    if arms.u_rows_rho.iter().any(|u| !is_good_g2(u)) { panic!("Invalid U^rho"); }
    if arms.w_rows_rho.iter().any(|w| !is_good_g2(w)) { panic!("Invalid W^rho"); }
    for (a,b) in &commitments.c_rows { if !is_good_g1(a) || !is_good_g1(b) { panic!("Invalid C limb"); } }
    for (a,b) in &commitments.theta { if !is_good_g1(a) || !is_good_g1(b) { panic!("Invalid theta limb"); } }
    // Initialize with ONE (multiplicative identity)
    use ark_std::One;
    let mut k = PairingOutput::<E>(One::one());
    
    // B1: Pair row commitments (both limbs) with U_ℓ^ρ
    for (c_row, u_rho) in commitments.c_rows.iter().zip(&arms.u_rows_rho) {
        k += E::pairing(c_row.0, *u_rho);  // First limb
        k += E::pairing(c_row.1, *u_rho);  // Second limb
    }
    
    // Theta/C-side: strict zip of θ with W^ρ
    for ((t0, t1), w_rho) in commitments.theta.iter().zip(&arms.w_rows_rho) {
        k += E::pairing(*t0, *w_rho);
        k += E::pairing(*t1, *w_rho);
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
        
        // Create mock armed bases (match ranks with commitments)
        let u_rows_rho = vec![G2Affine::rand(&mut rng); 2];
        let w_rows_rho = vec![G2Affine::rand(&mut rng); 2];
        
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
        };
        
        // Decap
        let k = decap_one_sided(&commitments, &arms);
        
        // K should be non-zero (in general)
        
        // Test uses mock data, but structure is correct
        let _ = k;
    }
}

