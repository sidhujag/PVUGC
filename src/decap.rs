//! One-Sided Decapsulation
//!
//! Computes K = R^ρ using armed bases and GS commitments

use ark_ec::pairing::{Pairing, PairingOutput};
use crate::arming::ColumnArms;
#[allow(unused_imports)]
use ark_ec::AffineRepr;
#[allow(unused_imports)]
use ark_std::Zero;
use crate::error::{Error, Result};

/// GS commitments for one-sided PPE
#[derive(Clone, Debug)]
pub struct OneSidedCommitments<E: Pairing> {
    /// Column commitments for B-side: X_B_j limbs per column
    pub x_b_cols: Vec<(E::G1Affine, E::G1Affine)>,
    /// Theta/C-side limbs per Υ row (keep vector for zipping to W)
    pub theta: Vec<(E::G1Affine, E::G1Affine)>,
    /// Canceller limbs for the δ-side Θ commitment (rank=1). REQUIRED.
    pub theta_delta_cancel: (E::G1Affine, E::G1Affine),
}

/// Canonical decapsulation: K = R^ρ using column arms
pub fn decap<E: Pairing>(
    commitments: &OneSidedCommitments<E>,
    col_arms: &ColumnArms<E>,
) -> Result<PairingOutput<E>> {
    // Size check (always)
    if commitments.x_b_cols.len() != col_arms.y_cols_rho.len() { 
        return Err(Error::MismatchedSizes); 
    }
    
    // Subgroup checks: ONLY in debug builds (very expensive!)
    #[cfg(debug_assertions)]
    {
        use ark_ff::PrimeField;
        let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
        let is_good_g1 = |g: &E::G1Affine| {
            if g.is_zero() { return true; }
            g.mul_bigint(order).is_zero()
        };
        for (a,b) in &commitments.x_b_cols { 
            if !is_good_g1(a) || !is_good_g1(b) { panic!("Invalid X_B limb"); } 
        }
        for (a,b) in &commitments.theta { 
            if !is_good_g1(a) || !is_good_g1(b) { panic!("Invalid theta limb"); } 
        }
        let (c0, c1) = commitments.theta_delta_cancel;
        if !is_good_g1(&c0) || !is_good_g1(&c1) { panic!("Invalid cancel limb"); }
    }
    
    use ark_std::One;
    let mut k = PairingOutput::<E>(One::one());
    // Fixed-shape pairing schedule derived from pinned column counts
    let num_cols = commitments.x_b_cols.len();
    for i in 0..num_cols {
        let (x0, x1) = commitments.x_b_cols[i];
        let y_rho = col_arms.y_cols_rho[i];
        k += E::pairing(x0, y_rho);
        k += E::pairing(x1, y_rho);
    }
    let num_theta = commitments.theta.len();
    for i in 0..num_theta {
        let (t0, t1) = commitments.theta[i];
        k += E::pairing(t0, col_arms.delta_rho);
        k += E::pairing(t1, col_arms.delta_rho);
    }
    let (c0, c1) = commitments.theta_delta_cancel;
    k += E::pairing(c0, col_arms.delta_rho);
    k += E::pairing(c1, col_arms.delta_rho);
    Ok(k)
}

