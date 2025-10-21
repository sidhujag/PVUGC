//! One-Sided Decapsulation
//!
//! Computes K = R^ρ using armed bases and GS commitments

use crate::arming::ColumnArms;
use crate::error::{Error, Result};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::AffineRepr;
use ark_std::Zero;

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
    // Subgroup predicate for G1 (accepts identity)
    let is_good_g1 = |g: &E::G1Affine| g.is_zero() || g.is_in_correct_subgroup_assuming_on_curve();

    // Sanity: number of X_B columns must match number of Y^ρ columns
    if commitments.x_b_cols.len() != col_arms.y_cols_rho.len() {
        return Err(Error::ColumnLengthMismatch);
    }

    // Validate all G1 limbs in X_B
    for (a, b) in &commitments.x_b_cols {
        if !is_good_g1(a) || !is_good_g1(b) {
            return Err(Error::InvalidG1Limb);
        }
    }

    // Validate all G1 limbs in Θ rows
    for (a, b) in &commitments.theta {
        if !is_good_g1(a) || !is_good_g1(b) {
            return Err(Error::InvalidG1Limb);
        }
    }

    // Validate canceller limbs for δ-side Θ commitment
    let (c0, c1) = commitments.theta_delta_cancel;
    if !is_good_g1(&c0) || !is_good_g1(&c1) {
        return Err(Error::InvalidG1Limb);
    }

    // Compute K = product of pairings per the one-sided PPE
    use ark_std::One;
    let mut k = PairingOutput::<E>(One::one());

    for ((x0, x1), y_rho) in commitments.x_b_cols.iter().zip(&col_arms.y_cols_rho) {
        k += E::pairing(*x0, *y_rho);
        k += E::pairing(*x1, *y_rho);
    }
    for (t0, t1) in &commitments.theta {
        k += E::pairing(*t0, col_arms.delta_rho);
        k += E::pairing(*t1, col_arms.delta_rho);
    }
    k += E::pairing(c0, col_arms.delta_rho);
    k += E::pairing(c1, col_arms.delta_rho);

    Ok(k)
}
