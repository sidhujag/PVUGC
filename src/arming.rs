use crate::error::{Error, Result};
use ark_ff::{PrimeField, Zero};

//! One-Sided Arming for PVUGC
//!
//! Arms statement-only G₂ bases (Y_j, δ) with ρ for permissionless decap.

use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Column bases for one-sided PPE: statement-only G₂ bases
#[derive(Clone, Debug)]
pub struct ColumnBases<E: Pairing> {
    /// Y columns = [β₂] ++ b_g2_query
    pub y_cols: Vec<E::G2Affine>,

    /// +δ for C-side
    pub delta: E::G2Affine,
}

/// Armed columns (ρ-powered)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ColumnArms<E: Pairing> {
    pub y_cols_rho: Vec<E::G2Affine>,
    pub delta_rho: E::G2Affine,
}

/// Arm the column bases with ρ
pub fn arm_columns<E: Pairing>(bases: &ColumnBases<E>, rho: &E::ScalarField) -> Result<ColumnArms<E>> {
    // Reject zero rho (it would nullify security)
    if rho.is_zero() {
        return Err(Error::InvalidRho);
    }

    // Subgroup predicate (accepts identity)
    let in_prime_subgroup_g2 = |g: &E::G2Affine| {
        g.is_zero() || g.is_in_correct_subgroup_assuming_on_curve()
    };

    // Subgroup checks for Y columns
    for y in &bases.y_cols {
        if !in_prime_subgroup_g2(y) {
            return Err(Error::NotInPrimeSubgroup);
        }
    }

    // δ must be non-zero and in the prime subgroup
    if bases.delta.is_zero() || !in_prime_subgroup_g2(&bases.delta) {
        return Err(Error::InvalidDelta);
    }

    // Compute Y^ρ and δ^ρ
    let y_cols_rho: Vec<_> = bases
        .y_cols
        .iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();

    let delta_rho = (bases.delta.into_group() * rho).into_affine();

    Ok(ColumnArms { y_cols_rho, delta_rho })
}



