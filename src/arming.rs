//! One-Sided Arming for PVUGC
//!
//! Arms statement-only G₂ bases (Y_j, δ) with ρ for permissionless decap.

use crate::error::Error;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Zero;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

/// Column bases for one-sided PPE: statement-only G₂ bases
#[derive(Clone, Debug)]
pub struct ColumnBases<E: Pairing> {
    /// Y columns = [β₂] ++ b_g2_query
    pub y_cols: Vec<E::G2Affine>,

    /// +δ for C-side
    pub delta: E::G2Affine,
}

impl<E: Pairing> ColumnBases<E> {
    /// Validate that all bases are in the prime-order subgroup
    pub fn validate_subgroups(&self) -> crate::error::Result<()> {
        use ark_ff::PrimeField;
        let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
        let in_prime_subgroup_g2 = |g: &E::G2Affine| {
            if g.is_zero() {
                return true;
            }
            g.mul_bigint(order).is_zero()
        };

        // Check all Y bases
        for y in &self.y_cols {
            if !in_prime_subgroup_g2(y) {
                return Err(Error::InvalidSubgroup);
            }
        }

        // Check delta
        if self.delta.is_zero() {
            return Err(Error::ZeroDelta);
        }
        if !in_prime_subgroup_g2(&self.delta) {
            return Err(Error::InvalidSubgroup);
        }

        Ok(())
    }
}

/// Armed columns (ρ-powered)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct ColumnArms<E: Pairing> {
    pub y_cols_rho: Vec<E::G2Affine>,
    pub delta_rho: E::G2Affine,
}

/// Arm the column bases with ρ
///
/// **Security note**: This function assumes `bases` have been validated.
/// Call `bases.validate_subgroups()` ONCE when keys are first generated/loaded.
pub fn arm_columns<E: Pairing>(
    bases: &ColumnBases<E>,
    rho: &E::ScalarField,
) -> crate::error::Result<ColumnArms<E>> {
    if rho.is_zero() {
        return Err(Error::ZeroRho);
    }
    // Quick sanity check: delta must not be zero (cheap, always check)
    if bases.delta.is_zero() {
        return Err(Error::ZeroDelta);
    }

    let y_cols_rho: Vec<_> = bases
        .y_cols
        .iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();
    let delta_rho = (bases.delta.into_group() * rho).into_affine();

    Ok(ColumnArms {
        y_cols_rho,
        delta_rho,
    })
}
