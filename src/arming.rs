//! One-Sided Arming for PVUGC
//!
//! Arms statement-only G₂ bases (Y_j, δ) with ρ for permissionless decap.

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_ff::Zero;

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
pub fn arm_columns<E: Pairing>(bases: &ColumnBases<E>, rho: &E::ScalarField) -> ColumnArms<E> {
    use ark_ff::PrimeField;
    if rho.is_zero() { panic!("rho must be non-zero"); }
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
    let in_prime_subgroup_g2 = |g: &E::G2Affine| {
        if g.is_zero() { return true; }
        g.mul_bigint(order).is_zero()
    };
    // Subgroup checks
    for y in &bases.y_cols { if !in_prime_subgroup_g2(y) { panic!("Y col not in subgroup"); } }
    if !in_prime_subgroup_g2(&bases.delta) || bases.delta.is_zero() { panic!("delta invalid"); }

    let y_cols_rho: Vec<_> = bases
        .y_cols
        .iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();
    let delta_rho = (bases.delta.into_group() * rho).into_affine();
    ColumnArms { y_cols_rho, delta_rho }
}



