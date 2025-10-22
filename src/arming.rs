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

impl<E: Pairing> ColumnBases<E> {
    /// Validate that all bases are in the prime-order subgroup
    pub fn validate_subgroups(&self) -> Result<(), &'static str> {
        use ark_ff::PrimeField;
        let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
        let in_prime_subgroup_g2 = |g: &E::G2Affine| {
            if g.is_zero() { return true; }
            g.mul_bigint(order).is_zero()
        };
        
        // Check all Y bases
        for y in &self.y_cols {
            if !in_prime_subgroup_g2(y) {
                return Err("Y column not in prime subgroup");
            }
        }
        
        // Check delta
        if self.delta.is_zero() {
            return Err("delta must be non-zero");
        }
        if !in_prime_subgroup_g2(&self.delta) {
            return Err("delta not in prime subgroup");
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
///
/// **Production usage**:
/// ```ignore
/// // At key loading/generation (ONCE):
/// let bases = build_column_bases(&vk, &pk);
/// bases.validate_subgroups().expect("Invalid Groth16 keys");
/// 
/// // During runtime (FAST, repeated many times):
/// let arms = arm_columns(&bases, &rho);  // No validation overhead
/// ```
pub fn arm_columns<E: Pairing>(bases: &ColumnBases<E>, rho: &E::ScalarField) -> ColumnArms<E> {
    if rho.is_zero() { panic!("rho must be non-zero"); }
    
    // In debug builds, do full validation to catch bugs during development
    #[cfg(debug_assertions)]
    {
        bases.validate_subgroups().expect("Base validation failed in debug build");
    }
    
    // Quick sanity check: delta must not be zero (cheap, always check)
    if bases.delta.is_zero() { panic!("delta must be non-zero"); }

    let y_cols_rho: Vec<_> = bases
        .y_cols
        .iter()
        .map(|y| (y.into_group() * rho).into_affine())
        .collect();
    let delta_rho = (bases.delta.into_group() * rho).into_affine();
    
    ColumnArms { y_cols_rho, delta_rho }
}



