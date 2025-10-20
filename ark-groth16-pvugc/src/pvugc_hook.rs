//! PVUGC Coefficient Hook
//!
//! Trait for recording MSM coefficients during Groth16 proving
//! Enables one-sided GS PPE construction

use ark_ec::pairing::Pairing;

/// Hook for recording Groth16 MSM coefficients
///
/// SECURITY: Only group elements are exposed (A, B, C, bases).
/// Scalars b_j are used ephemerally to compute X^(B)_j = b_j·A
/// and never stored or revealed.
pub trait PvugcCoefficientHook<E: Pairing> {
    /// Called after B is computed
    ///
    /// Parameters:
    /// - assignment: The b_j coefficients used in B MSM
    /// - a: The proof's A element (for computing X^(B)_j = b_j·A)
    /// - beta_g2: β from VK (Y_0 basis)
    /// - b_g2_query: The remaining Y_j bases from proving key
    /// - s: Delta coefficient (used for C-side)
    fn on_b_computed(
        &mut self,
        assignment: &[E::ScalarField],
        a: &E::G1Affine,
        beta_g2: &E::G2Affine,
        b_g2_query: &[E::G2Affine],
        s: &E::ScalarField,
    );
    
    /// Called after C is computed
    ///
    /// Parameters:
    /// - c: The proof's C element
    /// - delta_g2: δ from VK (base for C-side)
    fn on_c_computed(
        &mut self,
        c: &E::G1Affine,
        delta_g2: &E::G2Affine,
    );
}

/// No-op hook (default)
pub struct NoOpHook;

impl<E: Pairing> PvugcCoefficientHook<E> for NoOpHook {
    fn on_b_computed(
        &mut self,
        _assignment: &[E::ScalarField],
        _a: &E::G1Affine,
        _beta_g2: &E::G2Affine,
        _b_g2_query: &[E::G2Affine],
        _s: &E::ScalarField,
    ) {}
    
    fn on_c_computed(&mut self, _c: &E::G1Affine, _delta_g2: &E::G2Affine) {}
}

