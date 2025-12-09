//! OOD (Out-of-Domain) Evaluation Utilities
//!
//! This module provides utilities for OOD evaluation verification.
//! The main components are:
//!
//! - `OodFrame`: Structure holding trace and composition evaluations at OOD point
//! - `evaluate_aggregator_constraints`: Evaluates the Aggregator STARK's constraints
//!   (VDF-like: col0' = col0³ + col1, col1' = col0)
//! - `CompositionPoly`: Verifies composition polynomial consistency
//! - `verify_ood_constraint_equation`: Full OOD verification with boundary/exemption handling
//!
//! ## STARK OOD Verification Formula
//!
//! The composition polynomial encodes transition and boundary constraints:
//!
//! ```text
//! transition_sum / Z_trans + boundary_sum / Z_bound = C(z)
//! ```
//!
//! Where:
//! - `Z_trans = (z^n - 1) / (z - g^{n-1})` (transition zerofier with exemption)
//! - `Z_bound = z - g^{n-1}` (boundary constraint divisor for last step)
//!
//! Multiplying through to avoid division:
//! ```text
//! transition_sum * exemption² + boundary_sum * (z^n - 1) = C(z) * (z^n - 1) * exemption
//! ```
//!
//! Where `exemption = z - g^{n-1}`.
//!
//! ## Usage Context
//!
//! This module is used for:
//! 1. Integration tests validating constraint formulas
//! 2. The VerifierAir's in-circuit OOD verification
//! 3. Understanding the verification flow

use winterfell::math::{fields::f64::BaseElement, FieldElement};

// ============================================================================
// OOD FRAME
// ============================================================================

/// OOD evaluation frame containing trace values at z and z·g
#[derive(Clone, Debug)]
pub struct OodFrame {
    /// Trace evaluations at OOD point z
    pub trace_current: Vec<BaseElement>,
    /// Trace evaluations at z·g (next step)
    pub trace_next: Vec<BaseElement>,
    /// Composition polynomial evaluations at z
    pub composition: Vec<BaseElement>,
    /// Composition polynomial evaluations at z·g (for LINEAR batching)
    pub composition_next: Vec<BaseElement>,
}

impl OodFrame {
    pub fn new(
        trace_current: Vec<BaseElement>,
        trace_next: Vec<BaseElement>,
        composition: Vec<BaseElement>,
        composition_next: Vec<BaseElement>,
    ) -> Self {
        Self {
            trace_current,
            trace_next,
            composition,
            composition_next,
        }
    }

    /// Trace width
    pub fn trace_width(&self) -> usize {
        self.trace_current.len()
    }

    /// Composition width (number of columns)
    pub fn comp_width(&self) -> usize {
        self.composition.len()
    }
}

// ============================================================================
// AIR CONSTRAINT EVALUATION
// ============================================================================

/// Simple AIR constraints for the Aggregator STARK
///
/// The Aggregator STARK has two columns with VDF-like transitions:
/// - col0[i+1] = col0[i]^3 + col1[i]
/// - col1[i+1] = col0[i]
///
/// At OOD point z:
/// - constraint0: trace_next[0] - (trace_current[0]^3 + trace_current[1]) = 0
/// - constraint1: trace_next[1] - trace_current[0] = 0
pub fn evaluate_aggregator_constraints(
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
) -> Vec<BaseElement> {
    assert_eq!(trace_current.len(), 2);
    assert_eq!(trace_next.len(), 2);

    let col0 = trace_current[0];
    let col1 = trace_current[1];
    let next0 = trace_next[0];
    let next1 = trace_next[1];

    // VDF-like constraints
    let c0 = next0 - (col0 * col0 * col0 + col1);
    let c1 = next1 - col0;

    vec![c0, c1]
}

/// Evaluate boundary constraint at OOD point
///
/// For Aggregator STARK, we have:
/// - Final: trace[trace_len-1][1] = pub_result
///
/// At OOD point z, this evaluates to: trace_current[1] - pub_result
/// (since trace_current is the interpolated trace evaluated at z)
pub fn evaluate_boundary_constraint(
    trace_value: BaseElement,
    expected_value: BaseElement,
) -> BaseElement {
    trace_value - expected_value
}

/// OOD verification parameters
#[derive(Clone, Debug)]
pub struct OodParams {
    /// OOD challenge point z
    pub z: BaseElement,
    /// Trace length (power of 2)
    pub trace_len: usize,
    /// Trace domain generator g
    pub g_trace: BaseElement,
    /// Constraint composition coefficients [alpha_0, alpha_1, beta_0]
    /// - alpha_0, alpha_1: transition constraint coefficients
    /// - beta_0: boundary constraint coefficient
    pub constraint_coeffs: Vec<BaseElement>,
    /// Public result (boundary constraint target)
    pub pub_result: BaseElement,
}

/// Verify the full OOD constraint equation
///
/// This is the critical security check that ensures the composition polynomial
/// correctly represents the constraint quotient. The formula verified is:
///
/// ```text
/// transition_sum * exemption² + boundary_sum * (z^n - 1) = C(z) * (z^n - 1) * exemption
/// ```
///
/// Where:
/// - transition_sum = alpha_0 * c0(z) + alpha_1 * c1(z)
/// - boundary_sum = beta_0 * (trace_current[1] - pub_result)
/// - exemption = z - g^{n-1}
/// - C(z) = C_0(z) + C_1(z) * z^n (composition polynomial split into columns)
pub fn verify_ood_constraint_equation(
    ood_frame: &OodFrame,
    params: &OodParams,
) -> Result<(), OodVerificationError> {
    if ood_frame.trace_width() < 2 {
        return Err(OodVerificationError::TraceWidthMismatch);
    }
    if ood_frame.comp_width() < 2 {
        return Err(OodVerificationError::CompositionMismatch {
            expected: BaseElement::ZERO,
            got: BaseElement::ONE,
        });
    }
    if params.constraint_coeffs.len() < 3 {
        return Err(OodVerificationError::CoeffCountMismatch);
    }

    let z = params.z;
    let trace_len = params.trace_len;
    let g = params.g_trace;

    // Compute z^n
    let z_pow_n = z.exp((trace_len as u64).into());

    // Compute g^{n-1}
    let g_pow_n_minus_1 = g.exp(((trace_len - 1) as u64).into());

    // Exemption factor: z - g^{n-1}
    let exemption = z - g_pow_n_minus_1;

    // Zerofier numerator: z^n - 1
    let zerofier_num = z_pow_n - BaseElement::ONE;

    // exemption²
    let exemption_sq = exemption * exemption;

    // ==============================================================
    // TRANSITION CONSTRAINTS
    // ==============================================================
    let constraints = evaluate_aggregator_constraints(
        &ood_frame.trace_current,
        &ood_frame.trace_next,
    );

    let alpha_0 = params.constraint_coeffs[0];
    let alpha_1 = params.constraint_coeffs[1];

    let transition_sum = alpha_0 * constraints[0] + alpha_1 * constraints[1];

    // ==============================================================
    // BOUNDARY CONSTRAINT
    // Assertion: column 1, step (trace_len - 1), equals pub_result
    // ==============================================================
    let boundary_value = ood_frame.trace_current[1] - params.pub_result;
    let beta_0 = params.constraint_coeffs[2];
    let boundary_sum = beta_0 * boundary_value;

    // ==============================================================
    // LHS = transition_sum * exemption² + boundary_sum * (z^n - 1)
    // ==============================================================
    let lhs = transition_sum * exemption_sq + boundary_sum * zerofier_num;

    // ==============================================================
    // RHS = C(z) * (z^n - 1) * exemption
    // where C(z) = C_0(z) + C_1(z) * z^n
    // ==============================================================
    let c_combined = ood_frame.composition[0] + ood_frame.composition[1] * z_pow_n;
    let rhs = c_combined * zerofier_num * exemption;

    // Verify LHS == RHS
    if lhs != rhs {
        return Err(OodVerificationError::CompositionMismatch {
            expected: rhs,
            got: lhs,
        });
    }

    Ok(())
}

// ============================================================================
// COMPOSITION POLYNOMIAL CHECK
// ============================================================================

/// Composition polynomial structure for degree-2 constraints
///
/// The composition polynomial C(x) combines:
/// - Transition constraints at all steps
/// - Boundary constraints at first/last step
///
/// C(x) = (1/Z_H(x)) * Σ_i α_i * c_i(x)
///
/// where Z_H(x) = x^n - 1 is the vanishing polynomial
pub struct CompositionPoly {
    /// Degree of composition (trace_len - 1 for VDF-like)
    pub degree: usize,
    /// Number of composition columns
    pub num_columns: usize,
}

impl CompositionPoly {
   

    /// Full composition verification with boundary constraints and exemption
    ///
    /// This verifies the complete OOD constraint equation:
    /// ```text
    /// transition_sum * exemption² + boundary_sum * (z^n - 1) = C(z) * (z^n - 1) * exemption
    /// ```
    pub fn verify_composition_full(
        &self,
        ood_frame: &OodFrame,
        params: &OodParams,
    ) -> Result<(), OodVerificationError> {
        verify_ood_constraint_equation(ood_frame, params)
    }
}

// ============================================================================
// ERROR TYPES
// ============================================================================

/// Errors during OOD verification
#[derive(Clone, Debug)]
pub enum OodVerificationError {
    /// Coefficient count doesn't match constraint count
    CoeffCountMismatch,
    /// Composition polynomial doesn't match constraints
    CompositionMismatch {
        expected: BaseElement,
        got: BaseElement,
    },
    /// Boundary constraint failed
    BoundaryConstraintFailed,
    /// Trace width mismatch
    TraceWidthMismatch,
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aggregator_constraints_valid_transition() {
        // Valid VDF transition: next0 = curr0^3 + curr1, next1 = curr0
        let col0 = BaseElement::new(2);
        let col1 = BaseElement::new(3);

        // next0 = 2^3 + 3 = 11
        // next1 = 2
        let next0 = BaseElement::new(11);
        let next1 = BaseElement::new(2);

        let constraints = evaluate_aggregator_constraints(&[col0, col1], &[next0, next1]);

        assert_eq!(constraints[0], BaseElement::ZERO);
        assert_eq!(constraints[1], BaseElement::ZERO);
    }

    #[test]
    fn test_aggregator_constraints_invalid_transition() {
        // Invalid transition
        let col0 = BaseElement::new(2);
        let col1 = BaseElement::new(3);

        // Wrong values
        let next0 = BaseElement::new(10); // Should be 11
        let next1 = BaseElement::new(3);  // Should be 2

        let constraints = evaluate_aggregator_constraints(&[col0, col1], &[next0, next1]);

        assert_ne!(constraints[0], BaseElement::ZERO);
        assert_ne!(constraints[1], BaseElement::ZERO);
    }

    #[test]
    fn test_boundary_constraint() {
        let trace_value = BaseElement::new(42);
        let expected = BaseElement::new(42);

        assert_eq!(
            evaluate_boundary_constraint(trace_value, expected),
            BaseElement::ZERO
        );

        let wrong_expected = BaseElement::new(43);
        assert_ne!(
            evaluate_boundary_constraint(trace_value, wrong_expected),
            BaseElement::ZERO
        );
    }

    #[test]
    fn test_ood_frame_creation() {
        let frame = OodFrame::new(
            vec![BaseElement::new(1), BaseElement::new(2)],
            vec![BaseElement::new(3), BaseElement::new(4)],
            vec![BaseElement::new(5), BaseElement::new(6)],
            vec![BaseElement::new(7), BaseElement::new(8)],
        );

        assert_eq!(frame.trace_width(), 2);
        assert_eq!(frame.comp_width(), 2);
    }

    #[test]
    fn test_ood_params_creation() {
        // Goldilocks field primitive root for trace domain
        // For trace_len = 8, g = 2^(64-3) mod p = some generator of order 8
        let g_trace = BaseElement::new(18446744069414584320u64); // 2^61 in Goldilocks
        
        let params = OodParams {
            z: BaseElement::new(12345),
            trace_len: 8,
            g_trace,
            constraint_coeffs: vec![
                BaseElement::new(1), // alpha_0
                BaseElement::new(2), // alpha_1
                BaseElement::new(3), // beta_0
            ],
            pub_result: BaseElement::new(100),
        };
        
        assert_eq!(params.trace_len, 8);
        assert_eq!(params.constraint_coeffs.len(), 3);
    }

    #[test]
    fn test_verify_ood_constraint_equation_valid_transition() {
        // Create a valid OOD frame where transition constraints are satisfied
        // For VDF: next0 = curr0^3 + curr1, next1 = curr0
        let curr0 = BaseElement::new(2);
        let curr1 = BaseElement::new(3);
        let next0 = BaseElement::new(11); // 2^3 + 3 = 11
        let next1 = BaseElement::new(2);  // = curr0

        // When constraints are zero, the composition should be zero too
        // (for valid execution at non-boundary steps)
        let frame = OodFrame::new(
            vec![curr0, curr1],
            vec![next0, next1],
            vec![BaseElement::ZERO, BaseElement::ZERO], // C(z) = 0
            vec![BaseElement::ZERO, BaseElement::ZERO],
        );

        // With all coeffs = 0, the equation becomes 0 = 0
        let params = OodParams {
            z: BaseElement::new(12345),
            trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            constraint_coeffs: vec![
                BaseElement::ZERO, // alpha_0
                BaseElement::ZERO, // alpha_1
                BaseElement::ZERO, // beta_0
            ],
            pub_result: curr1, // Match boundary to avoid boundary term
        };

        // Should pass because 0 = 0
        assert!(verify_ood_constraint_equation(&frame, &params).is_ok());
    }

    #[test]
    fn test_verify_ood_constraint_detects_invalid() {
        // Create an invalid OOD frame where constraints are NOT satisfied
        let curr0 = BaseElement::new(2);
        let curr1 = BaseElement::new(3);
        let next0 = BaseElement::new(999); // Wrong! Should be 11
        let next1 = BaseElement::new(999); // Wrong! Should be 2

        let frame = OodFrame::new(
            vec![curr0, curr1],
            vec![next0, next1],
            vec![BaseElement::ZERO, BaseElement::ZERO],
            vec![BaseElement::ZERO, BaseElement::ZERO],
        );

        // Non-zero coeffs should detect the mismatch
        let params = OodParams {
            z: BaseElement::new(12345),
            trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            constraint_coeffs: vec![
                BaseElement::ONE, // alpha_0
                BaseElement::ONE, // alpha_1
                BaseElement::ZERO, // beta_0 (ignore boundary for this test)
            ],
            pub_result: curr1,
        };

        // Should fail - constraints are non-zero but composition is zero
        assert!(verify_ood_constraint_equation(&frame, &params).is_err());
    }

    #[test]
    fn test_exemption_factor_calculation() {
        // Test that exemption = z - g^{n-1} is computed correctly
        let z = BaseElement::new(100);
        let trace_len = 8usize;
        let g = BaseElement::new(2); // Simple generator for test

        // g^{n-1} = 2^7 = 128
        let g_pow_n_minus_1 = g.exp(((trace_len - 1) as u64).into());
        assert_eq!(g_pow_n_minus_1, BaseElement::new(128));

        // exemption = 100 - 128 (in field)
        let exemption = z - g_pow_n_minus_1;
        // In Goldilocks field, this wraps around
        assert_ne!(exemption, BaseElement::ZERO);
    }

    /// Test Verifier AIR constraint evaluation using real proof data
    #[test]
    fn test_verifier_air_ood_verification() {
        use crate::stark::verifier_air::constraints::evaluate_all;
        use crate::stark::verifier_air::{VerifierPublicInputs, VERIFIER_TRACE_WIDTH};
        use winterfell::EvaluationFrame;
        
        // Create a test OOD frame for the Verifier AIR
        // Using simple values that should produce predictable constraint evaluations
        let mut current = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        let mut next = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        
        // Set up as a Nop operation (111 in binary selectors)
        current[0] = BaseElement::ONE; // s0
        current[1] = BaseElement::ONE; // s1
        current[2] = BaseElement::ONE; // s2
        
        // Next row also Nop
        next[0] = BaseElement::ONE;
        next[1] = BaseElement::ONE;
        next[2] = BaseElement::ONE;
        
        // For Nop, hash state should copy (next = current)
        for i in 3..15 {
            let val = BaseElement::new(i as u64);
            current[i] = val;
            next[i] = val; // Copy for Nop
        }
        
        // FRI columns (15-22)
        for i in 15..23 {
            let val = BaseElement::new((i * 10) as u64);
            current[i] = val;
            next[i] = val; // Copy constraint
        }
        
        // Aux columns (23-26)
        current[23] = BaseElement::new(7); // Round counter = 7 (Nop/Squeeze state)
        next[23] = BaseElement::new(7);
        
        for i in 24..27 {
            current[i] = BaseElement::ZERO;
            next[i] = BaseElement::ZERO;
        }
        
        // Evaluate constraints using the Verifier AIR's evaluate_all
        let pub_inputs = VerifierPublicInputs {
            statement_hash: [BaseElement::ZERO; 4],
            trace_commitment: [BaseElement::ZERO; 4],
            comp_commitment: [BaseElement::ZERO; 4],
            fri_commitments: vec![],
            num_queries: 2,
            proof_trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            pub_result: BaseElement::ZERO,
        };
        let mut result = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        
        // Create evaluation frame
        let frame = EvaluationFrame::from_rows(current.clone(), next.clone());
        
        evaluate_all(&frame, &[], &mut result, &pub_inputs);
        
        // For a valid Nop transition, all constraints should be zero
        println!("Constraint evaluations for Nop transition:");
        for (i, c) in result.iter().enumerate() {
            println!("  constraint[{}] = {:?}", i, c.as_int());
        }
        
        // Selector constraints should be zero (binary check on 0 and 1)
        assert_eq!(result[0], BaseElement::ZERO, "s0 should be binary");
        assert_eq!(result[1], BaseElement::ZERO, "s1 should be binary");
        assert_eq!(result[2], BaseElement::ZERO, "s2 should be binary");
        
        // Hash state constraints should be zero for Nop (copy)
        for i in 3..15 {
            assert_eq!(result[i], BaseElement::ZERO, "hash[{}] should copy for Nop", i - 3);
        }
    
    }
}
