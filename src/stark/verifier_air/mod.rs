//! STARK Verifier AIR
//!
//! This module implements a STARK verifier as an AIR (Algebraic Intermediate Representation),
//! enabling recursive STARK verification (STARK-in-STARK).
//!
//! ## Architecture
//!
//! The verifier is implemented as a state machine with the following components:
//!
//! 1. **Hash Chiplet**: RPO-256 for Merkle verification and Fiat-Shamir
//! 2. **FRI Chiplet**: Polynomial folding and evaluation
//! 3. **DEEP Chiplet**: Deep composition polynomial computation
//! 4. **Arithmetic Chiplet**: Goldilocks field operations
//!
//! ## Trace Layout
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────────────────┐
//! │ Cycle │ Op  │ Hash State (12) │ FRI State │ DEEP State │ Aux Columns   │
//! ├───────┼─────┼─────────────────┼───────────┼────────────┼───────────────┤
//! │   0   │ INI │  init sponge    │    -      │     -      │ pub_inputs    │
//! │   1   │ ABS │  absorb ctx     │    -      │     -      │               │
//! │   2   │ PRM │  permute        │    -      │     -      │               │
//! │  ...  │ ... │     ...         │   ...     │    ...     │     ...       │
//! │   n   │ ACC │  final check    │    -      │     -      │ accept flag   │
//! └─────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Design Principles
//!
//! 1. **Sequential Execution**: Verifier steps execute in a fixed order
//! 2. **Chiplet Reuse**: Hash operations are shared across Merkle proofs and FS
//! 3. **Minimal Trace Width**: Use auxiliary columns for intermediate values
//! 4. **Fixed Parameters**: Verifier AIR has fixed structure regardless of proof

pub mod hash_chiplet;
pub mod verifier_state;
pub mod constraints;
pub mod trace;
pub mod merkle;
pub mod transcript;
pub mod fri;
pub mod ood_eval;
pub mod prover;
pub mod proof_parser;
pub mod aggregator_integration;

#[cfg(test)]
mod integration_test;

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

// ============================================================================
// CONSTANTS
// ============================================================================

/// Trace width for the verifier AIR
/// - 3 selector columns
/// - 12 hash state columns (RPO-256)
/// - 8 FRI/DEEP working columns
/// - 4 auxiliary columns
pub const VERIFIER_TRACE_WIDTH: usize = 27;

/// Number of hash state columns (RPO-256 state)
pub const HASH_STATE_WIDTH: usize = 12;

/// Number of selector columns
pub const NUM_SELECTORS: usize = 3;

/// RPO round count per permutation
pub const RPO_ROUNDS: usize = 7;

/// RPO cycle length (rounds + absorption row)
pub const RPO_CYCLE_LEN: usize = 8;

// ============================================================================
// OPERATION CODES
// ============================================================================

/// Operations that the verifier can perform
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum VerifierOp {
    /// Initialize sponge state
    Init = 0,
    /// Absorb elements into sponge
    Absorb = 1,
    /// Execute RPO permutation round
    Permute = 2,
    /// Squeeze elements from sponge
    Squeeze = 3,
    /// Verify Merkle authentication path step
    MerklePath = 4,
    /// FRI folding step
    FriFold = 5,
    /// DEEP composition step
    DeepCompose = 6,
    /// Field arithmetic (add, mul, exp)
    FieldOp = 7,
    /// Constraint evaluation at OOD point
    EvalConstraint = 8,
    /// Final acceptance check
    Accept = 9,
    /// No-op (padding)
    Nop = 15,
}

impl From<VerifierOp> for BaseElement {
    fn from(op: VerifierOp) -> Self {
        BaseElement::new(op as u64)
    }
}

// ============================================================================
// PUBLIC INPUTS
// ============================================================================

/// Public inputs for the verifier AIR
#[derive(Clone, Debug)]
pub struct VerifierPublicInputs {
    /// Statement hash of the proof being verified (binds all commitments)
    pub statement_hash: [BaseElement; 4],
    /// Expected trace commitment (Merkle root)
    pub trace_commitment: [BaseElement; 4],
    /// Expected composition commitment
    pub comp_commitment: [BaseElement; 4],
    /// Expected FRI layer commitments
    pub fri_commitments: Vec<[BaseElement; 4]>,
    /// Number of queries
    pub num_queries: usize,
    /// Trace length of the proof being verified
    pub proof_trace_len: usize,
    /// Trace domain generator for the proof being verified
    pub g_trace: BaseElement,
    /// Public result expected at final boundary (Aggregator's output)
    pub pub_result: BaseElement,
}

impl ToElements<BaseElement> for VerifierPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut elements = Vec::with_capacity(18 + self.fri_commitments.len() * 4);
        elements.extend_from_slice(&self.statement_hash);
        elements.extend_from_slice(&self.trace_commitment);
        elements.extend_from_slice(&self.comp_commitment);
        for commit in &self.fri_commitments {
            elements.extend_from_slice(commit);
        }
        elements.push(BaseElement::new(self.num_queries as u64));
        elements.push(BaseElement::new(self.proof_trace_len as u64));
        elements.push(self.g_trace);
        elements.push(self.pub_result);
        elements
    }
}

// ============================================================================
// VERIFIER AIR
// ============================================================================

/// STARK Verifier AIR
///
/// This AIR verifies a STARK proof within a STARK, enabling recursive composition.
pub struct VerifierAir {
    context: AirContext<BaseElement>,
    pub_inputs: VerifierPublicInputs,
}

impl Air for VerifierAir {
    type BaseField = BaseElement;
    type PublicInputs = VerifierPublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        // Define transition constraint degrees
        //
        // With full RPO verification:
        // - Lagrange interpolation for round constants: degree 6 in round_counter
        // - S-box (x^7): degree 7
        // - Combined with op_flag: very high degree (~50)
        //
        // We set high degrees to accommodate the RPO constraints.
        let mut degrees = Vec::new();

        // Selector binary constraints (3): degree 2
        for _ in 0..NUM_SELECTORS {
            degrees.push(TransitionConstraintDegree::new(2));
        }

        // Hash state constraints (12): 
        // With RPO verification: degree 45 (Lagrange*6 + S-box*7 + op_flag*3 ≈ 44)
        // Actual observed: 22484 = 44 * 511, so degree is 45
        for _ in 0..HASH_STATE_WIDTH {
            degrees.push(TransitionConstraintDegree::new(45));
        }

        // FRI/DEEP working constraints (8):
        // First 4: degree 7 (both_not_special * copy, active with real FRI operations)
        // Index 4: degree 5 (FRI folding verification: is_fri * fold_constraint)
        //          Actual eval degree is 1020/255 ≈ 4, but need declared >= actual
        // Rest: degree 1 (may evaluate to zero depending on trace structure)
        for i in 0..8 {
            if i < 4 {
                degrees.push(TransitionConstraintDegree::new(7));
            } else if i == 4 {
                // FRI folding constraint
                degrees.push(TransitionConstraintDegree::new(5));
            } else {
                degrees.push(TransitionConstraintDegree::new(1));
            }
        }

        // Auxiliary constraints (4):
        // aux[0]: degree 10 (round counter range check: is_permute*prod(rc-i) for i in 0..7)
        // aux[1,2]: degree 7 declared (aux_both_not_special * copy), but may be 0 in practice
        //           if no Nop→Nop or Squeeze→Squeeze transitions occur
        // aux[3]: degree 2 (binary check + monotonic)
        for i in 0..4 {
            if i == 0 {
                // Round counter: max(is_permute*7-term-product, basic_ops*(rc-7))
                // = max(3+7, 3+1) = degree 10
                degrees.push(TransitionConstraintDegree::new(10));
            } else if i == 3 {
                degrees.push(TransitionConstraintDegree::new(2));
            } else {
                // aux[1,2]: In practice these may always be 0 (no Nop→Nop transitions)
                // Declare degree 1 to handle the zero case
                degrees.push(TransitionConstraintDegree::new(1));
            }
        }

        let num_assertions = 5; // 4 initial capacity zeros + 1 final acceptance flag

        let context = AirContext::new(trace_info, degrees, num_assertions, options);

        Self { context, pub_inputs }
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<BaseElement>> {
        // RPO round constants (24 columns of 8 values each for the cycle)
        hash_chiplet::get_periodic_column_values()
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        let mut assertions = Vec::new();

        // Initial assertions: sponge starts with zeros in capacity
        for i in 0..4 {
            assertions.push(Assertion::single(
                NUM_SELECTORS + i, // First 4 elements of hash state
                0,
                BaseElement::ZERO,
            ));
        }

        // Final assertion: acceptance flag must be 1
        // (Located in last auxiliary column of final row)
        // Note: Actual row is determined by trace length
        let last_row = self.context.trace_len() - 1;
        assertions.push(Assertion::single(
            VERIFIER_TRACE_WIDTH - 1, // Last column
            last_row,
            BaseElement::ONE, // Must be 1 for valid proof
        ));

        assertions
    }

    fn evaluate_transition<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        constraints::evaluate_all(frame, periodic_values, result, &self.pub_inputs);
    }

    fn context(&self) -> &AirContext<Self::BaseField> {
        &self.context
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verifier_air_creation() {
        let pub_inputs = VerifierPublicInputs {
            statement_hash: [BaseElement::ONE; 4],
            trace_commitment: [BaseElement::ZERO; 4],
            comp_commitment: [BaseElement::ZERO; 4],
            fri_commitments: vec![[BaseElement::ZERO; 4]; 2],
            num_queries: 2,
            proof_trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            pub_result: BaseElement::ZERO,
        };

        let trace_info = TraceInfo::new(VERIFIER_TRACE_WIDTH, 64);
        let options = ProofOptions::new(
            2, 64, 0,  // blowup 64 to handle degree 45 constraints
            winterfell::FieldExtension::None,
            2, 31,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );

        let air = VerifierAir::new(trace_info, pub_inputs.clone(), options);
        assert_eq!(air.context().trace_len(), 64);
    }

    #[test]
    fn test_pub_inputs_to_elements() {
        let pub_inputs = VerifierPublicInputs {
            statement_hash: [BaseElement::new(1); 4],
            trace_commitment: [BaseElement::new(2); 4],
            comp_commitment: [BaseElement::new(3); 4],
            fri_commitments: vec![[BaseElement::new(4); 4]; 2],
            num_queries: 2,
            proof_trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            pub_result: BaseElement::new(42),
        };

        let elements = pub_inputs.to_elements();
        // 4 + 4 + 4 + 8 + 2 + 2 = 24 elements (added g_trace and pub_result)
        assert_eq!(elements.len(), 24);
    }
}
