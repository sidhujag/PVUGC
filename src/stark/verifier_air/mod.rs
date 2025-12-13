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

// Re-export common verification function for use by Aggregator
pub use prover::{append_proof_verification, append_proof_verification_with_options, VerificationResult};

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
    /// Expected number of verification checkpoints (SECURITY: enforces all steps run)
    /// 
    /// This must equal: 1 (OOD) + num_queries * (2 + 1 + num_fri_layers + terminal_checks)
    /// - 2 Merkle roots per query (trace + comp)
    /// - 1 DEEP verification per query
    /// - num_fri_layers FRI Merkle verifications per query
    /// - terminal_checks: 1 per query for FRI terminal
    pub expected_checkpoint_count: usize,
    /// Parameters digest binding the security-relevant STARK options of the proof being verified.
    ///
    /// Encoding (4 elements):
    /// - [0] = trace_len
    /// - [1] = lde_blowup
    /// - [2] = num_queries
    /// - [3] = (fri_folding_factor << 32) | grinding_factor
    pub params_digest: [BaseElement; 4],
    /// Expected mode counter
    /// 
    /// Packed encoding: statement_count + 4096 * params_count
    ///
    /// - statement_count is incremented on DeepCompose mode 4
    /// - params_count is incremented on DeepCompose mode 5
    ///
    /// For single proof: 1 + 4096*1 = 4097
    /// For multi-proof (N children): 1 + 4096*N
    pub expected_mode_counter: usize,
}

impl ToElements<BaseElement> for VerifierPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        // NOTE (Groth16 arming): downstream code expects `pub_inputs.len() >= 22`
        // so it can always include `stmt[0..4]` and the last 6 elements
        // (`expected_checkpoint_count`, `expected_mode_counter`, `params_digest[4]`).
        // When the verified proof has zero FRI layers, `fri_commitments` is empty and we'd end up
        // with only 18 elements. We pad to at least one commitment (4 elems) deterministically.
        let fri_commitments_len = self.fri_commitments.len().max(1);
        let mut elements = Vec::with_capacity(24 + fri_commitments_len * 4);
        elements.extend_from_slice(&self.statement_hash);
        elements.extend_from_slice(&self.trace_commitment);
        elements.extend_from_slice(&self.comp_commitment);
        for commit in &self.fri_commitments {
            elements.extend_from_slice(commit);
        }
        if self.fri_commitments.is_empty() {
            elements.extend_from_slice(&[BaseElement::ZERO; 4]);
        }
        elements.push(BaseElement::new(self.num_queries as u64));
        elements.push(BaseElement::new(self.proof_trace_len as u64));
        elements.push(self.g_trace);
        elements.push(self.pub_result);
        elements.push(BaseElement::new(self.expected_checkpoint_count as u64));
        elements.push(BaseElement::new(self.expected_mode_counter as u64));
        // Kept at end for Groth16 arming extraction.
        elements.extend_from_slice(&self.params_digest);
        elements
    }
}

impl VerifierPublicInputs {
    /// Compute expected checkpoint count from proof parameters
    /// 
    /// Formula: 1 (statement hash) + 1 (OOD) + num_queries * (2 + 1 + num_fri_layers + 1)
    /// - 1 statement hash verification (binds commitments to public inputs)
    /// - 1 OOD verification
    /// - 1 interpreter hash verification (binds formula to public inputs)
    /// - 2 Merkle roots per query (trace + comp)
    /// - 1 DEEP verification per query (if FRI layers exist)
    /// - num_fri_layers FRI Merkle verifications per query (if FRI layers exist)
    /// - 1 FRI terminal verification per query (if FRI layers exist)
    pub fn compute_expected_checkpoints(num_queries: usize, num_fri_layers: usize) -> usize {
        if num_fri_layers == 0 {
            // No FRI: statement hash + OOD + params digest + (trace + comp) Merkle per query
            3 + num_queries * 2
        } else {
            // With FRI: statement hash + OOD + params digest + (trace + comp + DEEP + FRI layers + terminal) per query
            3 + num_queries * (2 + 1 + num_fri_layers + 1)
        }
    }
    
    /// Compute expected mode counter from number of child proofs
    /// 
    /// Packed encoding: statement_count + 4096 * params_count
    /// - statement_count: always 1 (one combined statement hash verification)
    /// - params_count: number of child proofs whose options digest is checked (one per child proof)
    ///
    /// For single proof verification: 1 + 4096*1 = 4097
    /// For verifying aggregator (N children): 1 + 4096*N
    pub fn compute_expected_mode_counter(num_child_proofs: usize) -> usize {
        1 + num_child_proofs * 4096
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
        // For Permute: op.is_permute (deg 3) * sbox(candidate) - mid (deg 7)
        //   where candidate = inv_mds(next - ark2) and mid = mds(sbox(current)) + ark1
        //   Lagrange interpolation for ark1/ark2 adds degree 6 (product of 6 terms)
        //   Total: 3 + 7 + 6 = 16, but actual evaluation may simplify
        // With RPO verification: degree 45 (Lagrange*6 + S-box*7 + op_flag*3 ≈ 44)
        for _ in 0..HASH_STATE_WIDTH {
            degrees.push(TransitionConstraintDegree::new(45));
        }

        // FRI/DEEP working constraints (8):
        // Columns 0-3, 5, 7: copy constraint (both_not_special * copy)
        // Column 4: FRI folding (op.is_fri * fold + both_not_special * copy)
        // Column 6: OOD verification (op.is_deep * ood + both_not_special * copy)
        //
        // Degree analysis:
        // - op.is_X flags: degree 3 (product of 3 selector terms)
        // - both_not_special: For FRI column constraints, this involves selector products
        //   but the effective degree when combined with copy_constraint varies by trace
        // - copy_constraint: degree 1
        // - fri_fold_constraint: degree 1 (linear in trace)
        //
        // IMPORTANT: The declared degree must match what Winterfell computes from
        // the actual trace evaluation. For most FRI columns, degree 6 works.
        for i in 0..8 {
            if i == 4 {
                // FRI folding: op.is_fri(3)*fold(2) = degree 5
                // fri_fold_constraint has degree 2 (products like x*g, beta*f_x)
                // No copy constraint needed since column 4 only changes during FRI fold
                degrees.push(TransitionConstraintDegree::new(5));
            } else if i == 6 {
                // OOD constraint: op.is_deep(3) * aux_mode(1) * ood(1) + copy term
                // Degree: max(3+1+1, 6+1) = 7
                degrees.push(TransitionConstraintDegree::new(7));
            } else if i == 5 {
                // Column 5: unused (fri_state[5] always 0)
                // Constraint always evaluates to 0, declare degree 1 (minimum)
                degrees.push(TransitionConstraintDegree::new(1));
            } else if i == 7 {
                // Column 7: copy constraint only
                // both_not_special(6) * copy(1) = degree 7
                degrees.push(TransitionConstraintDegree::new(7));
            } else {
                // Columns 0-3: root/statement/interpreter check constraints
                // Root: op.is_deep(3) * is_root_check(6) * root(1) = degree 10
                // Statement: op.is_deep(3) * is_statement_check(6) * statement(1) = degree 10
                // Params: op.is_deep(3) * is_params_check(6) * params(1) = degree 10
                // Copy: both_not_special(6) * copy(1) = degree 7
                // Max = 10
                degrees.push(TransitionConstraintDegree::new(10));
            }
        }

        // Auxiliary constraints (4):
        // aux[0]: degree 10 (round counter range check: is_permute*prod(rc-i) for i in 0..7)
        // aux[1]: degree 8 (mode counter: is_deep * is_mode_4/5 normalized selectors)
        // aux[2]: mode value - unconstrained
        // aux[3]: degree 3 (checkpoint counter: aux_next - aux_curr - op.is_deep)
        for i in 0..4 {
            if i == 0 {
                // Round counter: max(is_permute*7-term-product, basic_ops*(rc-7))
                // = max(3+7, 3+1) = degree 10
                degrees.push(TransitionConstraintDegree::new(10));
            } else if i == 1 {
                // Mode counter: aux[1]_next = aux[1]_curr + is_deep * (is_mode_4 + is_mode_5 * 64)
                // is_deep = degree 3, is_mode_4/5 = degree 5
                // Total: 3 + 6 = degree 9
                degrees.push(TransitionConstraintDegree::new(9));
            } else if i == 3 {
                // Checkpoint counter: aux_next - aux_curr - op.is_deep
                // op.is_deep = s2 * s1 * (1 - s0) = degree 3
                degrees.push(TransitionConstraintDegree::new(3));
            } else {
                // aux[2]: mode value - unconstrained
                degrees.push(TransitionConstraintDegree::new(1));
            }
        }

        // Boundary assertions:
        // - 4 initial capacity zeros (columns 3-6)
        // - 1 initial aux[1] = 0 (mode counter)
        // - 1 initial aux[3] = 0 (checkpoint counter)
        // - 1 final aux[1] = expected_mode_counter
        // - 1 final aux[3] = expected_checkpoint_count
        // Total: 8
        let num_assertions = 8;

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

        // Initial mode counter must be 0
        // aux[1] is at column 24
        assertions.push(Assertion::single(
            24, // aux[1] = mode counter
            0,
            BaseElement::ZERO, // Starts at 0
        ));

        // Initial checkpoint counter must be 0
        // aux[3] is at column 26
        assertions.push(Assertion::single(
            26, // aux[3] = checkpoint counter
            0,
            BaseElement::ZERO, // Starts at 0
        ));

        let last_row = self.context.trace_len() - 1;
        
        // Final mode counter must equal expected value
        // Packed encoding: statement_count + 4096 * params_count
        // For single proof: 1 + 4096*1 = 4097
        // For multi-proof (N children): 1 + 4096*N
        assertions.push(Assertion::single(
            24, // aux[1] = mode counter
            last_row,
            BaseElement::new(self.pub_inputs.expected_mode_counter as u64),
        ));

        // Final checkpoint count must equal expected value
        // This ensures all verification steps were executed (not skipped).
        assertions.push(Assertion::single(
            26, // aux[3] = checkpoint counter
            last_row,
            BaseElement::new(self.pub_inputs.expected_checkpoint_count as u64),
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
            expected_checkpoint_count: VerifierPublicInputs::compute_expected_checkpoints(2, 2),
            params_digest: [BaseElement::ZERO; 4],
            expected_mode_counter: VerifierPublicInputs::compute_expected_mode_counter(1),
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
            expected_checkpoint_count: VerifierPublicInputs::compute_expected_checkpoints(2, 2),
            params_digest: [BaseElement::ZERO; 4],
            expected_mode_counter: VerifierPublicInputs::compute_expected_mode_counter(1),
        };

        let elements = pub_inputs.to_elements();
        // 4(stmt)+4(trace)+4(comp)+8(fri commitments)+6(meta)+4(params) = 30
        assert_eq!(elements.len(), 30);
    }
    
    #[test]
    fn test_compute_expected_checkpoints() {
        // With 2 queries and 3 FRI layers:
        // - 1 statement hash verification
        // - 1 OOD verification  
        // - 1 interpreter hash verification
        // - 1 params digest verification
        // - 2 queries * (2 Merkle roots + 1 DEEP + 3 FRI Merkle + 1 terminal) = 2 * 7 = 14
        // Total: 4 + 14 = 18
        assert_eq!(VerifierPublicInputs::compute_expected_checkpoints(2, 3), 18);

        // With 4 queries and 0 FRI layers:
        // - 1 statement hash + 1 OOD + 1 interpreter hash + 1 params digest = 4
        // - 4 queries * 2 (trace + comp Merkle only, no DEEP/terminal) = 8
        // Total: 12
        assert_eq!(VerifierPublicInputs::compute_expected_checkpoints(4, 0), 12);
        
        // With 2 queries and 0 FRI layers:
        // - 4 + 2 * 2 = 8
        assert_eq!(VerifierPublicInputs::compute_expected_checkpoints(2, 0), 8);
    }
}
