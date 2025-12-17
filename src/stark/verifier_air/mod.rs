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
/// - 1 dedicated index register column (`IDX_REG`, persistent query slot index Q_IDX)
/// - 4 expected-root register columns (loaded from public inputs; used by root checks)
/// - 1 QueryGen step-counter column (`QGEN_CTR`, enforces microprogram sequencing)
/// - 1 root-kind selector column
/// - 8 carry/register columns (cross-op binding; always copied unless explicitly updated)
/// - 4 auxiliary columns
pub const VERIFIER_TRACE_WIDTH: usize = 42;

/// Transition-constraint base degrees for `VerifierAir` / verifier-style AIRs.
///
/// IMPORTANT: this array is ordered by the **constraint emission order** in
/// `crate::stark::verifier_air::constraints::evaluate_all()` (i.e. “constraint #i”),
/// NOT by the **trace column index layout** (`IDX_REG`, `ROOT_REG_START`, `QGEN_CTR`, ...).
/// Thus it is normal that degrees for `IDX_REG` and `QGEN_CTR` constraints are adjacent here,
/// even though the `ROOT_REG[0..3]` columns sit between them in the trace.
///
/// Winterfell validates these degrees against the compiled evaluator; if constraint logic changes,
/// this table must be updated to match.
pub(crate) const VERIFIER_TRANSITION_DEGREE_BASES: [usize; VERIFIER_TRACE_WIDTH] = [
    // selectors (3)
    2, 2, 2,
    // hash state (12)
    45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45, 45,
    // fri/deep working (8)
    23, 23, 23, 23, 23, 23, 23, 23,
    // idx_reg (1), qgen_ctr (1)
    32, 33,
    // root_reg[0..3] (4)
    41, 40, 40, 40,
    // root_kind (1)
    8,
    // carry[0..7] (8)
    17, 16, 1, 18, 18, 32, 16, 4,
    // aux[0..3] (4)
    10, 9, 17, 3,
];

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
    /// Packed encoding:
    ///   statement_count
    /// + 4096 * params_count
    /// + 65536 * fri_link_count
    /// + 2^32 * root_count
    ///
    /// - root_count is incremented on DeepCompose mode 0 (Merkle root checks)
    /// - statement_count is incremented on DeepCompose mode 4
    /// - params_count is incremented on DeepCompose mode 5
    ///
    /// For single proof: (roots<<32) + 1 + 4096*1
    /// For multi-proof (N children): (roots<<32) + 1 + 4096*N
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
    /// Reconstruct `VerifierPublicInputs` from the exact `to_elements()` layout.
    ///
    /// This is used by the recursive verifier to evaluate verifier-style constraints at the OOD point.
    /// It must stay in sync with `VerifierPublicInputs::to_elements()`.
    pub fn from_elements_exact(elems: &[BaseElement]) -> Self {
        assert!(
            elems.len() >= 22 && (elems.len() - 22) % 4 == 0,
            "invalid VerifierPublicInputs element length: {}",
            elems.len()
        );

        let fri_len = (elems.len() - 22) / 4;
        assert!(fri_len >= 1, "expected at least 1 FRI commitment (padding included)");

        let mut statement_hash = [BaseElement::ZERO; 4];
        statement_hash.copy_from_slice(&elems[0..4]);
        let mut trace_commitment = [BaseElement::ZERO; 4];
        trace_commitment.copy_from_slice(&elems[4..8]);
        let mut comp_commitment = [BaseElement::ZERO; 4];
        comp_commitment.copy_from_slice(&elems[8..12]);

        let mut fri_commitments = Vec::with_capacity(fri_len);
        for i in 0..fri_len {
            let start = 12 + 4 * i;
            let mut d = [BaseElement::ZERO; 4];
            d.copy_from_slice(&elems[start..start + 4]);
            fri_commitments.push(d);
        }

        let tail = 12 + 4 * fri_len;
        let num_queries = elems[tail + 0].as_int() as usize;
        let proof_trace_len = elems[tail + 1].as_int() as usize;
        let g_trace = elems[tail + 2];
        let pub_result = elems[tail + 3];
        let expected_checkpoint_count = elems[tail + 4].as_int() as usize;
        let expected_mode_counter = elems[tail + 5].as_int() as usize;

        let mut params_digest = [BaseElement::ZERO; 4];
        params_digest.copy_from_slice(&elems[tail + 6..tail + 10]);

        Self {
            statement_hash,
            trace_commitment,
            comp_commitment,
            fri_commitments,
            num_queries,
            proof_trace_len,
            g_trace,
            pub_result,
            expected_checkpoint_count,
            params_digest,
            expected_mode_counter,
        }
    }

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
            // With FRI:
            // - 3 global checkpoints: statement-hash + OOD + params-digest
            // - per query:
            //   - 2 Merkle roots (trace + comp)
            //   - 1 DEEP check
            //   - num_fri_layers Merkle roots (FRI layers)
            //   - 1 terminal check
            //   - (num_fri_layers - 1) inter-layer link checks
            3 + num_queries * (2 + 1 + num_fri_layers + 1) + num_queries * num_fri_layers.saturating_sub(1)
        }
    }
    
    /// Compute expected mode counter from number of child proofs
    /// 
    /// Packed encoding: statement_count + 4096 * params_count + 2^32 * root_count
    /// - statement_count: always 1 (one combined statement hash verification)
    /// - params_count: number of child proofs whose options digest is checked (one per child proof)
    /// - root_count: number of Merkle root checks (trace + comp + FRI layers) across all queries
    /// 
    /// For single proof verification: (roots<<32) + 1 + 4096*1
    pub fn compute_expected_mode_counter(
        num_child_proofs: usize,
        num_queries: usize,
        num_fri_layers: usize,
    ) -> usize {
        let root_count = num_queries * (2 + num_fri_layers);
        let fri_link_count = num_queries * num_fri_layers.saturating_sub(1);
        (root_count << 32) + 1 + num_child_proofs * 4096 + fri_link_count * 65536
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
        let degrees: Vec<TransitionConstraintDegree> = VERIFIER_TRANSITION_DEGREE_BASES
            .iter()
            .map(|&d| TransitionConstraintDegree::new(d))
            .collect();
        debug_assert_eq!(degrees.len(), VERIFIER_TRACE_WIDTH);

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
        assertions.push(Assertion::single(
            constraints::AUX_START + 1, // aux[1] = mode counter
            0,
            BaseElement::ZERO, // Starts at 0
        ));

        // Initial checkpoint counter must be 0
        assertions.push(Assertion::single(
            constraints::AUX_START + 3, // aux[3] = checkpoint counter
            0,
            BaseElement::ZERO, // Starts at 0
        ));

        let last_row = self.context.trace_len() - 1;
        
        // Final mode counter must equal expected value
        // Packed encoding: statement_count + 4096 * params_count
        // For single proof: 1 + 4096*1 = 4097
        // For multi-proof (N children): 1 + 4096*N
        assertions.push(Assertion::single(
            constraints::AUX_START + 1, // aux[1] = mode counter
            last_row,
            BaseElement::new(self.pub_inputs.expected_mode_counter as u64),
        ));

        // Final checkpoint count must equal expected value
        // This ensures all verification steps were executed (not skipped).
        assertions.push(Assertion::single(
            constraints::AUX_START + 3, // aux[3] = checkpoint counter
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
            expected_mode_counter: VerifierPublicInputs::compute_expected_mode_counter(1, 2, 2),
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
            expected_mode_counter: VerifierPublicInputs::compute_expected_mode_counter(1, 2, 2),
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
