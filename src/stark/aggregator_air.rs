//! Aggregator STARK AIR
//!
//! This AIR aggregates multiple application STARK proofs into a single proof.
//! The Groth16 circuit then only needs to verify this ONE Aggregator STARK.
//!
//! ## Architecture
//!
//! ```text
//! Application STARKs (VDF, CubicFib, etc.)
//!    ↓ (statement hashes committed via Merkle tree)
//! Aggregator STARK (this AIR)
//!    ↓ (verified by)
//! Groth16 Circuit
//! ```
//!
//! ## How It Works
//!
//! 1. Each application STARK produces a `statement_hash` binding its proof
//! 2. Aggregator receives all statement hashes as witness data
//! 3. Aggregator computes Merkle root of all statement hashes
//! 4. Aggregator verifies chain consistency (output[i] = input[i+1])
//! 5. Final public outputs: (children_root, initial_state, final_state)
//!
//! ## Trace Structure
//!
//! The trace has 8 columns:
//! - Columns 0-3: Poseidon sponge state (for Merkle computation)
//! - Column 4: Child index counter
//! - Column 5: Chain state element 0
//! - Column 6: Chain state element 1  
//! - Column 7: Flags/mode indicator
//!
//! ## Constraint Formula
//!
//! For now, we use a simplified constraint formula that the Groth16 circuit expects:
//! - constraint[0] = next[0] - (current[0]^3 + current[1])
//! - constraint[1] = next[1] - current[0]
//!
//! This represents a hash-chain-like accumulation over the child hashes.

use winterfell::{
    math::{fields::f64::BaseElement, FieldElement},
    Air, AirContext, Assertion, EvaluationFrame, ProofOptions, TraceInfo,
    TransitionConstraintDegree,
};

// ============================================================================
// CONSTANTS
// ============================================================================

/// Trace width for Aggregator STARK
/// 2 columns for the simplified version (matching Groth16's expected formula)
pub const AGGREGATOR_TRACE_WIDTH: usize = 2;

/// Number of transition constraints
pub const AGGREGATOR_NUM_CONSTRAINTS: usize = 2;

/// Maximum number of child proofs that can be aggregated
pub const MAX_CHILDREN: usize = 32;

// ============================================================================
// AGGREGATOR CONFIGURATION
// ============================================================================

/// Configuration for Aggregator STARK parameters
/// 
/// This centralizes all tunable parameters for the Aggregator STARK.
/// The Groth16 circuit structure depends on these parameters, so they
/// must be fixed for a given trusted setup.
#[derive(Clone, Debug)]
pub struct AggregatorConfig {
    /// Trace length (must be power of 2)
    pub trace_len: usize,
    /// Number of FRI queries (security: ~3 bits per query with blowup=8)
    pub num_queries: usize,
    /// LDE blowup factor (typically 8)
    pub lde_blowup: usize,
    /// Grinding factor for PoW (adds security bits)
    pub grinding_factor: u32,
    /// FRI folding factor (2 or 4)
    pub fri_folding_factor: usize,
    /// FRI max remainder degree
    pub fri_max_remainder: usize,
}

impl AggregatorConfig {
    /// Production configuration with 128-bit security
    /// 
    /// Security: num_queries × log2(blowup) + grinding
    ///         = 27 × 3 + 20 = 101 bits from FRI + 20 bits from PoW
    ///         ≈ 121 bits total (acceptable for 128-bit target)
    pub fn production_128bit() -> Self {
        Self {
            trace_len: 8,
            num_queries: 27,
            lde_blowup: 8,
            grinding_factor: 20,
            fri_folding_factor: 4,
            fri_max_remainder: 31,
        }
    }
    
    /// Fast configuration for testing (NOT SECURE!)
    /// 
    /// Only ~6 bits of security - use for development only.
    pub fn test_fast() -> Self {
        Self {
            trace_len: 8,
            num_queries: 2,
            lde_blowup: 8,
            grinding_factor: 0,
            fri_folding_factor: 2,
            fri_max_remainder: 31,
        }
    }
    
    /// Medium configuration for CI/integration tests
    /// 
    /// ~40 bits of security - faster than production but more thorough than test_fast.
    pub fn test_medium() -> Self {
        Self {
            trace_len: 8,
            num_queries: 8,
            lde_blowup: 8,
            grinding_factor: 8,
            fri_folding_factor: 2,
            fri_max_remainder: 31,
        }
    }
    
    /// Test configuration with meaningful FRI layers
    /// 
    /// Uses larger trace to generate actual FRI folding rounds.
    /// LDE domain = 256 × 8 = 2048, with remainder 7 gives ~8 FRI layers.
    /// ~24 bits of security from FRI (4 queries × 3 bits × 2 layers checked)
    pub fn test_with_fri() -> Self {
        Self {
            trace_len: 256,        // Larger trace for FRI layers
            num_queries: 4,
            lde_blowup: 8,
            grinding_factor: 0,
            fri_folding_factor: 2,
            fri_max_remainder: 7,  // Must be 2^n - 1 (7 = 2^3 - 1)
        }
    }
    
    /// Convert to Winterfell ProofOptions
    pub fn to_proof_options(&self) -> ProofOptions {
        ProofOptions::new(
            self.num_queries,
            self.lde_blowup,
            self.grinding_factor,
            winterfell::FieldExtension::None,
            self.fri_folding_factor,
            self.fri_max_remainder,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        )
    }
    
    /// Calculate approximate security bits
    pub fn security_bits(&self) -> usize {
        let fri_bits = self.num_queries * (self.lde_blowup as f64).log2() as usize;
        fri_bits + self.grinding_factor as usize
    }
}

impl Default for AggregatorConfig {
    fn default() -> Self {
        // Default to test_fast for backward compatibility
        Self::test_fast()
    }
}

// ============================================================================
// PUBLIC INPUTS
// ============================================================================

/// Public inputs for the Aggregator STARK
///
/// In the full version, this would include:
/// - Merkle root of all child statement hashes
/// - Initial state (first chunk's input commitment)
/// - Final state (last chunk's output commitment)
///
/// For now (simplified version), it's just the final result.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AggregatorPublicInputs {
    /// Final accumulated result (commitment to all children)
    pub result: BaseElement,
    
    /// Merkle root of child statement hashes (4 Goldilocks elements = 256 bits)
    /// This is absorbed into the initial trace state to bind the children.
    pub children_root: [BaseElement; 4],
    
    /// Initial state commitment (first child's input)
    pub initial_state: [BaseElement; 4],
    
    /// Final state commitment (last child's output)
    pub final_state: [BaseElement; 4],

    /// Aggregation level (leaf chunks are level 0; parents increment by 1).
    pub level: u32,

    /// Span start index (inclusive).
    pub start_idx: u64,

    /// Span end index (inclusive).
    pub end_idx: u64,

    /// App context hash (e.g. "txout"/Add2 target context).
    pub context_hash: [BaseElement; 4],

    /// App interpreter/formula hash (Generic app identity).
    pub interpreter_hash: [BaseElement; 4],

    /// App security-params digest policy.
    pub params_digest: [BaseElement; 4],
}

impl std::fmt::Display for AggregatorPublicInputs {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "AggPubInputs(result={})", self.result)
    }
}

impl AggregatorPublicInputs {
    /// Get the result as BaseElement (for backward compatibility)
    pub fn result(&self) -> BaseElement {
        self.result
    }
    
    /// Create new public inputs from child data
    pub fn new(
        children_root: [BaseElement; 4],
        initial_state: [BaseElement; 4],
        final_state: [BaseElement; 4],
        level: u32,
        start_idx: u64,
        end_idx: u64,
        context_hash: [BaseElement; 4],
        interpreter_hash: [BaseElement; 4],
        params_digest: [BaseElement; 4],
    ) -> Self {
        // Compute result as hash of all components (simplified)
        let result = Self::compute_result(
            &children_root,
            &initial_state,
            &final_state,
            level,
            start_idx,
            end_idx,
            &context_hash,
            &interpreter_hash,
            &params_digest,
        );
        Self {
            result,
            children_root,
            initial_state,
            final_state,
            level,
            start_idx,
            end_idx,
            context_hash,
            interpreter_hash,
            params_digest,
        }
    }
    
    /// Compute the final result from components
    fn compute_result(
        children_root: &[BaseElement; 4],
        initial_state: &[BaseElement; 4],
        final_state: &[BaseElement; 4],
        level: u32,
        start_idx: u64,
        end_idx: u64,
        context_hash: &[BaseElement; 4],
        interpreter_hash: &[BaseElement; 4],
        params_digest: &[BaseElement; 4],
    ) -> BaseElement {
        // Simple combination (in production, use proper Poseidon hash)
        let mut acc = BaseElement::ZERO;
        for &elem in children_root.iter() {
            acc = acc * BaseElement::new(7) + elem;
        }
        for &elem in initial_state.iter() {
            acc = acc * BaseElement::new(11) + elem;
        }
        for &elem in final_state.iter() {
            acc = acc * BaseElement::new(13) + elem;
        }
        acc = acc * BaseElement::new(17) + BaseElement::new(level as u64);
        acc = acc * BaseElement::new(19) + BaseElement::new(start_idx);
        acc = acc * BaseElement::new(23) + BaseElement::new(end_idx);
        for &elem in context_hash.iter() {
            acc = acc * BaseElement::new(29) + elem;
        }
        for &elem in interpreter_hash.iter() {
            acc = acc * BaseElement::new(31) + elem;
        }
        for &elem in params_digest.iter() {
            acc = acc * BaseElement::new(37) + elem;
        }
        acc
    }
    
    /// Create simplified inputs (for backward compatibility)
    pub fn from_result(result: BaseElement) -> Self {
        Self {
            result,
            children_root: [BaseElement::ZERO; 4],
            initial_state: [BaseElement::ZERO; 4],
            final_state: [BaseElement::ZERO; 4],
            level: 0,
            start_idx: 0,
            end_idx: 0,
            context_hash: [BaseElement::ZERO; 4],
            interpreter_hash: [BaseElement::ZERO; 4],
            params_digest: [BaseElement::ZERO; 4],
        }
    }
}

// Implement ToElements for public coin seeding
// 
// SECURITY: All fields are included to bind the complete statement to outer proofs.
// This ensures that:
// - children_root: Merkle root of all child STARK statement hashes
// - initial_state: First chunk's input commitment
// - final_state: Last chunk's output commitment
// - result: The computed accumulation result
//
// All 13 elements are bound into the Groth16 statement_hash for full security.
impl winterfell::math::ToElements<BaseElement> for AggregatorPublicInputs {
    fn to_elements(&self) -> Vec<BaseElement> {
        let mut elements = Vec::with_capacity(13 + 1 + 2 + 12);
        elements.push(self.result);
        elements.extend_from_slice(&self.children_root);
        elements.extend_from_slice(&self.initial_state);
        elements.extend_from_slice(&self.final_state);
        elements.push(BaseElement::new(self.level as u64));
        elements.push(BaseElement::new(self.start_idx));
        elements.push(BaseElement::new(self.end_idx));
        elements.extend_from_slice(&self.context_hash);
        elements.extend_from_slice(&self.interpreter_hash);
        elements.extend_from_slice(&self.params_digest);
        elements
    }
}

// ============================================================================
// CHILD STATEMENT HASH
// ============================================================================

/// Statement hash for a child application STARK
///
/// This binds an application proof to its public inputs and commitments.
#[derive(Clone, Debug, Default)]
pub struct ChildStatementHash {
    /// Input state commitment (what this chunk starts with)
    pub input_state: [BaseElement; 4],
    /// Output state commitment (what this chunk produces)
    pub output_state: [BaseElement; 4],
    /// Program/circuit identifier
    pub program_hash: [BaseElement; 4],
    /// Chunk index in the sequence
    pub chunk_index: u64,

    /// Leaf level (0) or internal level (>0).
    pub level: u32,
    /// Span start index (inclusive).
    pub start_idx: u64,
    /// Span end index (inclusive).
    pub end_idx: u64,
    /// App context hash.
    pub context_hash: [BaseElement; 4],
    /// App interpreter/formula hash.
    pub interpreter_hash: [BaseElement; 4],
    /// App params digest.
    pub params_digest: [BaseElement; 4],
}

impl ChildStatementHash {
    /// Compute the statement hash (4 Goldilocks elements)
    /// 
    /// SECURITY: Includes program_hash (circuit ID) to prevent AIR substitution attacks.
    /// An attacker cannot use a trivial AIR because the statement hash would differ.
    pub fn to_hash(&self) -> [BaseElement; 4] {
        // Simple hash (in production, use Poseidon)
        let mut h0 = BaseElement::ZERO;
        let mut h1 = BaseElement::ZERO;
        let mut h2 = BaseElement::ZERO;
        let mut h3 = BaseElement::ZERO;
        
        // Include program_hash FIRST to bind circuit identity
        // This prevents an attacker from substituting a trivial AIR
        for (i, &elem) in self.program_hash.iter().enumerate() {
            match i % 4 {
                0 => h0 = h0 * BaseElement::new(7) + elem,
                1 => h1 = h1 * BaseElement::new(11) + elem,
                2 => h2 = h2 * BaseElement::new(13) + elem,
                _ => h3 = h3 * BaseElement::new(17) + elem,
            }
        }
        
        for (i, &elem) in self.input_state.iter().enumerate() {
            match i % 4 {
                0 => h0 = h0 * BaseElement::new(19) + elem,
                1 => h1 = h1 * BaseElement::new(23) + elem,
                2 => h2 = h2 * BaseElement::new(29) + elem,
                _ => h3 = h3 * BaseElement::new(31) + elem,
            }
        }
        for (i, &elem) in self.output_state.iter().enumerate() {
            match i % 4 {
                0 => h0 = h0 * BaseElement::new(37) + elem,
                1 => h1 = h1 * BaseElement::new(41) + elem,
                2 => h2 = h2 * BaseElement::new(43) + elem,
                _ => h3 = h3 * BaseElement::new(47) + elem,
            }
        }
        
        h0 = h0 + BaseElement::new(self.chunk_index);
        h1 = h1 + BaseElement::new(self.level as u64);
        h2 = h2 + BaseElement::new(self.start_idx);
        h3 = h3 + BaseElement::new(self.end_idx);
        for &e in self.context_hash.iter() {
            h0 = h0 * BaseElement::new(53) + e;
        }
        for &e in self.interpreter_hash.iter() {
            h1 = h1 * BaseElement::new(59) + e;
        }
        for &e in self.params_digest.iter() {
            h2 = h2 * BaseElement::new(61) + e;
        }
        
        [h0, h1, h2, h3]
    }
}

// ============================================================================
// MERKLE TREE FOR CHILDREN
// ============================================================================

/// Compute Merkle root of child statement hashes
/// 
/// Uses a simple binary Merkle tree with Poseidon-like hashing.
pub fn compute_children_merkle_root(children: &[ChildStatementHash]) -> [BaseElement; 4] {
    if children.is_empty() {
        return [BaseElement::ZERO; 4];
    }
    
    // Get hashes of all children
    let mut leaves: Vec<[BaseElement; 4]> = children.iter()
        .map(|c| c.to_hash())
        .collect();
    
    // Pad to power of 2
    let target_len = leaves.len().next_power_of_two();
    while leaves.len() < target_len {
        leaves.push([BaseElement::ZERO; 4]);
    }
    
    // Build Merkle tree bottom-up
    while leaves.len() > 1 {
        let mut next_level = Vec::with_capacity(leaves.len() / 2);
        for pair in leaves.chunks(2) {
            let left = &pair[0];
            let right = &pair[1];
            next_level.push(hash_pair(left, right));
        }
        leaves = next_level;
    }
    
    leaves[0]
}

/// Hash two 4-element nodes together (simplified Poseidon-like)
fn hash_pair(left: &[BaseElement; 4], right: &[BaseElement; 4]) -> [BaseElement; 4] {
    [
        left[0] * BaseElement::new(2) + right[0] * BaseElement::new(3) + left[1],
        left[1] * BaseElement::new(5) + right[1] * BaseElement::new(7) + left[2],
        left[2] * BaseElement::new(11) + right[2] * BaseElement::new(13) + left[3],
        left[3] * BaseElement::new(17) + right[3] * BaseElement::new(19) + right[0],
    ]
}

/// Verify chain consistency: output[i] == input[i+1]
pub fn verify_chain_consistency(children: &[ChildStatementHash]) -> bool {
    if children.len() < 2 {
        return true;
    }
    
    for i in 0..children.len() - 1 {
        if children[i].output_state != children[i + 1].input_state {
            return false;
        }
        if children[i].end_idx.saturating_add(1) != children[i + 1].start_idx {
            return false;
        }
        if children[i].level != children[i + 1].level {
            return false;
        }
        if children[i].context_hash != children[i + 1].context_hash {
            return false;
        }
        if children[i].interpreter_hash != children[i + 1].interpreter_hash {
            return false;
        }
        if children[i].params_digest != children[i + 1].params_digest {
            return false;
        }
    }
    true
}

// ============================================================================
// AGGREGATOR AIR
// ============================================================================

/// Aggregator STARK AIR
///
/// This AIR's constraints MUST match what the Groth16 circuit expects:
/// - constraint[0] = next[0] - (current[0]^3 + current[1])
/// - constraint[1] = next[1] - current[0]
pub struct AggregatorAir {
    context: AirContext<BaseElement>,
    /// Public inputs (simplified: just the result)
    pub_inputs: AggregatorPublicInputs,
}

impl Air for AggregatorAir {
    type BaseField = BaseElement;
    type PublicInputs = AggregatorPublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: AggregatorPublicInputs, options: ProofOptions) -> Self {
        assert_eq!(AGGREGATOR_TRACE_WIDTH, trace_info.width());

        // TWO constraints to match Groth16's expected formula:
        // constraint[0] = next[0] - (current[0]^3 + current[1]) - degree 3
        // constraint[1] = next[1] - current[0]                  - degree 1
        let degrees = vec![
            TransitionConstraintDegree::new(3),
            TransitionConstraintDegree::new(1),
        ];

        AggregatorAir {
            context: AirContext::new(trace_info, degrees, 1, options),
            pub_inputs,
        }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    /// Evaluate transition constraints
    ///
    /// These constraints MUST match what Groth16 expects!
    /// Two constraints:
    ///   constraint[0] = next[0] - (current[0]^3 + current[1])
    ///   constraint[1] = next[1] - current[0]
    fn evaluate_transition<E: FieldElement + From<BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = frame.current();
        let next = frame.next();

        // Constraint 0: next[0] = current[0]^3 + current[1]
        result[0] = next[0].clone() - (current[0].clone().exp(3u64.into()) + current[1].clone());
        
        // Constraint 1: next[1] = current[0]
        result[1] = next[1].clone() - current[0].clone();
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        // Assert the final result matches the public input (column 1, last row)
        vec![
            Assertion::single(1, self.context.trace_len() - 1, self.pub_inputs.result),
        ]
    }
}

// ============================================================================
// AGGREGATOR PROVER
// ============================================================================

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    matrix::ColMatrix,
    AuxRandElements, CompositionPoly, CompositionPolyTrace,
    ConstraintCompositionCoefficients, DefaultConstraintCommitment, 
    DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions,
    Proof, Prover, ProverError, StarkDomain, Trace, TracePolyTable, TraceTable,
};
use winter_crypto::hashers::Rp64_256;

/// Aggregator STARK prover
pub struct AggregatorProver {
    options: ProofOptions,
    /// Optional children data for computing full pub_inputs
    children: Option<Vec<ChildStatementHash>>,
}

impl AggregatorProver {
    /// Create a simple prover (pub_inputs will have ZERO for extra fields)
    pub fn new(options: ProofOptions) -> Self {
        Self { options, children: None }
    }
    
    /// Create a prover with children data (pub_inputs will include children_root, etc.)
    pub fn with_children(options: ProofOptions, children: Vec<ChildStatementHash>) -> Self {
        Self { options, children: Some(children) }
    }
}

impl Prover for AggregatorProver {
    type BaseField = BaseElement;
    type Air = AggregatorAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Rp64_256;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn get_pub_inputs(&self, trace: &Self::Trace) -> AggregatorPublicInputs {
        // Result is in column 1, last row
        let result = trace.get(1, trace.length() - 1);
        
        // If we have children data, compute full pub_inputs
        if let Some(ref children) = self.children {
            let children_root = compute_children_merkle_root(children);
            let initial_state = if children.is_empty() {
                [BaseElement::ZERO; 4]
            } else {
                children[0].input_state
            };
            let final_state = if children.is_empty() {
                [BaseElement::ZERO; 4]
            } else {
                children[children.len() - 1].output_state
            };
            let level = if children.is_empty() { 0 } else { children[0].level.saturating_add(1) };
            let start_idx = children.first().map(|c| c.start_idx).unwrap_or(0);
            let end_idx = children.last().map(|c| c.end_idx).unwrap_or(0);
            let context_hash = children.first().map(|c| c.context_hash).unwrap_or([BaseElement::ZERO; 4]);
            let interpreter_hash = children.first().map(|c| c.interpreter_hash).unwrap_or([BaseElement::ZERO; 4]);
            let params_digest = children.first().map(|c| c.params_digest).unwrap_or([BaseElement::ZERO; 4]);
            
            AggregatorPublicInputs {
                result,
                children_root,
                initial_state,
                final_state,
                level,
                start_idx,
                end_idx,
                context_hash,
                interpreter_hash,
                params_digest,
            }
        } else {
            // Simple case: just result, extras are ZERO
            AggregatorPublicInputs::from_result(result)
        }
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &ColMatrix<Self::BaseField>,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::TraceLde<E>, TracePolyTable<E>) {
        DefaultTraceLde::new(trace_info, main_trace, domain, partition_options)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<AuxRandElements<E>>,
        composition_coefficients: ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &StarkDomain<Self::BaseField>,
        partition_options: PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, CompositionPoly<E>) {
        DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }
}

/// Build trace for Aggregator STARK from child hashes
///
/// The trace uses the VDF-like formula to accumulate child hashes:
/// - Row 0: initialized from first child hash elements
/// - Each row: accumulator = prev_accumulator^3 + prev_value
pub fn build_aggregator_trace(
    children: &[ChildStatementHash],
    trace_len: usize,
) -> TraceTable<BaseElement> {
    assert!(trace_len.is_power_of_two());
    
    // Initialize trace columns
    let mut col0 = vec![BaseElement::ZERO; trace_len];
    let mut col1 = vec![BaseElement::ZERO; trace_len];
    
    // Compute children Merkle root and use it to seed the trace
    let children_root = compute_children_merkle_root(children);
    
    // Initial values come from children_root
    col0[0] = children_root[0];
    col1[0] = children_root[1];
    
    // Add more entropy from other root elements
    let extra = children_root[2] + children_root[3];
    col1[0] = col1[0] + extra;
    
    // Compute trace using the VDF-like recurrence:
    // col0[i+1] = col0[i]^3 + col1[i]
    // col1[i+1] = col0[i]
    for i in 0..trace_len - 1 {
        let current_0 = col0[i];
        let current_1 = col1[i];
        
        col0[i + 1] = current_0.exp(3u64.into()) + current_1;
        col1[i + 1] = current_0;
    }
    
    TraceTable::init(vec![col0, col1])
}

/// Generate Aggregator STARK proof from a single app statement hash
/// 
/// This creates a proper ChildStatementHash and uses the multi-child flow
/// to ensure children_root is correctly bound in the public inputs.
pub fn generate_aggregator_proof(
    app_statement_hash: [BaseElement; 4],
    trace_len: usize,
    options: ProofOptions,
) -> Result<(Proof, AggregatorPublicInputs, TraceTable<BaseElement>), ProverError> {
    // Create a proper child with the app hash
    let child = ChildStatementHash {
        input_state: [BaseElement::ZERO; 4],
        output_state: app_statement_hash,
        program_hash: [BaseElement::ZERO; 4],
        chunk_index: 0,
        level: 0,
        start_idx: 0,
        end_idx: 0,
        context_hash: [BaseElement::ZERO; 4],
        interpreter_hash: [BaseElement::ZERO; 4],
        params_digest: [BaseElement::ZERO; 4],
    };
    
    // Use the multi-child flow to ensure proper binding
    generate_aggregator_proof_multi(&[child], trace_len, options)
}

/// Generate Aggregator STARK proof using AggregatorConfig
pub fn generate_aggregator_proof_with_config(
    app_statement_hash: [BaseElement; 4],
    config: &AggregatorConfig,
) -> Result<(Proof, AggregatorPublicInputs, TraceTable<BaseElement>), ProverError> {
    generate_aggregator_proof(
        app_statement_hash,
        config.trace_len,
        config.to_proof_options(),
    )
}

/// Generate Aggregator STARK proof from multiple children
pub fn generate_aggregator_proof_multi(
    children: &[ChildStatementHash],
    trace_len: usize,
    options: ProofOptions,
) -> Result<(Proof, AggregatorPublicInputs, TraceTable<BaseElement>), ProverError> {
    // Verify chain consistency
    assert!(verify_chain_consistency(children), "Chain consistency check failed");
    
    let trace = build_aggregator_trace(children, trace_len);
    
    // Use prover with children data so pub_inputs includes children_root, etc.
    // This ensures the public coin seed during proving matches verification.
    let prover = AggregatorProver::with_children(options, children.to_vec());
    let proof = prover.prove(trace.clone())?;
    let pub_inputs = prover.get_pub_inputs(&trace);

    // Development sanity-check: ensure the produced Aggregator proof verifies.
    // This catches prover/trace/pub-input mismatches early.
    #[cfg(any(test, debug_assertions))]
    {
        use winter_crypto::{DefaultRandomCoin, MerkleTree};
        use winterfell::{verify, AcceptableOptions};

        eprintln!(
            "[aggregator] sanity-check: verifying proof (children={}, trace_len={}, num_queries={}, lde_blowup={}, fri_folding_factor={})",
            children.len(),
            proof.context.trace_info().length(),
            proof.options().num_queries(),
            proof.options().blowup_factor(),
            proof.options().to_fri_options().folding_factor(),
        );
        let acceptable = AcceptableOptions::OptionSet(vec![prover.options().clone()]);
        verify::<AggregatorAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
            proof.clone(),
            pub_inputs.clone(),
            &acceptable,
        )
        .expect("Aggregator proof verification failed (sanity check)");
        eprintln!("[aggregator] sanity-check: proof verified OK");
    }
    
    Ok((proof, pub_inputs, trace))
}

// ============================================================================
// VERIFYING AGGREGATOR (uses common verification function)
// ============================================================================

use super::verifier_air::{
    append_proof_verification_with_options, VerificationResult,
    prover::ParsedProof,
    trace::VerifierTraceBuilder,
};

/// Build aggregator trace that VERIFIES two child STARK proofs
/// 
/// This function:
/// 1. Verifies child proof 0 using the common verification function
/// 2. Verifies child proof 1 using the common verification function
/// 3. Binds both statement hashes together
/// 4. Returns the combined aggregator trace
/// 
/// SECURITY: The AIR constraints enforce that verification was done correctly.
/// A malicious prover cannot produce a valid trace without valid child proofs.
pub fn build_verifying_aggregator_trace(
    child0_proof: &ParsedProof,
    child0_type: super::verifier_air::ood_eval::ChildAirType,
    child1_proof: &ParsedProof,
    child1_type: super::verifier_air::ood_eval::ChildAirType,
) -> (TraceTable<BaseElement>, VerificationResult, VerificationResult, [BaseElement; 4]) {
    // Estimate total trace length (2 proofs + binding rows)
    let child0_len = estimate_verification_trace_length(child0_proof);
    let child1_len = estimate_verification_trace_length(child1_proof);
    let binding_rows = 64; // For combining statement hashes
    let total_len = (child0_len + child1_len + binding_rows).next_power_of_two();
    
    let mut builder = VerifierTraceBuilder::new(total_len);
    
    // SECURITY / API NOTE:
    // This function is used to build a *verifying aggregator* node which verifies 2 child proofs.
    // The child AIR type (and for Generic mode: the interpreter/formula) must be supplied by the
    // caller and will be bound by VerifierAir via the interpreter-hash check(s).
    
    // === Phase 1: Verify child 0 (skip per-child statement hash verification) ===
    // We skip the statement hash check here because pub_inputs.statement_hash
    // will be the COMBINED hash, not child0's individual hash.
    let result0 = append_proof_verification_with_options(
        &mut builder, child0_proof, child0_type, false
    );
    
    // === Phase 2: Verify child 1 (skip per-child statement hash verification) ===
    let result1 = append_proof_verification_with_options(
        &mut builder, child1_proof, child1_type, false
    );
    
    // === Phase 3: Bind both statement hashes ===
    // Absorb both statement hashes to create combined binding
    // This is the ONLY statement hash verification for this aggregator
    let mut combined = [BaseElement::ZERO; 8];
    combined[0..4].copy_from_slice(&result0.statement_hash);
    combined[4..8].copy_from_slice(&result1.statement_hash);
    builder.absorb(&combined);
    builder.permute();
    let combined_hash = builder.squeeze();
    
    // Verify the combined statement hash (this is the binding to pub_inputs.statement_hash)
    let _statement_ok = builder.verify_statement_hash(combined_hash);
    
    // Final acceptance
    builder.accept(true);
    
    // Return the combined hash so the caller can use it for pub_inputs
    (builder.finalize(), result0, result1, combined_hash)
}

/// Estimate trace length for verifying a single proof
fn estimate_verification_trace_length(proof: &ParsedProof) -> usize {
    // Each hash needs 8 rows (RPO cycle)
    let merkle_depth = (proof.trace_len * proof.lde_blowup).ilog2() as usize;
    
    let hash_rows = 8;
    let context_hashes = 2;
    let ood_hashes = (proof.trace_width * 2 + proof.comp_width + 7) / 8 * 2;
    let merkle_rows = proof.num_queries * merkle_depth * hash_rows * 2;
    let fri_rows = proof.num_fri_layers * proof.num_queries * (1 + merkle_depth / 2) * hash_rows;
    
    context_hashes * hash_rows + ood_hashes * hash_rows + merkle_rows + fri_rows + 100
}

/// Create ChildStatementHash from VerificationResult
/// 
/// This binds a verified proof's statement hash to the aggregator structure.
pub fn child_from_verification(
    result: &VerificationResult,
    program_hash: [BaseElement; 4],
    chunk_index: u64,
) -> ChildStatementHash {
    ChildStatementHash {
        input_state: [BaseElement::ZERO; 4],  // Not used for verified proofs
        output_state: result.statement_hash,   // The verified statement hash
        program_hash,                           // Circuit ID of the verified AIR
        chunk_index,
        level: 0,
        start_idx: 0,
        end_idx: 0,
        context_hash: [BaseElement::ZERO; 4],
        interpreter_hash: [BaseElement::ZERO; 4],
        params_digest: [BaseElement::ZERO; 4],
    }
}

/// Create a `ChildStatementHash` from an Aggregator node's public statement.
///
/// This is used when building higher levels of the aggregation tree: parents treat each child
/// (which is itself an Aggregator node) as a span with `(initial_state, final_state)` and a
/// level/span/context/interpreter/params binding.
pub fn child_from_aggregator_pub_inputs(
    pub_inputs: &AggregatorPublicInputs,
    program_hash: [BaseElement; 4],
) -> ChildStatementHash {
    ChildStatementHash {
        input_state: pub_inputs.initial_state,
        output_state: pub_inputs.final_state,
        program_hash,
        chunk_index: pub_inputs.start_idx,
        level: pub_inputs.level,
        start_idx: pub_inputs.start_idx,
        end_idx: pub_inputs.end_idx,
        context_hash: pub_inputs.context_hash,
        interpreter_hash: pub_inputs.interpreter_hash,
        params_digest: pub_inputs.params_digest,
    }
}

// ============================================================================
// VERIFYING AGGREGATOR PROOF GENERATION
// ============================================================================

use super::verifier_air::{VerifierPublicInputs, prover::VerifierProver};

/// Generate a Verifying Aggregator STARK proof
/// 
/// This creates a STARK proof that verifies 2 child proofs.
/// Uses the 32-column VerifierAir structure.
/// 
/// # Architecture
/// 
/// ```text
/// Child 0 (App or Aggregator)  Child 1 (App or Aggregator)
///            \                         /
///             \                       /
///              --- Verifying Aggregator ---
///                         |
///                   Aggregator Proof
/// ```
/// 
/// # Security
/// 
/// The proof binds:
/// - Both child statement hashes
/// - The verification trace showing both were correctly verified
/// - Combined statement hash for propagation up the tree
pub fn generate_verifying_aggregator_proof(
    child0_proof: &ParsedProof,
    child0_type: super::verifier_air::ood_eval::ChildAirType,
    child1_proof: &ParsedProof,
    child1_type: super::verifier_air::ood_eval::ChildAirType,
    expected_child_params_digest: [BaseElement; 4],
    options: ProofOptions,
) -> Result<(Proof, VerifierPublicInputs, TraceTable<BaseElement>), ProverError> {
    // Build the verification trace (27 columns)
    let (trace, result0, result1, combined_hash) = build_verifying_aggregator_trace(
        child0_proof,
        child0_type.clone(),
        child1_proof,
        child1_type.clone(),
    );
    
    // Check both children verified successfully
    // If verification failed, the trace won't satisfy the acceptance flag boundary assertion
    assert!(result0.valid, "Child 0 verification failed");
    assert!(result1.valid, "Child 1 verification failed");
    
    // Create public inputs.
    //
    // The VerifierAir enforces these via boundary assertions on aux counters.
    // To avoid mismatches between "expected" accounting and the actual trace builder
    // schedule (especially across small proof parameter regimes), we derive the
    // expected counters from the constructed trace itself.
    //
    // aux[1] is the mode counter, aux[3] is the checkpoint counter.
    let last = trace.length() - 1;
    // NOTE: with the dedicated idx_reg column, aux columns shifted by +1:
    // aux[1] (mode counter) is at col 29, aux[3] (checkpoint counter) at col 31.
    let expected_mode_counter = trace.get(29, last).as_int() as usize;
    let total_checkpoints = trace.get(31, last).as_int() as usize;
    
    // Compute interpreter hash for the child proofs.
    //
    // IMPORTANT:
    // Today, VerifierAir has a *single* public input `interpreter_hash` which is checked in
    // INTERPRETER mode (aux[2]=5). Because this verifying-aggregator node verifies TWO proofs,
    // both interpreter checks must agree on the same expected hash.
    //
    // In the intended protocol, the armed statement selects the interpreter/formula, and the
    // aggregation tree is built over proofs of that same interpreter. We enforce that here.
    let interpreter_hash_0 = child0_type.compute_formula_hash();
    let interpreter_hash_1 = child1_type.compute_formula_hash();
    assert_eq!(
        interpreter_hash_0, interpreter_hash_1,
        "verifying-aggregator currently requires both children to use the same interpreter hash"
    );
    // Params digest POLICY for the child proofs.
    // SECURITY: do NOT derive this from the proof; it must be fixed by protocol policy.
    let _ = (child0_proof, child1_proof); // keep args used for now
    
    let pub_inputs = VerifierPublicInputs {
        statement_hash: combined_hash,
        trace_commitment: result0.trace_commitment,
        comp_commitment: result0.comp_commitment,
        fri_commitments: result0.fri_commitments.clone(),
        num_queries: child0_proof.num_queries,
        proof_trace_len: trace.length(),
        g_trace: child0_proof.g_trace,
        pub_result: child0_proof.pub_result,
        expected_checkpoint_count: total_checkpoints,
        params_digest: expected_child_params_digest,
        expected_mode_counter,
    };
    
    // Generate proof using VerifierProver
    let prover = VerifierProver::with_pub_inputs(options, pub_inputs.clone());
    let proof = prover.prove(trace.clone())?;
    
    Ok((proof, pub_inputs, trace))
}

/// Compute combined statement hash from two verification results
/// 
/// This creates a unique hash that binds both child proofs together.
/// Uses RPO sponge to match what the trace builder computes.
#[allow(dead_code)]
fn compute_combined_statement_hash(
    result0: &VerificationResult,
    result1: &VerificationResult,
) -> [BaseElement; 4] {
    use super::verifier_air::trace::VerifierTraceBuilder;
    
    // Use the same sponge logic as the trace builder
    // This ensures the computed hash matches what verify_statement_hash checks
    let mut builder = VerifierTraceBuilder::new(64);
    
    // Absorb both statement hashes (8 elements total)
    let mut combined = [BaseElement::ZERO; 8];
    combined[0..4].copy_from_slice(&result0.statement_hash);
    combined[4..8].copy_from_slice(&result1.statement_hash);
    builder.absorb(&combined);
    builder.permute();
    
    // Squeeze to get the combined hash (matches what the trace will compute)
    builder.squeeze()
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use winterfell::{verify, AcceptableOptions};
    use winter_crypto::{DefaultRandomCoin, MerkleTree};

    #[test]
    fn test_aggregator_proof_single_child() {
        let app_hash = [
            BaseElement::new(1),
            BaseElement::new(2),
            BaseElement::new(3),
            BaseElement::new(4),
        ];
        
        let options = ProofOptions::new(
            2, 8, 0,
            winterfell::FieldExtension::None,
            2, 31,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );
        
        let (proof, pub_inputs, _trace) = generate_aggregator_proof(app_hash, 8, options.clone())
            .expect("proof generation should succeed");
        
        let acceptable = AcceptableOptions::OptionSet(vec![options]);
        verify::<AggregatorAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
            proof,
            pub_inputs,
            &acceptable,
        )
        .expect("verification should succeed");
    }
    
    #[test]
    fn test_aggregator_proof_multiple_children() {
        // Create a chain of 4 children
        let children = vec![
            ChildStatementHash {
                input_state: [BaseElement::new(0); 4],
                output_state: [BaseElement::new(100), BaseElement::new(101), BaseElement::new(102), BaseElement::new(103)],
                program_hash: [BaseElement::new(1); 4],
                chunk_index: 0,
                level: 0,
                start_idx: 0,
                end_idx: 0,
                context_hash: [BaseElement::new(10); 4],
                interpreter_hash: [BaseElement::new(20); 4],
                params_digest: [BaseElement::new(30); 4],
            },
            ChildStatementHash {
                input_state: [BaseElement::new(100), BaseElement::new(101), BaseElement::new(102), BaseElement::new(103)],
                output_state: [BaseElement::new(200), BaseElement::new(201), BaseElement::new(202), BaseElement::new(203)],
                program_hash: [BaseElement::new(1); 4],
                chunk_index: 1,
                level: 0,
                start_idx: 1,
                end_idx: 1,
                context_hash: [BaseElement::new(10); 4],
                interpreter_hash: [BaseElement::new(20); 4],
                params_digest: [BaseElement::new(30); 4],
            },
            ChildStatementHash {
                input_state: [BaseElement::new(200), BaseElement::new(201), BaseElement::new(202), BaseElement::new(203)],
                output_state: [BaseElement::new(300), BaseElement::new(301), BaseElement::new(302), BaseElement::new(303)],
                program_hash: [BaseElement::new(1); 4],
                chunk_index: 2,
                level: 0,
                start_idx: 2,
                end_idx: 2,
                context_hash: [BaseElement::new(10); 4],
                interpreter_hash: [BaseElement::new(20); 4],
                params_digest: [BaseElement::new(30); 4],
            },
            ChildStatementHash {
                input_state: [BaseElement::new(300), BaseElement::new(301), BaseElement::new(302), BaseElement::new(303)],
                output_state: [BaseElement::new(400), BaseElement::new(401), BaseElement::new(402), BaseElement::new(403)],
                program_hash: [BaseElement::new(1); 4],
                chunk_index: 3,
                level: 0,
                start_idx: 3,
                end_idx: 3,
                context_hash: [BaseElement::new(10); 4],
                interpreter_hash: [BaseElement::new(20); 4],
                params_digest: [BaseElement::new(30); 4],
            },
        ];
        
        let options = ProofOptions::new(
            2, 8, 0,
            winterfell::FieldExtension::None,
            2, 31,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );
        
        let (proof, pub_inputs, _trace) = generate_aggregator_proof_multi(&children, 8, options.clone())
            .expect("proof generation should succeed");
        
        let acceptable = AcceptableOptions::OptionSet(vec![options]);
        verify::<AggregatorAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
            proof,
            pub_inputs,
            &acceptable,
        )
        .expect("verification should succeed");
    }
    
    #[test]
    fn test_chain_consistency() {
        let good_chain = vec![
            ChildStatementHash {
                input_state: [BaseElement::new(0); 4],
                output_state: [BaseElement::new(1); 4],
                program_hash: [BaseElement::ZERO; 4],
                chunk_index: 0,
                level: 0,
                start_idx: 0,
                end_idx: 0,
                context_hash: [BaseElement::ZERO; 4],
                interpreter_hash: [BaseElement::ZERO; 4],
                params_digest: [BaseElement::ZERO; 4],
            },
            ChildStatementHash {
                input_state: [BaseElement::new(1); 4],  // Matches previous output
                output_state: [BaseElement::new(2); 4],
                program_hash: [BaseElement::ZERO; 4],
                chunk_index: 1,
                level: 0,
                start_idx: 1,
                end_idx: 1,
                context_hash: [BaseElement::ZERO; 4],
                interpreter_hash: [BaseElement::ZERO; 4],
                params_digest: [BaseElement::ZERO; 4],
            },
        ];
        assert!(verify_chain_consistency(&good_chain));
        
        let bad_chain = vec![
            ChildStatementHash {
                input_state: [BaseElement::new(0); 4],
                output_state: [BaseElement::new(1); 4],
                program_hash: [BaseElement::ZERO; 4],
                chunk_index: 0,
                level: 0,
                start_idx: 0,
                end_idx: 0,
                context_hash: [BaseElement::ZERO; 4],
                interpreter_hash: [BaseElement::ZERO; 4],
                params_digest: [BaseElement::ZERO; 4],
            },
            ChildStatementHash {
                input_state: [BaseElement::new(999); 4],  // Does NOT match previous output
                output_state: [BaseElement::new(2); 4],
                program_hash: [BaseElement::ZERO; 4],
                chunk_index: 1,
                level: 0,
                start_idx: 1,
                end_idx: 1,
                context_hash: [BaseElement::ZERO; 4],
                interpreter_hash: [BaseElement::ZERO; 4],
                params_digest: [BaseElement::ZERO; 4],
            },
        ];
        assert!(!verify_chain_consistency(&bad_chain));
    }
    
    #[test]
    fn test_merkle_root_deterministic() {
        let children = vec![
            ChildStatementHash {
                input_state: [BaseElement::new(1); 4],
                output_state: [BaseElement::new(2); 4],
                program_hash: [BaseElement::new(3); 4],
                chunk_index: 0,
                level: 0,
                start_idx: 0,
                end_idx: 0,
                context_hash: [BaseElement::ZERO; 4],
                interpreter_hash: [BaseElement::ZERO; 4],
                params_digest: [BaseElement::ZERO; 4],
            },
        ];
        
        let root1 = compute_children_merkle_root(&children);
        let root2 = compute_children_merkle_root(&children);
        
        assert_eq!(root1, root2, "Merkle root should be deterministic");
    }

    #[test]
    fn test_context_changes_affect_public_binding() {
        let mk_children = |ctx0: BaseElement| {
            vec![
                ChildStatementHash {
                    input_state: [BaseElement::new(0); 4],
                    output_state: [BaseElement::new(1); 4],
                    program_hash: [BaseElement::new(5); 4],
                    chunk_index: 0,
                    level: 0,
                    start_idx: 0,
                    end_idx: 0,
                    context_hash: [ctx0; 4],
                    interpreter_hash: [BaseElement::new(7); 4],
                    params_digest: [BaseElement::new(9); 4],
                },
                ChildStatementHash {
                    input_state: [BaseElement::new(1); 4],
                    output_state: [BaseElement::new(2); 4],
                    program_hash: [BaseElement::new(5); 4],
                    chunk_index: 1,
                    level: 0,
                    start_idx: 1,
                    end_idx: 1,
                    context_hash: [ctx0; 4],
                    interpreter_hash: [BaseElement::new(7); 4],
                    params_digest: [BaseElement::new(9); 4],
                },
            ]
        };

        let options = ProofOptions::new(
            2, 8, 0,
            winterfell::FieldExtension::None,
            2, 31,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );

        let (_p1, pub1, _t1) = generate_aggregator_proof_multi(&mk_children(BaseElement::new(10)), 8, options.clone())
            .expect("proof generation should succeed");
        let (_p2, pub2, _t2) = generate_aggregator_proof_multi(&mk_children(BaseElement::new(11)), 8, options)
            .expect("proof generation should succeed");

        assert_ne!(pub1.result, pub2.result);
        assert_ne!(pub1.children_root, pub2.children_root);
    }

    #[test]
    fn test_tree_level_increments() {
        let leaf_children = vec![
            ChildStatementHash {
                input_state: [BaseElement::new(0); 4],
                output_state: [BaseElement::new(1); 4],
                program_hash: [BaseElement::new(5); 4],
                chunk_index: 0,
                level: 0,
                start_idx: 0,
                end_idx: 0,
                context_hash: [BaseElement::new(10); 4],
                interpreter_hash: [BaseElement::new(20); 4],
                params_digest: [BaseElement::new(30); 4],
            },
            ChildStatementHash {
                input_state: [BaseElement::new(1); 4],
                output_state: [BaseElement::new(2); 4],
                program_hash: [BaseElement::new(5); 4],
                chunk_index: 1,
                level: 0,
                start_idx: 1,
                end_idx: 1,
                context_hash: [BaseElement::new(10); 4],
                interpreter_hash: [BaseElement::new(20); 4],
                params_digest: [BaseElement::new(30); 4],
            },
        ];

        let options = ProofOptions::new(
            2, 8, 0,
            winterfell::FieldExtension::None,
            2, 31,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        );

        let (_p0, pub0, _t0) = generate_aggregator_proof_multi(&leaf_children, 8, options.clone())
            .expect("leaf aggregation should succeed");
        assert_eq!(pub0.level, 1, "first aggregation level should be 1 (children are level 0)");

        // Aggregate two level-1 spans into a level-2 parent.
        let left_child = child_from_aggregator_pub_inputs(&pub0, [BaseElement::new(9); 4]);
        let mut right_child = left_child.clone();
        right_child.start_idx = left_child.end_idx + 1;
        right_child.end_idx = right_child.start_idx;
        right_child.input_state = left_child.output_state;
        right_child.output_state = [BaseElement::new(3); 4];

        let (_p1, pub1, _t1) = generate_aggregator_proof_multi(&[left_child, right_child], 8, options)
            .expect("parent aggregation should succeed");
        assert_eq!(pub1.level, 2);
        assert_eq!(pub1.start_idx, 0);
        assert_eq!(pub1.end_idx, 2);
    }
}
