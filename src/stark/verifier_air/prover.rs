//! Prover for Verifier AIR
//!
//! Generates the execution trace that proves correct STARK verification.
//! Takes a Winterfell proof as input and produces a trace that, when proven,
//! attests to the validity of the original proof.

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    matrix::ColMatrix,
    Air, AuxRandElements, CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients,
    DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions,
    Proof, ProofOptions, Prover, StarkDomain, TraceInfo, TracePolyTable, TraceTable,
};
use winter_crypto::hashers::Rp64_256;

use super::{
    merkle::{MerkleDigest, MerklePath, MerkleDirection},
    trace::VerifierTraceBuilder,
    VerifierAir, VerifierPublicInputs,
};

// ============================================================================
// VERIFIER PROVER
// ============================================================================

/// Prover that generates traces for STARK verification
pub struct VerifierProver {
    options: ProofOptions,
    /// Public inputs to use (must be set before proving)
    pub_inputs: Option<VerifierPublicInputs>,
}

impl VerifierProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { 
            options,
            pub_inputs: None,
        }
    }
    
    /// Create prover with public inputs
    pub fn with_pub_inputs(options: ProofOptions, pub_inputs: VerifierPublicInputs) -> Self {
        Self {
            options,
            pub_inputs: Some(pub_inputs),
        }
    }

    /// Generate a verification trace for the given proof
    ///
    /// This is the core function that "runs" the verifier and records
    /// every step as a row in the execution trace.
    /// 
    /// Uses the common `append_proof_verification` function which can be
    /// reused by Aggregator AIR for verifying multiple proofs.
    pub fn build_verification_trace(
        &self,
        proof_data: &ParsedProof,
    ) -> TraceTable<BaseElement> {
        let estimated_len = estimate_trace_length(proof_data);
        let mut builder = VerifierTraceBuilder::new(estimated_len);

        // Use common verification function
        let result = append_proof_verification(&mut builder, proof_data);

        // CRITICAL: Only accept if all verification checks passed
        // Boundary assertion enforces acceptance_flag = 1, so invalid proofs fail
        builder.accept(result.valid);

        builder.finalize()
    }
    
    /// Generate a verification trace and return the statement hash
    /// 
    /// This variant returns the verification result for use in aggregation.
    pub fn build_verification_trace_with_result(
        &self,
        proof_data: &ParsedProof,
    ) -> (TraceTable<BaseElement>, VerificationResult) {
        let estimated_len = estimate_trace_length(proof_data);
        let mut builder = VerifierTraceBuilder::new(estimated_len);

        // Use common verification function
        let result = append_proof_verification(&mut builder, proof_data);

        // CRITICAL: Only accept if all verification checks passed
        builder.accept(result.valid);

        (builder.finalize(), result)
    }
}

impl Prover for VerifierProver {
    type BaseField = BaseElement;
    type Air = VerifierAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = Rp64_256;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = Self::BaseField>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> VerifierPublicInputs {
        // Use the pre-set public inputs if available
        self.pub_inputs.clone().unwrap_or_else(|| {
            // Fallback to dummy values (should not be used in production)
            VerifierPublicInputs {
                statement_hash: [BaseElement::ZERO; 4],
                trace_commitment: [BaseElement::ZERO; 4],
                comp_commitment: [BaseElement::ZERO; 4],
                fri_commitments: vec![],
                num_queries: 2,
                proof_trace_len: 8,
                g_trace: BaseElement::new(18446744069414584320u64),
                pub_result: BaseElement::ZERO,
            }
        })
    }

    fn options(&self) -> &ProofOptions {
        &self.options
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

// ============================================================================
// COMMON VERIFICATION FUNCTION
// ============================================================================

/// Result of verifying a single STARK proof
#[derive(Clone, Debug)]
pub struct VerificationResult {
    /// Whether all verification checks passed (Merkle roots, OOD, etc.)
    pub valid: bool,
    /// Statement hash binding: commitments + public inputs
    pub statement_hash: [BaseElement; 4],
    /// Trace commitment from the proof
    pub trace_commitment: MerkleDigest,
    /// Composition commitment
    pub comp_commitment: MerkleDigest,
    /// FRI layer commitments
    pub fri_commitments: Vec<MerkleDigest>,
}

/// Append verification trace rows for a single STARK proof
/// 
/// This is the core reusable function for STARK verification.
/// It can be called:
/// - Once by Verifier AIR (single proof verification)
/// - Twice by Aggregator AIR (verify two children then bind)
/// 
/// Returns the verification result containing statement hash and commitments.
/// 
/// SECURITY: This function now enforces verification via AIR constraints:
/// - Merkle hash correctness: Each merkle_step is constrained
/// - Root verification: verify_root emits DeepCompose rows with AIR checks
/// - OOD verification: verify_ood_constraints checks the inner proof's constraints
pub fn append_proof_verification(
    builder: &mut VerifierTraceBuilder,
    proof_data: &ParsedProof,
) -> VerificationResult {
    // Track verification results - ALL checks must pass for acceptance
    let mut all_valid = true;
    
    // === Sanity Checks (like R1CS) ===
    // Check required data is present
    
    eprintln!("[VERIFIER AIR] Proof stats: trace_width={}, comp_width={}, trace_len={}", 
        proof_data.trace_width, proof_data.comp_width, proof_data.trace_len);
    eprintln!("[VERIFIER AIR] num_fri_layers={}, fri_layers.len()={}", 
        proof_data.num_fri_layers, proof_data.fri_layers.len());
    eprintln!("[VERIFIER AIR] trace_queries={}, comp_queries={}, deep_coeffs={}", 
        proof_data.trace_queries.len(), proof_data.comp_queries.len(), proof_data.deep_coeffs.len());
    
    if proof_data.trace_queries.is_empty() { 
        eprintln!("[VERIFIER AIR] FAIL: trace_queries is empty");
        all_valid = false; 
    }
    if proof_data.comp_queries.is_empty() { 
        eprintln!("[VERIFIER AIR] FAIL: comp_queries is empty");
        all_valid = false; 
    }
    if proof_data.trace_queries.len() != proof_data.comp_queries.len() { 
        eprintln!("[VERIFIER AIR] FAIL: trace_queries.len() != comp_queries.len()");
        all_valid = false; 
    }
    
    // FRI layers: 0 is valid for small proofs (num_fri_layers determines expected count)
    if proof_data.fri_layers.len() != proof_data.num_fri_layers { 
        eprintln!("[VERIFIER AIR] FAIL: fri_layers.len() != num_fri_layers");
        all_valid = false; 
    }
    
    if !proof_data.ood_trace_current.is_empty() 
        && proof_data.ood_trace_current.len() != proof_data.trace_width 
    { 
        eprintln!("[VERIFIER AIR] FAIL: ood_trace_current.len() != trace_width");
        all_valid = false; 
    }
    
    let expected_deep_coeffs = proof_data.trace_width * 2 + proof_data.comp_width;
    if proof_data.deep_coeffs.len() < expected_deep_coeffs { 
        eprintln!("[VERIFIER AIR] FAIL: deep_coeffs.len()={} < expected={}", 
            proof_data.deep_coeffs.len(), expected_deep_coeffs);
        all_valid = false; 
    }
    
    for (i, layer) in proof_data.fri_layers.iter().enumerate() {
        if layer.queries.len() != proof_data.num_queries { 
            eprintln!("[VERIFIER AIR] FAIL: fri_layer[{}].queries.len()={} != num_queries={}", 
                i, layer.queries.len(), proof_data.num_queries);
            all_valid = false; 
        }
    }
    
    // === Phase 1: Initialize transcript and absorb context ===
    builder.init_sponge();

    // Absorb proof context (trace info, options)
    let context_elements = proof_data.context_to_elements();
    for chunk in context_elements.chunks(8) {
        let mut absorb_buf = [BaseElement::ZERO; 8];
        for (i, &e) in chunk.iter().enumerate() {
            absorb_buf[i] = e;
        }
        builder.absorb(&absorb_buf);
        builder.permute();
    }

    // === Phase 2: Absorb all commitments (for statement binding) ===
    let mut commit_buf = [BaseElement::ZERO; 8];
    
    // Absorb trace commitment
    commit_buf[0..4].copy_from_slice(&proof_data.trace_commitment);
    builder.absorb(&commit_buf);
    builder.permute();
    
    // Absorb composition commitment
    commit_buf[0..4].copy_from_slice(&proof_data.comp_commitment);
    builder.absorb(&commit_buf);
    builder.permute();
    
    // Absorb FRI commitments
    for fri_commit in &proof_data.fri_commitments {
        commit_buf[0..4].copy_from_slice(fri_commit);
        builder.absorb(&commit_buf);
        builder.permute();
    }

    // === Phase 3: OOD VERIFICATION (CRITICAL FOR SECURITY!) ===
    // Verify the inner proof's AIR constraints at the OOD point z.
    // This prevents the "Free Key" attack where an attacker substitutes a trivial AIR.
    {
        use super::ood_eval::OodFrame;
        
        let ood_frame = OodFrame::new(
            proof_data.ood_trace_current.clone(),
            proof_data.ood_trace_next.clone(),
            proof_data.ood_composition.clone(),
            vec![BaseElement::ZERO; proof_data.comp_width],
        );
        
        // Use constraint coefficients from Fiat-Shamir
        let coeffs: [BaseElement; 3] = if proof_data.constraint_coeffs.len() >= 3 {
            [
                proof_data.constraint_coeffs[0],
                proof_data.constraint_coeffs[1],
                proof_data.constraint_coeffs[2],
            ]
        } else {
            [BaseElement::ONE; 3]
        };
        
        let ood_valid = builder.verify_ood_constraints(
            &ood_frame,
            proof_data.z,
            proof_data.g_trace,
            proof_data.trace_len,
            &coeffs,
            proof_data.pub_result,
        );
        
        if !ood_valid {
            eprintln!("[VERIFIER AIR] FAIL: OOD verification failed");
            all_valid = false;
        }
    }

    // === Phase 4: Verify trace Merkle paths ===
    // AIR constraints enforce:
    // 1. merkle_step correctness (hash(left || right) with correct direction)
    // 2. Root verification (hash_state[0..3] == trace_commitment)
    for query in &proof_data.trace_queries {
        // Initialize hash state with leaf data
        builder.init_leaf(&query.values);
        
        // Process Merkle authentication path
        for step in &query.merkle_path.steps {
            builder.merkle_step(step.sibling, step.direction == MerkleDirection::Right);
        }
        
        // CRITICAL: Verify computed root matches trace commitment
        // AIR constraint enforces hash_state[0..3] == fri[0..3] (expected root)
        let root_ok = builder.verify_root(proof_data.trace_commitment);
        if !root_ok {
            eprintln!("[VERIFIER AIR] FAIL: Trace Merkle root verification failed");
            all_valid = false;
        }
    }

    // === Phase 5: Verify composition Merkle paths ===
    for query in &proof_data.comp_queries {
        // Initialize hash state with leaf data
        builder.init_leaf(&query.values);
        
        // Process Merkle authentication path
        for step in &query.merkle_path.steps {
            builder.merkle_step(step.sibling, step.direction == MerkleDirection::Right);
        }
        
        // CRITICAL: Verify computed root matches composition commitment
        let root_ok = builder.verify_root(proof_data.comp_commitment);
        if !root_ok {
            eprintln!("[VERIFIER AIR] FAIL: Composition Merkle root verification failed");
            all_valid = false;
        }
    }

    // === Phase 6: DEEP Composition Verification (CRITICAL!) ===
    // 
    // R1CS computes DEEP and passes it as FRI starting values.
    // AIR verifies: prover's claimed DEEP values (in layer 0) match our computation.
    //
    // The first FRI layer commits to DEEP polynomial evaluations:
    //   DEEP(x) = Σ γᵢ * (T(x) - T(z)) / (x - z) 
    //           + Σ γⱼ * (T(x) - T(z·g)) / (x - z·g) 
    //           + comp terms
    //
    // We independently compute DEEP(x) and verify it matches the committed f_x values.
    // This prevents a malicious prover from using incorrect DEEP values.
    if !proof_data.fri_layers.is_empty() && !proof_data.trace_queries.is_empty() {
    let first_layer = &proof_data.fri_layers[0];
    
    for (q_idx, fri_query) in first_layer.queries.iter().enumerate() {
        // Get corresponding trace and comp query data
        let trace_query = proof_data.trace_queries.get(q_idx);
        let comp_query = proof_data.comp_queries.get(q_idx);
        
        if let (Some(trace_q), Some(comp_q)) = (trace_query, comp_query) {
            // Compute expected DEEP value at this query position
            let x = fri_query.x;
            let expected_deep = compute_deep_value(
                x,
                &trace_q.values,
                &comp_q.values,
                &proof_data.ood_trace_current,
                &proof_data.ood_trace_next,
                &proof_data.ood_composition,
                proof_data.z,
                proof_data.g_trace,
                &proof_data.deep_coeffs,
            );
            
            // The prover's DEEP value is f_x for the first FRI layer
            let prover_deep = fri_query.f_x;
            
            // Verify DEEP computation is correct (AIR enforces via mode 3)
            let deep_ok = builder.verify_deep_value(prover_deep, expected_deep);
            if !deep_ok {
                all_valid = false;
            }
        }
    }
    } // end DEEP verification guard

    // === Phase 7: FRI layer verification ===
    // Track final folded values for terminal verification
    let mut final_folded_values: Vec<BaseElement> = Vec::new();
    
    for (layer_idx, layer) in proof_data.fri_layers.iter().enumerate() {
        for query in &layer.queries {
            // Initialize hash state with the FRI layer values being committed
            // For folding factor 2: the leaf is (f_x, f_neg_x) pair
            builder.init_leaf(&[query.f_x, query.f_neg_x]);
            
            // Verify Merkle path for this FRI layer
            for step in &query.merkle_path.steps {
                builder.merkle_step(step.sibling, step.direction == MerkleDirection::Right);
            }
            
            // CRITICAL: Verify computed root matches FRI layer commitment
            if layer_idx < proof_data.fri_commitments.len() {
                let root_ok = builder.verify_root(proof_data.fri_commitments[layer_idx]);
                if !root_ok {
                    all_valid = false;
                }
            }
            
            // Fold evaluation - AIR constraint verifies formula is correct
            // NOTE: This is done AFTER root verification because the folded value
            // feeds into the NEXT layer, not this layer's commitment
            let folded = builder.fri_fold(
                query.f_x,
                query.f_neg_x,
                query.x,
                layer.beta,
            );
            
            // Track final layer's folded values for terminal verification
            if layer_idx == proof_data.fri_layers.len() - 1 {
                final_folded_values.push(folded);
            }
        }
    }

    // === Phase 8: FRI Terminal Verification (CRITICAL!) ===
    // Verify that the final folded values are consistent.
    // For Constant terminal: all final values must be equal
    // For Poly terminal: final values must match remainder polynomial evaluation
    if !final_folded_values.is_empty() {
        if proof_data.fri_terminal_is_constant {
            // Constant terminal: all values should equal the first value
            let first_val = final_folded_values[0];
            for &final_val in &final_folded_values[1..] {
                let terminal_ok = builder.verify_fri_terminal(final_val, first_val);
                if !terminal_ok {
                    all_valid = false;
                }
            }
        } else if !proof_data.fri_remainder_coeffs.is_empty() && !proof_data.fri_layers.is_empty() {
            // Polynomial terminal: values should match P(x) at folded positions
            let last_layer = &proof_data.fri_layers[proof_data.fri_layers.len() - 1];
            for (i, &final_val) in final_folded_values.iter().enumerate() {
                if let Some(query) = last_layer.queries.get(i) {
                    // Evaluate remainder polynomial at query.x (post-folding x)
                    let expected = evaluate_polynomial(
                        &proof_data.fri_remainder_coeffs, 
                        query.x
                    );
                    let terminal_ok = builder.verify_fri_terminal(final_val, expected);
                    if !terminal_ok {
                        all_valid = false;
                    }
                }
            }
        }
    }

    // Compute statement hash from commitments
    // This binds the verified proof to a unique identifier
    let statement_hash = compute_statement_hash(
        &proof_data.trace_commitment,
        &proof_data.comp_commitment,
        &proof_data.fri_commitments,
    );

    VerificationResult {
        valid: all_valid,
        statement_hash,
        trace_commitment: proof_data.trace_commitment,
        comp_commitment: proof_data.comp_commitment,
        fri_commitments: proof_data.fri_commitments.clone(),
    }
}

/// Compute statement hash from commitments
/// 
/// This creates a unique identifier for the verified proof.
fn compute_statement_hash(
    trace_commitment: &MerkleDigest,
    comp_commitment: &MerkleDigest,
    fri_commitments: &[MerkleDigest],
) -> [BaseElement; 4] {
    // Simple polynomial combination (in production, use Poseidon)
    let mut h = [BaseElement::ZERO; 4];
    
    // Include trace commitment
    for (i, &elem) in trace_commitment.iter().enumerate() {
        h[i] = h[i] * BaseElement::new(7) + elem;
    }
    
    // Include composition commitment
    for (i, &elem) in comp_commitment.iter().enumerate() {
        h[i] = h[i] * BaseElement::new(11) + elem;
    }
    
    // Include FRI commitments
    for fri_commit in fri_commitments {
        for (i, &elem) in fri_commit.iter().enumerate() {
            h[i] = h[i] * BaseElement::new(13) + elem;
        }
    }
    
    h
}

// ============================================================================
// DEEP COMPOSITION HELPERS
// ============================================================================

/// Compute DEEP polynomial evaluation at position x
/// 
/// DEEP(x) = Σ γᵢ * (T(x) - T(z)) / (x - z) + Σ γⱼ * (T(x) - T(z·g)) / (x - z·g) + comp terms
/// 
/// This combines trace and composition polynomial quotients weighted by random coefficients.
fn compute_deep_value(
    x: BaseElement,
    trace_values: &[BaseElement],  // T(x) for all trace columns
    comp_values: &[BaseElement],   // C(x) for all composition columns
    ood_trace_current: &[BaseElement], // T(z)
    ood_trace_next: &[BaseElement],    // T(z·g)
    ood_composition: &[BaseElement],   // C(z)
    z: BaseElement,
    g_trace: BaseElement,
    deep_coeffs: &[BaseElement],  // γ coefficients
) -> BaseElement {
    // Compute denominators
    let den_z = x - z;           // x - z
    let den_zg = x - (z * g_trace); // x - z·g
    
    // If either denominator is zero, return zero (degenerate case)
    if den_z == BaseElement::ZERO || den_zg == BaseElement::ZERO {
        return BaseElement::ZERO;
    }
    
    // Compute inverse denominators for division
    let inv_den_z = den_z.inv();
    let inv_den_zg = den_zg.inv();
    
    let mut result = BaseElement::ZERO;
    let mut coeff_idx = 0;
    
    // Process trace columns: Σ γᵢ * (T(x) - T(z)) / (x - z)
    for (col, &t_x) in trace_values.iter().enumerate() {
        if coeff_idx >= deep_coeffs.len() { break; }
        let gamma = deep_coeffs[coeff_idx];
        coeff_idx += 1;
        
        // Quotient for (T(x) - T(z)) / (x - z)
        if col < ood_trace_current.len() {
            let t_z = ood_trace_current[col];
            let numerator = t_x - t_z;
            let quotient = numerator * inv_den_z;
            result = result + (gamma * quotient);
        }
    }
    
    // Process trace columns for next: Σ γᵢ * (T(x) - T(z·g)) / (x - z·g)
    for (col, &t_x) in trace_values.iter().enumerate() {
        if coeff_idx >= deep_coeffs.len() { break; }
        let gamma = deep_coeffs[coeff_idx];
        coeff_idx += 1;
        
        // Quotient for (T(x) - T(z·g)) / (x - z·g)
        if col < ood_trace_next.len() {
            let t_zg = ood_trace_next[col];
            let numerator = t_x - t_zg;
            let quotient = numerator * inv_den_zg;
            result = result + (gamma * quotient);
        }
    }
    
    // Process composition columns: Σ γⱼ * (C(x) - C(z)) / (x - z)
    for (col, &c_x) in comp_values.iter().enumerate() {
        if coeff_idx >= deep_coeffs.len() { break; }
        let gamma = deep_coeffs[coeff_idx];
        coeff_idx += 1;
        
        if col < ood_composition.len() {
            let c_z = ood_composition[col];
            let numerator = c_x - c_z;
            let quotient = numerator * inv_den_z;
            result = result + (gamma * quotient);
        }
    }
    
    result
}

/// Evaluate polynomial at a point using Horner's method
/// 
/// P(x) = c[0] + c[1]*x + c[2]*x² + ... + c[n]*x^n
fn evaluate_polynomial(coeffs: &[BaseElement], x: BaseElement) -> BaseElement {
    if coeffs.is_empty() {
        return BaseElement::ZERO;
    }
    
    // Horner's method: start from highest degree
    let mut result = coeffs[coeffs.len() - 1];
    for i in (0..coeffs.len() - 1).rev() {
        result = result * x + coeffs[i];
    }
    result
}

// ============================================================================
// PARSED PROOF STRUCTURE
// ============================================================================

/// Parsed proof data ready for verification trace generation
#[derive(Clone, Debug)]
pub struct ParsedProof {
    // Commitments
    pub trace_commitment: MerkleDigest,
    pub comp_commitment: MerkleDigest,
    pub fri_commitments: Vec<MerkleDigest>,

    // OOD frame
    pub ood_trace_current: Vec<BaseElement>,
    pub ood_trace_next: Vec<BaseElement>,
    pub ood_composition: Vec<BaseElement>,

    // OOD verification parameters (CRITICAL for security!)
    /// OOD challenge point z (derived from Fiat-Shamir)
    pub z: BaseElement,
    /// Trace domain generator g
    pub g_trace: BaseElement,
    /// Constraint mixing coefficients from Fiat-Shamir
    pub constraint_coeffs: Vec<BaseElement>,
    /// Public result/boundary value for verification
    pub pub_result: BaseElement,

    // Query data
    pub trace_queries: Vec<QueryData>,
    pub comp_queries: Vec<QueryData>,
    pub fri_layers: Vec<FriLayerData>,

    // FRI verification data (CRITICAL for faithful verification!)
    /// FRI remainder polynomial coefficients (empty for Constant terminal)
    pub fri_remainder_coeffs: Vec<BaseElement>,
    /// Whether FRI uses constant terminal (all values equal) vs polynomial
    pub fri_terminal_is_constant: bool,
    /// Query positions in LDE domain (derived from Fiat-Shamir)
    pub query_positions: Vec<usize>,
    /// DEEP composition coefficients from Fiat-Shamir
    pub deep_coeffs: Vec<BaseElement>,
    /// Domain offset for LDE domain
    pub domain_offset: BaseElement,
    /// LDE domain generator
    pub g_lde: BaseElement,

    // Parameters
    pub trace_width: usize,
    pub comp_width: usize,
    pub trace_len: usize,
    pub lde_blowup: usize,
    pub num_queries: usize,
    pub num_constraints: usize,
    pub num_fri_layers: usize,
}

impl ParsedProof {
    /// Convert proof context to field elements for transcript
    pub fn context_to_elements(&self) -> Vec<BaseElement> {
        vec![
            BaseElement::new(self.trace_width as u64),
            BaseElement::new(self.comp_width as u64),
            BaseElement::new(self.trace_len as u64),
            BaseElement::new(self.lde_blowup as u64),
            BaseElement::new(self.num_queries as u64),
        ]
    }
}

/// Query opening data
#[derive(Clone, Debug)]
pub struct QueryData {
    pub position: usize,
    pub values: Vec<BaseElement>,
    pub merkle_path: MerklePath,
}

/// FRI layer data
#[derive(Clone, Debug)]
pub struct FriLayerData {
    pub commitment: MerkleDigest,
    pub beta: BaseElement,
    pub queries: Vec<FriQueryData>,
}

/// Single FRI query
#[derive(Clone, Debug)]
pub struct FriQueryData {
    pub f_x: BaseElement,
    pub f_neg_x: BaseElement,
    pub x: BaseElement,
    pub merkle_path: MerklePath,
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Estimate trace length needed for verification
fn estimate_trace_length(proof: &ParsedProof) -> usize {
    // Each hash needs 8 rows (RPO cycle)
    // Merkle path needs depth hashes per query
    let merkle_depth = (proof.trace_len * proof.lde_blowup).ilog2() as usize;
    
    let hash_rows = 8; // RPO cycle
    let context_hashes = 2;
    let ood_hashes = (proof.trace_width * 2 + proof.comp_width + 7) / 8 * 2;
    let merkle_rows = proof.num_queries * merkle_depth * hash_rows * 2; // trace + comp
    let fri_rows = proof.num_fri_layers * proof.num_queries * (1 + merkle_depth / 2) * hash_rows;
    
    let total = context_hashes * hash_rows + ood_hashes * hash_rows + merkle_rows + fri_rows + 100;
    
    total.next_power_of_two()
}



// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::verifier_air::VERIFIER_TRACE_WIDTH;

    fn make_test_proof() -> ParsedProof {
        use winterfell::math::StarkField;
        ParsedProof {
            trace_commitment: [BaseElement::new(1); 4],
            comp_commitment: [BaseElement::new(2); 4],
            fri_commitments: vec![[BaseElement::new(3); 4], [BaseElement::new(4); 4]],
            ood_trace_current: vec![BaseElement::new(10), BaseElement::new(11)],
            ood_trace_next: vec![BaseElement::new(12), BaseElement::new(13)],
            ood_composition: vec![BaseElement::new(20)],
            // OOD verification parameters
            z: BaseElement::new(42), // Test OOD challenge point
            g_trace: BaseElement::get_root_of_unity(3), // trace_len=8, so log2=3
            constraint_coeffs: vec![BaseElement::ONE, BaseElement::ONE, BaseElement::ONE],
            pub_result: BaseElement::ZERO,
            // Query data
            trace_queries: vec![],
            comp_queries: vec![],
            fri_layers: vec![],
            // FRI verification data
            fri_remainder_coeffs: vec![],
            fri_terminal_is_constant: true,
            query_positions: vec![0, 1],
            deep_coeffs: vec![BaseElement::ONE; 5],
            domain_offset: BaseElement::GENERATOR,
            g_lde: BaseElement::get_root_of_unity(6), // lde_domain_size=64, log2=6
            // Parameters
            trace_width: 2,
            comp_width: 1,
            trace_len: 8,
            lde_blowup: 8,
            num_queries: 2,
            num_constraints: 2,
            num_fri_layers: 2,
        }
    }

    #[test]
    fn test_estimate_trace_length() {
        let proof = make_test_proof();
        let len = estimate_trace_length(&proof);
        
        assert!(len.is_power_of_two());
        assert!(len >= 64); // Should be reasonably sized
    }

    #[test]
    fn test_context_to_elements() {
        let proof = make_test_proof();
        let elements = proof.context_to_elements();
        
        assert_eq!(elements.len(), 5);
        assert_eq!(elements[0], BaseElement::new(2)); // trace_width
        assert_eq!(elements[2], BaseElement::new(8)); // trace_len
    }

    #[test]
    fn test_build_verification_trace() {
        let prover = VerifierProver::new(ProofOptions::new(
            2, 8, 0,
            winterfell::FieldExtension::None,
            2, 31,
            winterfell::BatchingMethod::Linear,
            winterfell::BatchingMethod::Linear,
        ));

        let proof = make_test_proof();
        let trace = prover.build_verification_trace(&proof);

        use winterfell::Trace;
        assert!(trace.length().is_power_of_two());
        assert_eq!(trace.width(), VERIFIER_TRACE_WIDTH);
    }



    #[test]
    fn test_compute_deep_value() {
        // Test DEEP computation with simple values
        // DEEP(x) = Σ γᵢ * (T(x) - T(z)) / (x - z) + Σ γⱼ * (T(x) - T(z·g)) / (x - z·g) + comp terms
        
        let x = BaseElement::new(100);
        let z = BaseElement::new(50);
        let g_trace = BaseElement::new(2);
        
        // Simple case: 1 trace column, 1 comp column
        let trace_values = vec![BaseElement::new(10)];  // T(x) = 10
        let comp_values = vec![BaseElement::new(20)];   // C(x) = 20
        let ood_trace_current = vec![BaseElement::new(5)];  // T(z) = 5
        let ood_trace_next = vec![BaseElement::new(7)];     // T(z*g) = 7
        let ood_composition = vec![BaseElement::new(15)];   // C(z) = 15
        
        // Coefficients: γ0 for T(z), γ1 for T(z*g), γ2 for C(z)
        let deep_coeffs = vec![
            BaseElement::new(1), // γ0
            BaseElement::new(1), // γ1  
            BaseElement::new(1), // γ2
        ];
        
        let result = compute_deep_value(
            x,
            &trace_values,
            &comp_values,
            &ood_trace_current,
            &ood_trace_next,
            &ood_composition,
            z,
            g_trace,
            &deep_coeffs,
        );
        
        // Manual calculation:
        // x - z = 100 - 50 = 50
        // x - z*g = 100 - 100 = 0 → will return 0 for degenerate case
        
        // Actually x - z*g = 100 - (50*2) = 100 - 100 = 0
        // This is a degenerate case, function returns 0
        assert_eq!(result, BaseElement::ZERO);
        
        // Test with non-degenerate values
        let z2 = BaseElement::new(30);  // z*g = 60, so x-z*g = 40 ≠ 0
        let result2 = compute_deep_value(
            x,
            &trace_values,
            &comp_values,
            &ood_trace_current,
            &ood_trace_next,
            &ood_composition,
            z2,
            g_trace,
            &deep_coeffs,
        );
        
        // x - z = 100 - 30 = 70
        // x - z*g = 100 - 60 = 40
        // term1 = 1 * (10 - 5) / 70 = 5/70
        // term2 = 1 * (10 - 7) / 40 = 3/40
        // term3 = 1 * (20 - 15) / 70 = 5/70
        // Total = 5/70 + 3/40 + 5/70 = 10/70 + 3/40
        
        // Just verify result is non-zero and deterministic
        assert_ne!(result2, BaseElement::ZERO);
    }

    #[test]
    fn test_evaluate_polynomial() {
        // P(x) = 1 + 2x + 3x²
        let coeffs = vec![
            BaseElement::new(1),
            BaseElement::new(2),
            BaseElement::new(3),
        ];
        
        // P(0) = 1
        assert_eq!(evaluate_polynomial(&coeffs, BaseElement::ZERO), BaseElement::new(1));
        
        // P(1) = 1 + 2 + 3 = 6
        assert_eq!(evaluate_polynomial(&coeffs, BaseElement::ONE), BaseElement::new(6));
        
        // P(2) = 1 + 4 + 12 = 17
        assert_eq!(evaluate_polynomial(&coeffs, BaseElement::new(2)), BaseElement::new(17));
    }
}
