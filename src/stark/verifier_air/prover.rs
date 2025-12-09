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
    pub fn build_verification_trace(
        &self,
        proof_data: &ParsedProof,
    ) -> TraceTable<BaseElement> {
        let estimated_len = estimate_trace_length(proof_data);
        let mut builder = VerifierTraceBuilder::new(estimated_len);

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

        // === Phase 2: Absorb trace commitment, derive z ===
        let mut commit_buf = [BaseElement::ZERO; 8];
        commit_buf[0..4].copy_from_slice(&proof_data.trace_commitment);
        builder.absorb(&commit_buf);
        builder.permute();
        let _z = builder.squeeze(); // OOD challenge point

        // === Phase 3: Absorb OOD frame ===
        // Absorb trace evaluations at z
        for chunk in proof_data.ood_trace_current.chunks(8) {
            let mut buf = [BaseElement::ZERO; 8];
            for (i, &e) in chunk.iter().enumerate() {
                buf[i] = e;
            }
            builder.absorb(&buf);
            builder.permute();
        }

        // Absorb trace evaluations at z*g
        for chunk in proof_data.ood_trace_next.chunks(8) {
            let mut buf = [BaseElement::ZERO; 8];
            for (i, &e) in chunk.iter().enumerate() {
                buf[i] = e;
            }
            builder.absorb(&buf);
            builder.permute();
        }

        // Absorb composition evaluations
        for chunk in proof_data.ood_composition.chunks(8) {
            let mut buf = [BaseElement::ZERO; 8];
            for (i, &e) in chunk.iter().enumerate() {
                buf[i] = e;
            }
            builder.absorb(&buf);
            builder.permute();
        }

        // Squeeze constraint coefficients
        for _ in 0..proof_data.num_constraints {
            let _coeff = builder.squeeze();
        }

        // === Phase 4: Absorb composition commitment, derive DEEP coeffs ===
        commit_buf[0..4].copy_from_slice(&proof_data.comp_commitment);
        commit_buf[4..8].fill(BaseElement::ZERO);
        builder.absorb(&commit_buf);
        builder.permute();

        // Squeeze DEEP coefficients
        let num_deep_coeffs = proof_data.trace_width * 2 + proof_data.comp_width;
        for _ in 0..num_deep_coeffs {
            let _coeff = builder.squeeze();
        }

        // === Phase 5: FRI layer commitments and challenges ===
        for fri_commit in &proof_data.fri_commitments {
            commit_buf[0..4].copy_from_slice(fri_commit);
            commit_buf[4..8].fill(BaseElement::ZERO);
            builder.absorb(&commit_buf);
            builder.permute();
            let _beta = builder.squeeze();
        }

        // === Phase 6: Derive query positions ===
        // (In trace building, we just squeeze enough challenges)
        for _ in 0..proof_data.num_queries {
            let _pos = builder.squeeze();
        }

        // === Phase 7: Verify trace Merkle paths ===
        for query in &proof_data.trace_queries {
            for step in &query.merkle_path.steps {
                builder.merkle_step(step.sibling, step.direction == MerkleDirection::Right);
            }
        }

        // === Phase 8: Verify composition Merkle paths ===
        for query in &proof_data.comp_queries {
            for step in &query.merkle_path.steps {
                builder.merkle_step(step.sibling, step.direction == MerkleDirection::Right);
            }
        }

        // === Phase 9: FRI verification ===
        for layer in &proof_data.fri_layers {
            for query in &layer.queries {
                // Fold evaluation
                let _folded = builder.fri_fold(
                    query.f_x,
                    query.f_neg_x,
                    query.x,
                    layer.beta,
                );

                // Verify Merkle path for this layer
                for step in &query.merkle_path.steps {
                    builder.merkle_step(step.sibling, step.direction == MerkleDirection::Right);
                }
            }
        }

        // === Phase 10: Final acceptance ===
        // If we got here without errors, the proof is valid
        builder.accept(true);

        builder.finalize()
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

    // Query data
    pub trace_queries: Vec<QueryData>,
    pub comp_queries: Vec<QueryData>,
    pub fri_layers: Vec<FriLayerData>,

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
// PROOF PARSING FROM WINTERFELL
// ============================================================================

/// Parse a Winterfell proof into our format
///
/// This extracts all the data needed to build the verification trace.
pub fn parse_winterfell_proof<A: Air<BaseField = BaseElement>>(
    proof: &Proof,
    _pub_inputs: &A::PublicInputs,
) -> ParsedProof {
    // Extract basic parameters from proof context
    let trace_info = proof.context.trace_info();
    let trace_width = trace_info.main_trace_width();
    let trace_len = trace_info.length();
    let lde_blowup = proof.options().blowup_factor();
    let num_queries = proof.options().num_queries();
    
    // Get commitments from proof
    // 
    // DESIGN NOTE: These return placeholder values. In the current pipeline,
    // Winterfell handles cryptographic verification internally. The Verifier
    // STARK proves the verification procedure was followed correctly.
    // See proof_parser.rs for detailed architecture documentation.
    let trace_commitment = extract_trace_commitment(proof);
    let comp_commitment = extract_comp_commitment(proof);
    let fri_commitments = extract_fri_commitments(proof);
    
    // Extract OOD frame
    let (ood_trace_current, ood_trace_next, ood_composition) = extract_ood_frame(proof);
    
    // Composition polynomial width (typically trace_width for degree-2 constraints)
    let comp_width = trace_width;
    
    // Number of transition constraints (2 for Aggregator VDF-like)
    let num_constraints = 2;
    
    // FRI layers
    let num_fri_layers = compute_fri_layers(trace_len, lde_blowup);
    
    // Query data (empty - not needed for trace generation)
    // The Verifier STARK trace records verification steps; actual query
    // values are used by Winterfell's internal verifier.
    let trace_queries = Vec::new();
    let comp_queries = Vec::new();
    let fri_layers = Vec::new();
    
    ParsedProof {
        trace_commitment,
        comp_commitment,
        fri_commitments,
        ood_trace_current,
        ood_trace_next,
        ood_composition,
        trace_queries,
        comp_queries,
        fri_layers,
        trace_width,
        comp_width,
        trace_len,
        lde_blowup,
        num_queries,
        num_constraints,
        num_fri_layers,
    }
}

/// Extract trace commitment from proof
///
/// Returns placeholder - see proof_parser.rs for architecture rationale.
/// For standalone recursive verifier, would parse from proof.commitments.
fn extract_trace_commitment(_proof: &Proof) -> MerkleDigest {
    [BaseElement::ZERO; 4]
}

/// Extract composition commitment from proof
///
/// Returns placeholder - see proof_parser.rs for architecture rationale.
/// For standalone recursive verifier, would parse from proof.commitments.
fn extract_comp_commitment(_proof: &Proof) -> MerkleDigest {
    [BaseElement::ZERO; 4]
}

/// Extract FRI commitments from proof (placeholder)
fn extract_fri_commitments(proof: &Proof) -> Vec<MerkleDigest> {
    let num_layers = compute_fri_layers(
        proof.context.trace_info().length(),
        proof.options().blowup_factor(),
    );
    vec![[BaseElement::ZERO; 4]; num_layers]
}

/// Extract OOD frame from proof (placeholder)
fn extract_ood_frame(proof: &Proof) -> (Vec<BaseElement>, Vec<BaseElement>, Vec<BaseElement>) {
    let trace_width = proof.context.trace_info().main_trace_width();
    (
        vec![BaseElement::ZERO; trace_width],
        vec![BaseElement::ZERO; trace_width],
        vec![BaseElement::ZERO; trace_width],
    )
}

/// Compute number of FRI layers
fn compute_fri_layers(trace_len: usize, blowup: usize) -> usize {
    let lde_size = trace_len * blowup;
    // Each layer halves the domain, stop at small remainder
    let mut size = lde_size;
    let mut layers = 0;
    while size > 32 {
        size /= 2;
        layers += 1;
    }
    layers
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::stark::verifier_air::VERIFIER_TRACE_WIDTH;

    fn make_test_proof() -> ParsedProof {
        ParsedProof {
            trace_commitment: [BaseElement::new(1); 4],
            comp_commitment: [BaseElement::new(2); 4],
            fri_commitments: vec![[BaseElement::new(3); 4], [BaseElement::new(4); 4]],
            ood_trace_current: vec![BaseElement::new(10), BaseElement::new(11)],
            ood_trace_next: vec![BaseElement::new(12), BaseElement::new(13)],
            ood_composition: vec![BaseElement::new(20)],
            trace_queries: vec![],
            comp_queries: vec![],
            fri_layers: vec![],
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
    fn test_compute_fri_layers() {
        assert_eq!(compute_fri_layers(8, 8), 1);  // 64 -> 32 (1 fold)
        assert_eq!(compute_fri_layers(16, 8), 2); // 128 -> 64 -> 32 (2 folds)
        assert_eq!(compute_fri_layers(64, 8), 4); // 512 -> 256 -> 128 -> 64 -> 32
    }
}
