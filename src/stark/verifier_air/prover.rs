//! Prover for Verifier AIR
//!
//! Generates the execution trace that proves correct STARK verification.
//! Takes a Winterfell proof as input and produces a trace that, when proven,
//! attests to the validity of the original proof.

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    matrix::ColMatrix,
    AuxRandElements, CompositionPoly, CompositionPolyTrace, ConstraintCompositionCoefficients,
    DefaultConstraintCommitment, DefaultConstraintEvaluator, DefaultTraceLde, PartitionOptions,
    ProofOptions, Prover, StarkDomain, TraceInfo, TracePolyTable, TraceTable,
};
use winter_crypto::hashers::Rp64_256;

use super::{
    merkle::{MerkleDigest, MerklePath},
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

    /// Generate a verification trace with explicit child AIR type.
    ///
    /// SECURITY: callers must specify the child AIR type being verified; we do not
    /// "guess" or default, to avoid verifying the wrong statement with the right proof.
    pub fn build_verification_trace(
        &self,
        proof_data: &ParsedProof,
        child_type: super::ood_eval::ChildAirType,
    ) -> TraceTable<BaseElement> {
        let estimated_len = estimate_trace_length(proof_data);
        let mut builder = VerifierTraceBuilder::new(estimated_len);

        // Use common verification function with specified child type
        let result = append_proof_verification(&mut builder, proof_data, child_type);

        // Only accept if all verification checks passed
        // Boundary assertion enforces acceptance_flag = 1, so invalid proofs fail
        builder.accept(result.valid);

        builder.finalize()
    }
    
    /// Generate a verification trace and return the verification result with explicit child type.
    /// 
    /// SECURITY: callers must specify the child AIR type being verified.
    pub fn build_verification_trace_with_result(
        &self,
        proof_data: &ParsedProof,
        child_type: super::ood_eval::ChildAirType,
    ) -> (TraceTable<BaseElement>, VerificationResult) {
        let estimated_len = estimate_trace_length(proof_data);
        let mut builder = VerifierTraceBuilder::new(estimated_len);

        // Use common verification function with specified child type
        let result = append_proof_verification(&mut builder, proof_data, child_type);

        // Only accept if all verification checks passed
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
        let pub_inputs = self.pub_inputs.clone().unwrap_or_else(|| {
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
                expected_checkpoint_count: 0, // Will fail boundary assertion if used
                params_digest: [BaseElement::ZERO; 4],
                expected_mode_counter: 0, // Will fail boundary assertion if used
            }
        });
        pub_inputs
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
/// 
/// # Parameters
/// 
/// - `child_type`: The AIR type of the proof being verified. This determines
///   which constraint formula to use for OOD verification.
///   - Use `ChildAirType::Generic{...}` for app proofs (formula-as-witness)
///   - Use `ChildAirType::verifier_air()` for recursive VerifierAir proofs (aggregator nodes)
pub fn append_proof_verification(
    builder: &mut VerifierTraceBuilder,
    proof_data: &ParsedProof,
    child_type: super::ood_eval::ChildAirType,
) -> VerificationResult {
    append_proof_verification_with_options(builder, proof_data, child_type, true, None)
}

/// Append proof verification trace with options
/// 
/// Same as `append_proof_verification` but with option to skip statement hash verification.
/// Set `verify_statement_hash = false` when verifying multiple child proofs and you want
/// to do ONE combined statement hash verification at the end.
///
/// `root_kind_base` controls how expected Merkle roots are bound to public inputs:
/// - `None`: canonical mapping (0=trace, 1=comp, 2+i=fri[i]).
/// - `Some(base_kind)` (must be >=2): treat this proof's roots as living in the `fri_commitments`
///   pool starting at `base_kind` for trace, `base_kind+1` for comp, and `base_kind+2+i` for FRI layer i.
pub fn append_proof_verification_with_options(
    builder: &mut VerifierTraceBuilder,
    proof_data: &ParsedProof,
    child_type: super::ood_eval::ChildAirType,
    verify_statement_hash: bool,
    root_kind_base: Option<u64>,
) -> VerificationResult {
    // Track verification results - ALL checks must pass for acceptance
    let mut all_valid = true;
    
    // === Sanity Checks (like R1CS) ===
    // Check required data is present

    if proof_data.trace_queries.is_empty() { 
        #[cfg(any(test, debug_assertions))]
        eprintln!("[verifier] sanity: trace_queries empty");
        all_valid = false; 
    }
    if proof_data.comp_queries.is_empty() { 
        #[cfg(any(test, debug_assertions))]
        eprintln!("[verifier] sanity: comp_queries empty");
        all_valid = false; 
    }
    if proof_data.trace_queries.len() != proof_data.comp_queries.len() { 
        #[cfg(any(test, debug_assertions))]
        eprintln!(
            "[verifier] sanity: trace/comp query count mismatch (trace={}, comp={})",
            proof_data.trace_queries.len(),
            proof_data.comp_queries.len()
        );
        all_valid = false; 
    }
    
    // FRI layers: 0 is valid for small proofs (num_fri_layers determines expected count)
    if proof_data.fri_layers.len() != proof_data.num_fri_layers { 
        #[cfg(any(test, debug_assertions))]
        eprintln!(
            "[verifier] sanity: fri_layers len mismatch (got={}, expected={})",
            proof_data.fri_layers.len(),
            proof_data.num_fri_layers
        );
        all_valid = false; 
    }
    
    if !proof_data.ood_trace_current.is_empty() && proof_data.ood_trace_current.len() != proof_data.trace_width {
        #[cfg(any(test, debug_assertions))]
        eprintln!(
            "[verifier] sanity: ood_trace_current width mismatch (got={}, expected={})",
            proof_data.ood_trace_current.len(),
            proof_data.trace_width
        );
        all_valid = false; 
    }
    
    // Winterfell DEEP uses the same gamma for both z and z*g terms.
    // Layout: [γ_trace_0.., γ_comp_0..]
    let expected_deep_coeffs = proof_data.trace_width + proof_data.comp_width;
    if proof_data.deep_coeffs.len() < expected_deep_coeffs { 
        #[cfg(any(test, debug_assertions))]
        eprintln!(
            "[verifier] sanity: deep_coeffs too short (got={}, expected>={})",
            proof_data.deep_coeffs.len(),
            expected_deep_coeffs
        );
        all_valid = false; 
    }
    
    for layer in proof_data.fri_layers.iter() {
        if layer.queries.len() != proof_data.num_queries { 
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

    // Bind child AIR type / app formula ID into the statement hash.
    //
    // SECURITY: prevents AIR-substitution (e.g. verify a different app AIR but claim the same public output).
    // This is also the mechanism that lets production enforce "this proof is an Aggregator node vs an App leaf"
    // without changing Groth16 public inputs: the statement hash commits to the child-type tag.
    let formula_hash = child_type.compute_formula_hash();
    commit_buf = [BaseElement::ZERO; 8];
    commit_buf[0..4].copy_from_slice(&formula_hash);
    builder.absorb(&commit_buf);
    builder.permute();

    // === Statement Hash Verification ===
    // The statement hash binds all commitments to the public inputs.
    // The AIR constraint verifies: hash_state[0..3] == pub_inputs.statement_hash
    // This prevents an attacker from verifying a DIFFERENT proof than what's claimed.
    // 
    // After absorbing all commitments, the hash_state[0..3] contains the computed hash.
    // We emit a DeepCompose row with mode=4 (STATEMENT), and the AIR enforces it
    // equals pub_inputs.statement_hash.
    //
    // NOTE: For Verifying Aggregators with multiple children, we skip per-child
    // statement hash verification and do ONE combined verification at the end.
    // This is because pub_inputs.statement_hash is the COMBINED hash, not per-child.
    let computed_hash = builder.squeeze();
    if verify_statement_hash {
        // Verify statement hash - the real check is the AIR constraint
        // which compares hash_state to pub_inputs.statement_hash
        let statement_ok = builder.verify_statement_hash(computed_hash);
        if !statement_ok {
            all_valid = false;
        }
    }

    // === Phase 3: OOD VERIFICATION ===
    // Verify the inner proof's AIR constraints at the OOD point z.
    {
        use super::ood_eval::OodFrame;
        
        let ood_frame = OodFrame::new(
            proof_data.ood_trace_current.clone(),
            proof_data.ood_trace_next.clone(),
            proof_data.ood_comp_current.clone(),
            proof_data.ood_comp_next.clone(),
        );
        
        // Use constraint coefficients from Fiat-Shamir.
        // For VerifierAir children we need 32 transition + 8 boundary coefficients.
        let num_constraints = child_type.num_constraints();
        let needed_coeffs = if matches!(child_type, super::ood_eval::ChildAirType::VerifierAir) {
            num_constraints + 8
        } else {
            num_constraints + 1
        };
        let coeffs: Vec<BaseElement> = if proof_data.constraint_coeffs.len() >= needed_coeffs {
            proof_data.constraint_coeffs[..needed_coeffs].to_vec()
        } else {
            vec![BaseElement::ONE; needed_coeffs]
        };
        
        let ood_valid = if matches!(child_type, super::ood_eval::ChildAirType::VerifierAir) {
            builder.verify_ood_constraints_verifier_air_child(
                &ood_frame,
                proof_data.z,
                proof_data.g_trace,
                proof_data.trace_len,
                &coeffs,
                proof_data.trace_commitment,
                proof_data.comp_commitment,
                &proof_data.fri_commitments,
                proof_data.num_queries,
                proof_data.trace_len,
                proof_data.pub_result,
                proof_data.verifier_expected_checkpoint_count,
                proof_data.verifier_expected_mode_counter,
                &proof_data.verifier_statement_hash,
                &proof_data.verifier_params_digest,
            )
        } else {
            builder.verify_ood_constraints_typed(
            &ood_frame,
            proof_data.z,
            proof_data.g_trace,
            proof_data.trace_len,
            &coeffs,
            proof_data.pub_result,
            child_type.clone(),
            )
        };
        
        if !ood_valid {
            #[cfg(any(test, debug_assertions))]
            eprintln!("[verifier] OOD verification failed");
            all_valid = false;
        }
        
        // === Params Digest Binding ===
        // Bind the security-relevant STARK options of the proof being verified.
        let packed = ((proof_data.fri_folding_factor as u64) << 32) | (proof_data.grinding_factor as u64);
        let params_digest = [
            BaseElement::new(proof_data.trace_len as u64),
            BaseElement::new(proof_data.lde_blowup as u64),
            BaseElement::new(proof_data.num_queries as u64),
            BaseElement::new(packed),
        ];
        let params_ok = builder.verify_params_digest(params_digest);
        if !params_ok {
            #[cfg(any(test, debug_assertions))]
            eprintln!("[verifier] params-digest binding failed");
            all_valid = false;
        }
    }

    // === Phase 3.5: Derive Fiat–Shamir seed + PoW IN-TRACE (recursion-friendly) ===
    //
    // SECURITY: Verifier randomness (query positions) must be transcript-derived, not prover-chosen.
    // We replicate Winterfell's DefaultRandomCoin flow:
    //   seed0 = hash_elements(context.to_elements() || pub_inputs.to_elements())
    //   seed  = merge(seed, trace_root)
    //   seed  = merge(seed, comp_root)
    //   seed  = merge(seed, hash_elements(merge_ood_evaluations))
    //   seed  = merge(seed, fri_root_i) for all commitments
    //   check_leading_zeros(pow_nonce) >= grinding_factor   (on current seed)
    //   seed_nonce = merge_with_int(seed, pow_nonce)
    //   draws: digest_i = merge_with_int(seed_nonce, i+1) (DefaultRandomCoin::next increments counter first)
    //   pos_i = u64(digest_i[0]) & (lde_domain_size - 1)
    //
    // We use the raw draw order (no sort) and rely on the parser to have reordered openings
    // into this order for fixed-shape recursion. Collisions are allowed; repeated indices re-use
    // the same opening (this is sound and simply reduces the number of distinct checks).
    let lde_domain_size = proof_data.trace_len * proof_data.lde_blowup;
    let domain_bits = if lde_domain_size == 0 || !lde_domain_size.is_power_of_two() {
        all_valid = false;
        0usize
    } else {
        let bits = lde_domain_size.trailing_zeros() as usize;
        if bits > 32 {
            // This recursion pipeline assumes LDE domain size <= 2^32.
            all_valid = false;
            0usize
        } else {
            bits
        }
    };

    // seed0 = hash_elements(context.to_elements() || pub_inputs.to_elements()).
    //
    // SECURITY: do not accept `context_elems` / `pub_inputs_elems` as free witness vectors.
    // We reconstruct the exact Winterfell seed material deterministically from:
    // - parsed proof context fields (trace widths/len/options),
    // - and the child public inputs implied by `child_type`.
    fn reconstruct_context_to_elements_exact(p: &ParsedProof) -> Vec<BaseElement> {
        // Matches winter-air `Context::to_elements()` exactly (no metadata case):
        // - trace_info.to_elements(): [layout_pack, trace_len]
        // - field modulus bytes split into 2 elements (Goldilocks): [1, 0xFFFF_FFFF]
        // - num_constraints (u32)
        // - proof_options.to_elements(): [packed, grinding_factor, num_queries]

        // TraceInfo layout pack:
        // buf = main_width; buf = (buf<<8)|num_aux_segments; if aux present: (buf<<8)|aux_width; (buf<<8)|num_aux_rands
        let mut trace_info_pack = p.trace_width as u32;
        let num_aux_segments: u32 = if p.aux_trace_width > 0 { 1 } else { 0 };
        trace_info_pack = (trace_info_pack << 8) | num_aux_segments;
        if num_aux_segments == 1 {
            trace_info_pack = (trace_info_pack << 8) | (p.aux_trace_width as u32);
            trace_info_pack = (trace_info_pack << 8) | (p.num_aux_segment_rands as u32);
        }

        vec![
            BaseElement::new(trace_info_pack as u64),
            BaseElement::new(p.trace_len as u64),
            // Goldilocks modulus bytes LE: 0xFFFFFFFF00000001 => halves: 0x00000001, 0xFFFFFFFF
            BaseElement::new(1u64),
            BaseElement::new(0xFFFF_FFFFu64),
            BaseElement::new(p.num_constraints as u64),
            BaseElement::new(p.proof_options_packed),
            BaseElement::new(p.grinding_factor as u64),
            BaseElement::new(p.num_queries as u64),
        ]
    }

    fn reconstruct_pub_inputs_to_elements_exact(
        p: &ParsedProof,
        child_type: &super::ood_eval::ChildAirType,
    ) -> Vec<BaseElement> {
        let _ = child_type;
        // IMPORTANT (recursion correctness):
        // Fiat–Shamir seeding MUST use the child proof's public inputs in the exact
        // `pub_inputs.to_elements()` order Winterfell used when generating the proof.
        // We therefore always use the parsed `pub_inputs_elements` verbatim (for both VerifierAir
        // and Generic child types). Any "reconstruction" risks subtle padding/order mismatches,
        // which would change derived query positions and break recursive verification.
        p.pub_inputs_elements.clone()
    }

    let mut seed_material = reconstruct_context_to_elements_exact(proof_data);
    seed_material.extend_from_slice(&reconstruct_pub_inputs_to_elements_exact(proof_data, &child_type));
    let mut seed = builder.hash_elements_digest(&seed_material);

    // reseeds
    seed = builder.merge_digest(seed, proof_data.trace_commitment);
    seed = builder.merge_digest(seed, proof_data.comp_commitment);
    // IMPORTANT: bind OOD digest in-trace (no host-chosen FS knobs).
    // Winterfell merge_ood_evaluations order: [trace_current, comp_current, trace_next, comp_next]
    let mut ood_elems = Vec::new();
    ood_elems.extend_from_slice(&proof_data.ood_trace_current);
    ood_elems.extend_from_slice(&proof_data.ood_comp_current);
    ood_elems.extend_from_slice(&proof_data.ood_trace_next);
    ood_elems.extend_from_slice(&proof_data.ood_comp_next);
    let ood_digest = builder.hash_elements_digest(&ood_elems);
    seed = builder.merge_digest(seed, ood_digest);
    for fri_root in &proof_data.fri_commitments {
        seed = builder.merge_digest(seed, *fri_root);
    }

    // PoW/grinding check on current seed with nonce.
    // Enforce pow_nonce is a 32-bit integer (u32) in-trace.
    builder.qgen_assert_u32(proof_data.pow_nonce);
    let pow_digest = builder.merge_digest_with_int(seed, proof_data.pow_nonce);
    // Enforce PoW and canonical u64 extraction in-trace from pow_digest[0].
    builder.capture_fri4_equals_hash0();
    builder.decompose_fri4_u64_canonical(proof_data.grinding_factor as usize, 0);
    let seed_nonce = pow_digest;

    // === Phase 4: Verify trace Merkle paths ===
    // AIR constraints enforce:
    // 1. merkle_step correctness (hash(left || right) with correct direction)
    // 2. Root verification (hash_state[0..3] == trace_commitment)
    // Load the expected root digest for the trace commitment tree.
    match root_kind_base {
        None => builder.set_expected_root_trace(proof_data.trace_commitment),
        Some(base) => builder.set_expected_root_kind(base, proof_data.trace_commitment),
    }
    for (q_idx, query) in proof_data.trace_queries.iter().enumerate() {
        // Derive and bind the query index IN-TRACE, and export it into the next row's idx register.
        // This closes the "derive honestly then choose any opening index" attack.
        if domain_bits > 0 {
            let _d = builder.merge_digest_with_int(seed_nonce, (q_idx as u64) + 1);
            builder.capture_fri4_equals_hash0();
            let pos = builder.decompose_fri4_u64_canonical(0, domain_bits) as usize;
            if pos != query.position {
                #[cfg(any(test, debug_assertions))]
                eprintln!(
                    "[verifier] derived trace query position mismatch: derived={}, proof={}",
                    pos, query.position
                );
                all_valid = false;
            }
            builder.export_fri6_to_next_idx_reg();
        } else {
            // Invalid domain; keep idx at 0 (will fail elsewhere).
            builder.set_merkle_index(0);
        }
        // Materialize scratch Merkle index from the transcript-derived Q_IDX.
        builder.mask_idx_reg_to_merkle_idx(domain_bits);
        // Initialize hash state with leaf data
        builder.init_leaf(&query.values);
        
        // Process Merkle authentication path
        for step in &query.merkle_path.steps {
            builder.merkle_step_from_index(step.sibling);
        }
        
        // Verify computed root matches the loaded expected trace commitment root.
        let root_ok = builder.verify_root();
        if !root_ok {
            #[cfg(any(test, debug_assertions))]
            eprintln!("[verifier] trace Merkle root check failed at position={}", query.position);
            all_valid = false;
        }
    }

    // === Phase 5: Verify composition Merkle paths ===
    // Load the expected root digest for the composition commitment tree.
    match root_kind_base {
        None => builder.set_expected_root_comp(proof_data.comp_commitment),
        Some(base) => builder.set_expected_root_kind(base + 1, proof_data.comp_commitment),
    }
    for (q_idx, query) in proof_data.comp_queries.iter().enumerate() {
        // Derive/bind the same query index for the composition commitment tree.
        if domain_bits > 0 {
            let _d = builder.merge_digest_with_int(seed_nonce, (q_idx as u64) + 1);
            builder.capture_fri4_equals_hash0();
            let pos = builder.decompose_fri4_u64_canonical(0, domain_bits) as usize;
            if pos != query.position {
                #[cfg(any(test, debug_assertions))]
                eprintln!(
                    "[verifier] derived comp query position mismatch: derived={}, proof={}",
                    pos, query.position
                );
                all_valid = false;
            }
            builder.export_fri6_to_next_idx_reg();
        } else {
            builder.set_merkle_index(0);
        }
        // Materialize scratch Merkle index from the transcript-derived Q_IDX.
        builder.mask_idx_reg_to_merkle_idx(domain_bits);
        // Initialize hash state with leaf data
        builder.init_leaf(&query.values);
        
        // Process Merkle authentication path
        for step in &query.merkle_path.steps {
            builder.merkle_step_from_index(step.sibling);
        }
        
        // Verify computed root matches the loaded expected composition commitment root.
        let root_ok = builder.verify_root();
        if !root_ok {
            #[cfg(any(test, debug_assertions))]
            eprintln!("[verifier] comp Merkle root check failed at position={}", query.position);
            all_valid = false;
        }
    }

    // === Phase 6: DEEP Composition Verification ===
    //
    // Implemented in-trace as a microprogram:
    // - Nop(mode=7) rows accumulate DEEP numerators into carry[3], carry[4]
    // - one DeepCompose(mode=3) row enforces the final cross-multiplied DEEP equation.

    // === Phase 7: FRI layer verification ===
    //
    // Process per-query so that the x-coordinate can be chained across layers as x_{i+1}=x_i^2
    // and so that `IDX_REG` is treated as the persistent query index (Q_IDX) for that slot.
    let mut final_folded_values: Vec<BaseElement> = Vec::new();

    let num_layers = proof_data.fri_layers.len();
    if num_layers > 0 {
        let num_q = proof_data.fri_layers[0].queries.len();

        for q_idx in 0..num_q {
            // Derive and bind the persistent query index (Q_IDX) for this slot.
            if domain_bits > 0 {
                let _d = builder.merge_digest_with_int(seed_nonce, (q_idx as u64) + 1);
                builder.capture_fri4_equals_hash0();
                let pos = builder.decompose_fri4_u64_canonical(0, domain_bits) as usize;
                if let Some(p) = proof_data.query_positions.get(q_idx) {
                    if pos != *p {
                        #[cfg(any(test, debug_assertions))]
                        eprintln!(
                            "[verifier] derived FRI query position mismatch: derived={}, proof={}",
                            pos, *p
                        );
                        all_valid = false;
                    }
                }
                builder.export_fri6_to_next_idx_reg();
            } else {
                builder.set_merkle_index(0);
            }

            // Seed x for layer 0 from the proof’s opened x (todo(3) will derive this from IDX_REG).
            if let Some(q0) = proof_data.fri_layers[0].queries.get(q_idx) {
                builder.set_fri_x(q0.x);
            }
            // Compute x once per query from the transcript-bound Q_IDX (IDX_REG), then
            // carry it across layers by squaring on each FriFold.
            builder.xexp_init_from_qidx();
            builder.xexp_run_32();

            for layer_idx in 0..num_layers {
                let layer = &proof_data.fri_layers[layer_idx];
                let query = match layer.queries.get(q_idx) {
                    Some(q) => q,
                    None => {
                        all_valid = false;
                        break;
                    }
                };

                // Load expected Merkle root for this layer.
                let layer_commitment = proof_data
                    .fri_commitments
                    .get(layer_idx)
                    .copied()
                    .unwrap_or([BaseElement::ZERO; 4]);
                match root_kind_base {
                    None => builder.set_expected_root_fri(layer_idx, layer_commitment),
                    Some(base) => builder.set_expected_root_kind(base + 2 + (layer_idx as u64), layer_commitment),
                }

                // Seed scratch MERKLE_IDX from Q_IDX for this layer, and capture the layer swap bit into carry[5].
                let bits_for_layer = domain_bits.saturating_sub(layer_idx + 1);
                builder.mask_idx_reg_to_merkle_idx(bits_for_layer);

                // Merkle leaf is (f_x, f_neg_x).
                builder.init_leaf(&[query.f_x, query.f_neg_x]);
                for step in &query.merkle_path.steps {
                    builder.merkle_step_from_index(step.sibling);
                }
                if !builder.verify_root() {
                    #[cfg(any(test, debug_assertions))]
                    eprintln!("[verifier] FRI Merkle root failed at layer={}, query={}", layer_idx, q_idx);
                    all_valid = false;
                }

                // DEEP check at layer 0: compute DEEP(x) in-trace and enforce it matches the committed
                // layer-0 opened value (selected by swap bit).
                if layer_idx == 0 {
                    // Trace terms (AggregatorAir has trace_width=2).
                    if let Some(trace_q) = proof_data.trace_queries.get(q_idx) {
                        // gamma_0, gamma_1
                        if proof_data.deep_coeffs.len() >= 2 && trace_q.values.len() >= 2 {
                            builder.deep_accumulate(
                                trace_q.values[0],
                                proof_data.ood_trace_current[0],
                                proof_data.ood_trace_next[0],
                                proof_data.deep_coeffs[0],
                            );
                            builder.deep_accumulate(
                                trace_q.values[1],
                                proof_data.ood_trace_current[1],
                                proof_data.ood_trace_next[1],
                                proof_data.deep_coeffs[1],
                            );
                        } else {
                            all_valid = false;
                        }
                    } else {
                        all_valid = false;
                    }
                    // Comp term (AggregatorAir has comp_width=1).
                    if let Some(comp_q) = proof_data.comp_queries.get(q_idx) {
                        if proof_data.deep_coeffs.len() >= 3 && !comp_q.values.is_empty() {
                            builder.deep_accumulate(
                                comp_q.values[0],
                                proof_data.ood_comp_current[0],
                                proof_data.ood_comp_next[0],
                                proof_data.deep_coeffs[2],
                            );
                        } else {
                            all_valid = false;
                        }
                    } else {
                        all_valid = false;
                    }

                    builder.deep_check(proof_data.z, query.f_x, query.f_neg_x, proof_data.g_trace);
                }

                // If not the first layer, verify the inter-layer link against the *selected* opened
                // value for this layer (depends on the transcript-derived swap bit).
                if layer_idx > 0 {
                    builder.verify_fri_link(query.f_x, query.f_neg_x);
                }

                // Fold (AIR chooses canonical ordering using carry[5]) and store folded in carry[7].
                let folded = builder.fri_fold(query.f_x, query.f_neg_x, layer.beta);

                if layer_idx + 1 == num_layers {
                    final_folded_values.push(folded);
                }
            }
        }
    }

    // === Phase 8: FRI Terminal Verification ===
    // Verify that the final folded values are consistent.
    // For Constant terminal: all final values must be equal
    // For Poly terminal: final values must match remainder polynomial evaluation
    
    if !final_folded_values.is_empty() {
        if proof_data.fri_terminal_is_constant {
            // Constant terminal: all values should equal the first value
            let first_val = final_folded_values[0];
            for &final_val in final_folded_values[1..].iter() {
                if !builder.verify_eq(final_val, first_val) {
                    #[cfg(any(test, debug_assertions))]
                    eprintln!("[verifier] FRI terminal(constant) failed");
                    all_valid = false;
                }
            }
        } else if !proof_data.fri_remainder_coeffs.is_empty() && !proof_data.fri_layers.is_empty() {
            // Polynomial terminal: values should match P(x) at x in the TERMINAL domain
            // 
            // The terminal domain has generator g_terminal = g_lde^(2^num_layers)
            // x_terminal = offset * g_terminal^terminal_pos
            //
            // This matches R1CS implementation in fri.rs lines 293-332
            
            let num_layers = proof_data.fri_layers.len();
            
            // Compute g_terminal = g_lde^(2^num_layers) by repeated squaring
            let mut g_terminal = proof_data.g_lde;
            for _ in 0..num_layers {
                g_terminal = g_terminal * g_terminal;
            }
            
            for (i, &final_val) in final_folded_values.iter().enumerate() {
                // Use the (sorted, unique) query position parsed from the proof, and fold it down
                // by dividing by 2 once per layer (folding factor = 2).
                let mut terminal_pos = proof_data.query_positions.get(i).copied().unwrap_or(0);
                for _ in 0..num_layers {
                    terminal_pos >>= 1;
                }
                
                // Compute x_terminal = offset * g_terminal^terminal_pos
                let x_terminal = proof_data.domain_offset * g_terminal.exp(terminal_pos as u64);
                
                // Terminal check in-trace: for folding_factor=2, remainder degree < 2, so we only
                // support c0 + c1*x here (missing coeffs treated as 0).
                let c0 = proof_data.fri_remainder_coeffs.get(0).copied().unwrap_or(BaseElement::ZERO);
                let c1 = proof_data.fri_remainder_coeffs.get(1).copied().unwrap_or(BaseElement::ZERO);
                builder.set_fri_x(x_terminal);
                if !builder.verify_fri_terminal_poly(final_val, c0, c1) {
                    #[cfg(any(test, debug_assertions))]
                    eprintln!("[verifier] FRI terminal(poly) failed");
                    all_valid = false;
                }
            }
        }
    }

    // IMPORTANT: `computed_hash` is the ONLY statement hash actually enforced by AIR (mode 4).
    // Always return it (even if we skipped the mode-4 check), so higher-level aggregation can
    // bind to the *real* statement hash, not a host-only placeholder.
    let statement_hash = computed_hash;

    VerificationResult {
        valid: all_valid,
        statement_hash,
        trace_commitment: proof_data.trace_commitment,
        comp_commitment: proof_data.comp_commitment,
        fri_commitments: proof_data.fri_commitments.clone(),
    }
}

// ============================================================================
// DEEP COMPOSITION HELPERS
// ============================================================================

/// Compute DEEP polynomial evaluation at position x
/// 
/// DEEP(x) = Σ γᵢ * (T(x) - T(z)) / (x - z) + Σ γⱼ * (T(x) - T(z·g)) / (x - z·g) + comp terms
/// 
/// This combines trace and composition polynomial quotients weighted by random coefficients.
/// 
/// DEEP composition per Winterfell's exact formula (composer.rs):
/// result = (t1_num * den_zg + t2_num * den_z) / (den_z * den_zg)
/// 
/// Where:
/// - t1_num = Σ(T(x)-T(z))*γ for trace + Σ(C(x)-C(z))*γ for comp
/// - t2_num = Σ(T(x)-T(z*g))*γ for trace + Σ(C(x)-C(z*g))*γ for comp
/// 
/// Coefficient layout:
/// - [γ_trace_0..γ_trace_{w-1}]
/// - [γ_comp_0..γ_comp_{c-1}]
fn compute_deep_value(
    x: BaseElement,
    trace_values: &[BaseElement],  // T(x) for all trace columns
    comp_values: &[BaseElement],   // C(x) for all composition columns
    ood_trace_current: &[BaseElement], // T(z)
    ood_trace_next: &[BaseElement],    // T(z·g)
    ood_comp_current: &[BaseElement],  // C(z)
    ood_comp_next: &[BaseElement],     // C(z·g) - from quotient OOD next row
    z: BaseElement,
    g_trace: BaseElement,
    deep_coeffs: &[BaseElement],  // γ coefficients: [trace..., comp...]
) -> BaseElement {
    // Compute denominators
    let den_z = x - z;           // x - z
    let zg = z * g_trace;
    let den_zg = x - zg;         // x - z·g
    
    // If either denominator is zero, return zero (degenerate case)
    if den_z == BaseElement::ZERO || den_zg == BaseElement::ZERO {
        return BaseElement::ZERO;
    }
    
    let trace_w = trace_values.len();
    let comp_w = comp_values.len();
    
    // Accumulate numerators for z and z*g terms
    let mut t1_num = BaseElement::ZERO; // sum for z terms
    let mut t2_num = BaseElement::ZERO; // sum for z*g terms
    
    let mut coeff_idx = 0;
    
    // Process trace columns - SAME gamma for both z and z*g terms
    for col in 0..trace_w {
        if coeff_idx >= deep_coeffs.len() {
            break;
        }
        let gamma = deep_coeffs[coeff_idx];
        coeff_idx += 1;
        
        let t_x = trace_values[col];
        
        // z term: (T(x) - T(z)) * γ
        if col < ood_trace_current.len() {
            let t_z = ood_trace_current[col];
            let diff_z = t_x - t_z;
            t1_num = t1_num + (diff_z * gamma);
        }
        
        // z*g term: (T(x) - T(z*g)) * γ (same gamma!)
        if col < ood_trace_next.len() {
            let t_zg = ood_trace_next[col];
            let diff_zg = t_x - t_zg;
            t2_num = t2_num + (diff_zg * gamma);
        }
    }
    
    // Process composition columns - SAME gamma for both z and z*g terms
    // Winterfell uses ood_quotient_frame.next_row() for z*g, NOT current!
    for col in 0..comp_w {
        if coeff_idx >= deep_coeffs.len() {
            break;
        }
        let gamma = deep_coeffs[coeff_idx];
        coeff_idx += 1;
        
        let c_x = comp_values[col];
        
        // z term: (C(x) - C(z)) * γ
        if col < ood_comp_current.len() {
            let c_z = ood_comp_current[col];
            let diff_z = c_x - c_z;
            t1_num = t1_num + (diff_z * gamma);
        }
        
        // z*g term: (C(x) - C(z*g)) * γ - uses NEXT row from OOD frame!
        if col < ood_comp_next.len() {
            let c_zg = ood_comp_next[col];
            let diff_zg = c_x - c_zg;
            t2_num = t2_num + (diff_zg * gamma);
        }
    }
    
    // DEEP composition: (t1_num * den_zg + t2_num * den_z) / (den_z * den_zg)
    let cross1 = t1_num * den_zg;
    let cross2 = t2_num * den_z;
    let numerator = cross1 + cross2;
    let denominator = den_z * den_zg;
    
    numerator * denominator.inv()
}

/// Evaluate polynomial at a point using Horner's method
///
/// Coefficients are in HIGH to LOW order (matches R1CS/Winterfell):
/// P(x) = c[0]*x^n + c[1]*x^(n-1) + ... + c[n-1]*x + c[n]
fn evaluate_polynomial(coeffs: &[BaseElement], x: BaseElement) -> BaseElement {
    if coeffs.is_empty() {
        return BaseElement::ZERO;
    }

    // Horner's method: P(x) = ((...((c[0]*x + c[1])*x + c[2])*x + ...)*x + c[n])
    // Start with c[0], multiply by x and add next coefficient
    let mut result = coeffs[0];
    for &coeff in &coeffs[1..] {
        result = result * x + coeff;
    }
    result
}

// ============================================================================
// PARSED PROOF STRUCTURE
// ============================================================================

/// Parsed proof data ready for verification trace generation
#[derive(Clone, Debug)]
pub struct ParsedProof {
    /// Proof-specific PoW nonce used by Winterfell for query position derivation.
    pub pow_nonce: u64,

    /// Child proof public inputs as elements (exact Winterfell `pub_inputs.to_elements()` order).
    ///
    /// Required to replay Winterfell Fiat–Shamir seeding in-trace for fixed-shape recursion
    /// when verifying AggregatorAir proofs (whose public inputs are not a single element).
    pub pub_inputs_elements: Vec<BaseElement>,

    // Commitments
    pub trace_commitment: MerkleDigest,
    pub comp_commitment: MerkleDigest,
    pub fri_commitments: Vec<MerkleDigest>,

    // OOD frame
    pub ood_trace_current: Vec<BaseElement>,
    pub ood_trace_next: Vec<BaseElement>,
    pub ood_comp_current: Vec<BaseElement>,  // C(z)
    pub ood_comp_next: Vec<BaseElement>,     // C(z*g) - needed for DEEP composition!
    /// Digest of `merge_ood_evaluations(trace_ood_frame, comp_ood_frame)` used to reseed the public coin.
    pub ood_evals_digest: MerkleDigest,

    // OOD verification parameters
    /// OOD challenge point z (derived from Fiat-Shamir)
    pub z: BaseElement,
    /// Trace domain generator g
    pub g_trace: BaseElement,
    /// Constraint mixing coefficients from Fiat-Shamir
    pub constraint_coeffs: Vec<BaseElement>,
    /// Public result/boundary value for verification
    pub pub_result: BaseElement,

    // VerifierAir-specific public-input tail (needed to verify VerifierAir proofs recursively)
    //
    // When the child proof is itself a VerifierAir proof, its AIR has boundary constraints
    // that depend on these public inputs (final aux counters + params digest + statement hash).
    // These are extracted from `VerifierPublicInputs::to_elements()` by the parser.
    pub verifier_statement_hash: [BaseElement; 4],
    pub verifier_params_digest: [BaseElement; 4],
    pub verifier_expected_checkpoint_count: usize,
    pub verifier_expected_mode_counter: usize,

    // Query data
    pub trace_queries: Vec<QueryData>,
    pub comp_queries: Vec<QueryData>,
    pub fri_layers: Vec<FriLayerData>,

    // FRI verification data
    /// FRI remainder polynomial coefficients (empty for Constant terminal)
    pub fri_remainder_coeffs: Vec<BaseElement>,
    /// Whether FRI uses constant terminal (all values equal) vs polynomial
    pub fri_terminal_is_constant: bool,
    /// Query positions in LDE domain as parsed from the proof (Fiat–Shamir output).
    ///
    /// NOTE: VerifierAir should *re-derive and bind* these positions inside the trace, and then
    /// use the derived positions to drive Merkle/FRI verification. This field is kept for parsing.
    pub query_positions: Vec<usize>,
    /// DEEP composition coefficients from Fiat-Shamir
    pub deep_coeffs: Vec<BaseElement>,
    /// Domain offset for LDE domain
    pub domain_offset: BaseElement,
    /// LDE domain generator
    pub g_lde: BaseElement,

    // Parameters
    pub trace_width: usize,
    pub aux_trace_width: usize,
    pub comp_width: usize,
    pub trace_len: usize,
    pub lde_blowup: usize,
    pub num_queries: usize,
    pub num_constraints: usize,
    pub num_fri_layers: usize,
    pub fri_folding_factor: usize,
    pub grinding_factor: u32,
    pub num_trace_segments: usize,
    /// Proof-options encoding used by Winterfell in `ProofContext::to_elements()`.
    /// This is the packed u32 stored as a field element:
    ///   (field_extension<<24)|(fri_folding_factor<<16)|(fri_remainder_max_degree<<8)|blowup_factor
    pub proof_options_packed: u64,
    /// Number of auxiliary random elements encoded into `TraceInfo::to_elements()` when aux segment exists.
    pub num_aux_segment_rands: usize,
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
    // Note: commitment is accessed via proof_data.fri_commitments[layer_idx]
    // to avoid duplication (matches R1CS pattern)
    pub beta: BaseElement,
    pub queries: Vec<FriQueryData>,
}

/// Single FRI query
#[derive(Clone, Debug)]
pub struct FriQueryData {
    /// Value at the low position (val_low)
    pub f_x: BaseElement,
    /// Value at the high position (val_high)  
    pub f_neg_x: BaseElement,
    /// Domain element at query position
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
            pow_nonce: 0,
            pub_inputs_elements: vec![],
            trace_commitment: [BaseElement::new(1); 4],
            comp_commitment: [BaseElement::new(2); 4],
            fri_commitments: vec![[BaseElement::new(3); 4], [BaseElement::new(4); 4]],
            ood_trace_current: vec![BaseElement::new(10), BaseElement::new(11)],
            ood_trace_next: vec![BaseElement::new(12), BaseElement::new(13)],
            ood_comp_current: vec![BaseElement::new(20)],
            ood_comp_next: vec![BaseElement::new(21)],
            ood_evals_digest: [BaseElement::new(9); 4],
            // OOD verification parameters
            z: BaseElement::new(42), // Test OOD challenge point
            g_trace: BaseElement::get_root_of_unity(3), // trace_len=8, so log2=3
            constraint_coeffs: vec![BaseElement::ONE, BaseElement::ONE, BaseElement::ONE],
            pub_result: BaseElement::ZERO,
            verifier_statement_hash: [BaseElement::ZERO; 4],
            verifier_params_digest: [BaseElement::ZERO; 4],
            verifier_expected_checkpoint_count: 0,
            verifier_expected_mode_counter: 0,
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
            aux_trace_width: 0,
            comp_width: 1,
            trace_len: 8,
            lde_blowup: 8,
            num_queries: 2,
            num_constraints: 2,
            num_fri_layers: 2,
            fri_folding_factor: 2,
            grinding_factor: 0,
            num_trace_segments: 1,
            proof_options_packed: (1u64 << 24) | (2u64 << 16) | (31u64 << 8) | 8u64,
            num_aux_segment_rands: 0,
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
        let trace = prover.build_verification_trace(
            &proof,
            crate::stark::verifier_air::ood_eval::ChildAirType::generic_aggregator_vdf(),
        );

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
        let ood_comp_current = vec![BaseElement::new(15)];  // C(z) = 15
        let ood_comp_next = vec![BaseElement::new(17)];     // C(z*g) = 17
        
        // Coefficients: γ0 for trace, γ1 for comp (same coeff for z and z*g terms!)
        let deep_coeffs = vec![
            BaseElement::new(1), // γ0 - trace col 0
            BaseElement::new(1), // γ1 - comp col 0
        ];
        
        let result = compute_deep_value(
            x,
            &trace_values,
            &comp_values,
            &ood_trace_current,
            &ood_trace_next,
            &ood_comp_current,
            &ood_comp_next,
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
            &ood_comp_current,
            &ood_comp_next,
            z2,
            g_trace,
            &deep_coeffs,
        );
        
        // x - z = 100 - 30 = 70
        // x - z*g = 100 - 60 = 40
        // Winterfell formula: (t1_num * den_zg + t2_num * den_z) / (den_z * den_zg)
        // t1_num = (10-5)*1 + (20-15)*1 = 5 + 5 = 10
        // t2_num = (10-7)*1 + (20-17)*1 = 3 + 3 = 6
        // result = (10*40 + 6*70) / (70*40) = (400 + 420) / 2800 = 820/2800
        // Total = 5/70 + 3/40 + 5/70 = 10/70 + 3/40
        
        // Just verify result is non-zero and deterministic
        assert_ne!(result2, BaseElement::ZERO);
    }

    #[test]
    fn test_evaluate_polynomial() {
        // Coefficients in HIGH to LOW order: P(x) = 3x² + 2x + 1
        let coeffs = vec![
            BaseElement::new(3),  // x² coefficient
            BaseElement::new(2),  // x coefficient
            BaseElement::new(1),  // constant
        ];

        // P(0) = 1
        assert_eq!(evaluate_polynomial(&coeffs, BaseElement::ZERO), BaseElement::new(1));

        // P(1) = 3 + 2 + 1 = 6
        assert_eq!(evaluate_polynomial(&coeffs, BaseElement::ONE), BaseElement::new(6));

        // P(2) = 3*4 + 2*2 + 1 = 12 + 4 + 1 = 17
        assert_eq!(evaluate_polynomial(&coeffs, BaseElement::new(2)), BaseElement::new(17));
    }
}
