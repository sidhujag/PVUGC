//! Aggregator STARK AIR
//!
//! This is the aggregation layer in the two-AIR design:
//!
//! ```text
//! AppProof -> AggregatorAirProof -> VerifierAirProof -> R1CS
//! ```
//!
//! In this repository, AggregatorAir is implemented as a *verifier-style AIR*:
//! it reuses the same fixed verifier microprogram trace layout as `VerifierAir`.
//! The semantic difference is at the protocol layer: AggregatorAir is where
//! leaf proof verification + aggregation/binding happens.
//!
//! NOTE: OOD-in-AIR hardening is a follow-up todo; this task establishes the
//! real AggregatorAir skeleton (no 2-column toy AIR).

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement, ToElements},
    Air, AirContext, Assertion, EvaluationFrame, Proof, ProofOptions, Prover, ProverError, Trace,
    TraceInfo,
    TransitionConstraintDegree,
};

use winter_crypto::hashers::Rp64_256;

use crate::stark::verifier_air::{
    constraints as verifier_constraints,
    hash_chiplet,
    ood_eval::ChildAirType,
    proof_parser::parse_proof,
    prover::{append_proof_verification_with_options, ParsedProof, VerificationResult},
    trace::VerifierTraceBuilder,
    VerifierPublicInputs,
    HASH_STATE_WIDTH, NUM_SELECTORS, VERIFIER_TRACE_WIDTH,
};

// =============================================================================
// CONSTANTS
// =============================================================================

/// AggregatorAir trace width.
///
/// For the real skeleton we reuse the verifier trace layout.
pub const AGGREGATOR_TRACE_WIDTH: usize = VERIFIER_TRACE_WIDTH;

// =============================================================================
// CONFIG
// =============================================================================

/// Protocol parameters for AggregatorAir proofs (not the leaf app proofs).
#[derive(Clone, Debug)]
pub struct AggregatorConfig {
    /// AggregatorAir trace length (power of 2). Must cover the fixed verifier schedule.
    pub trace_len: usize,
    pub num_queries: usize,
    pub lde_blowup: usize,
    pub grinding_factor: u32,
    pub fri_folding_factor: usize,
    pub fri_max_remainder: usize,
}

impl AggregatorConfig {
    /// Fast dev config (NOT production-secure). Keeps recursion tests snappy.
    pub fn test_fast() -> Self {
        Self {
            // NOTE: verifier-style AIRs use periodic columns; keeping this at 2048 avoids
            // degree-metadata mismatches across configs while we keep degrees specified
            // without explicit `with_cycles(...)` annotations.
            trace_len: 2048,
            num_queries: 2,
            // Verifier-style AIR has high max degrees; keep blowup at 64.
            lde_blowup: 64,
            grinding_factor: 0,
            fri_folding_factor: 2,
            // Use production-style terminal remainder (degree ≤ 31).
            fri_max_remainder: 31,
        }
    }

    pub fn test_with_fri() -> Self {
        Self {
            trace_len: 2048,
            num_queries: 4,
            lde_blowup: 64,
            grinding_factor: 0,
            fri_folding_factor: 2,
            fri_max_remainder: 7,
        }
    }

    pub fn production_128bit() -> Self {
        Self {
            trace_len: 2048,
            num_queries: 28,
            lde_blowup: 64,
            grinding_factor: 12,
            fri_folding_factor: 4,
            fri_max_remainder: 31,
        }
    }

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
}

impl Default for AggregatorConfig {
    fn default() -> Self {
        Self::test_fast()
    }
}

// =============================================================================
// PUBLIC INPUTS
// =============================================================================

/// Public inputs for AggregatorAir.
///
/// We reuse `VerifierPublicInputs` layout. The aggregated statement is carried in `pub_result`
/// and bound via `statement_hash`.
pub type AggregatorPublicInputs = VerifierPublicInputs;

// =============================================================================
// AIR
// =============================================================================

pub struct AggregatorAir {
    context: AirContext<BaseElement>,
    pub_inputs: AggregatorPublicInputs,
}

impl Air for AggregatorAir {
    type BaseField = BaseElement;
    type PublicInputs = AggregatorPublicInputs;

    fn new(trace_info: TraceInfo, pub_inputs: Self::PublicInputs, options: ProofOptions) -> Self {
        assert_eq!(trace_info.width(), AGGREGATOR_TRACE_WIDTH);

        // Mirror verifier-style degrees exactly.
        let degrees: Vec<TransitionConstraintDegree> =
            crate::stark::verifier_air::VERIFIER_TRANSITION_DEGREE_BASES
                .iter()
                .map(|&d| TransitionConstraintDegree::new(d))
                .collect();
        debug_assert_eq!(degrees.len(), AGGREGATOR_TRACE_WIDTH);

        let num_assertions = 8;
        let context = AirContext::new(trace_info, degrees, num_assertions, options);

        Self { context, pub_inputs }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn get_periodic_column_values(&self) -> Vec<Vec<BaseElement>> {
        hash_chiplet::get_periodic_column_values()
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        // Mirror VerifierAir boundary assertions.
        let mut assertions = Vec::new();

        // Initial capacity[0..3] must be zero at row 0.
        for i in 0..4 {
            assertions.push(Assertion::single(NUM_SELECTORS + i, 0, BaseElement::ZERO));
        }
        // Initial aux[1] (mode counter) and aux[3] (checkpoint counter) must be zero.
        assertions.push(Assertion::single(
            crate::stark::verifier_air::constraints::AUX_START + 1,
            0,
            BaseElement::ZERO,
        ));
        assertions.push(Assertion::single(
            crate::stark::verifier_air::constraints::AUX_START + 3,
            0,
            BaseElement::ZERO,
        ));
        // Final aux[1]/aux[3] must match expected values from public inputs.
        let last = self.context.trace_len() - 1;
        assertions.push(Assertion::single(
            crate::stark::verifier_air::constraints::AUX_START + 1,
            last,
            BaseElement::new(self.pub_inputs.expected_mode_counter as u64),
        ));
        assertions.push(Assertion::single(
            crate::stark::verifier_air::constraints::AUX_START + 3,
            last,
            BaseElement::new(self.pub_inputs.expected_checkpoint_count as u64),
        ));

        assertions
    }

    fn evaluate_transition<E: FieldElement<BaseField = BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        periodic_values: &[E],
        result: &mut [E],
    ) {
        verifier_constraints::evaluate_all(frame, periodic_values, result, &self.pub_inputs);
    }
}

// =============================================================================
// STATEMENT HASH (helper)
// =============================================================================

/// Compute the statement hash exactly as VerifierTraceBuilder’s sponge schedule.
fn compute_statement_hash_sponge(parsed: &ParsedProof, child_type: &ChildAirType) -> [BaseElement; 4] {
    #[inline]
    fn sponge_absorb_permute(state: &mut [BaseElement; 12], input: &[BaseElement; 8]) {
        use winter_crypto::hashers::Rp64_256;
        for i in 0..8 {
            state[4 + i] = state[4 + i] + input[i];
        }
        for round in 0..7 {
            Rp64_256::apply_round(state, round);
        }
    }

    let mut state = [BaseElement::ZERO; 12];

    for chunk in parsed.context_to_elements().chunks(8) {
        let mut buf = [BaseElement::ZERO; 8];
        for (i, &e) in chunk.iter().enumerate() {
            buf[i] = e;
        }
        sponge_absorb_permute(&mut state, &buf);
    }

    let mut buf = [BaseElement::ZERO; 8];
    buf[0..4].copy_from_slice(&parsed.trace_commitment);
    sponge_absorb_permute(&mut state, &buf);

    buf = [BaseElement::ZERO; 8];
    buf[0..4].copy_from_slice(&parsed.comp_commitment);
    sponge_absorb_permute(&mut state, &buf);

    for commitment in parsed.fri_commitments.iter() {
        buf = [BaseElement::ZERO; 8];
        buf[0..4].copy_from_slice(commitment);
        sponge_absorb_permute(&mut state, &buf);
    }

    // Bind child AIR type / interpreter hash.
    buf = [BaseElement::ZERO; 8];
    buf[0..4].copy_from_slice(&child_type.compute_formula_hash());
    sponge_absorb_permute(&mut state, &buf);

    [state[0], state[1], state[2], state[3]]
}

// =============================================================================
// PROVER
// =============================================================================

type Hasher = Rp64_256;
type VC = MerkleTree<Hasher>;
type RandomCoin = DefaultRandomCoin<Hasher>;

pub struct AggregatorProver {
    options: ProofOptions,
    pub_inputs: AggregatorPublicInputs,
}

impl AggregatorProver {
    pub fn with_pub_inputs(options: ProofOptions, pub_inputs: AggregatorPublicInputs) -> Self {
        Self { options, pub_inputs }
    }
}

impl Prover for AggregatorProver {
    type BaseField = BaseElement;
    type Air = AggregatorAir;
    type Trace = winterfell::TraceTable<BaseElement>;
    type HashFn = Hasher;
    type VC = VC;
    type RandomCoin = RandomCoin;

    type TraceLde<E: FieldElement<BaseField = BaseElement>> =
        winterfell::DefaultTraceLde<E, Self::HashFn, Self::VC>;

    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        winterfell::DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;

    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        winterfell::DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn options(&self) -> &ProofOptions {
        &self.options
    }

    fn get_pub_inputs(&self, _trace: &Self::Trace) -> AggregatorPublicInputs {
        self.pub_inputs.clone()
    }

    fn new_trace_lde<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        trace_info: &TraceInfo,
        main_trace: &winterfell::matrix::ColMatrix<Self::BaseField>,
        domain: &winterfell::StarkDomain<Self::BaseField>,
        partition_options: winterfell::PartitionOptions,
    ) -> (Self::TraceLde<E>, winterfell::TracePolyTable<E>) {
        winterfell::DefaultTraceLde::new(trace_info, main_trace, domain, partition_options)
    }

    fn new_evaluator<'a, E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        air: &'a Self::Air,
        aux_rand_elements: Option<winterfell::AuxRandElements<E>>,
        composition_coefficients: winterfell::ConstraintCompositionCoefficients<E>,
    ) -> Self::ConstraintEvaluator<'a, E> {
        winterfell::DefaultConstraintEvaluator::new(air, aux_rand_elements, composition_coefficients)
    }

    fn build_constraint_commitment<E: FieldElement<BaseField = Self::BaseField>>(
        &self,
        composition_poly_trace: winterfell::CompositionPolyTrace<E>,
        num_constraint_composition_columns: usize,
        domain: &winterfell::StarkDomain<Self::BaseField>,
        partition_options: winterfell::PartitionOptions,
    ) -> (Self::ConstraintCommitment<E>, winterfell::CompositionPoly<E>) {
        winterfell::DefaultConstraintCommitment::new(
            composition_poly_trace,
            num_constraint_composition_columns,
            domain,
            partition_options,
        )
    }
}

// =============================================================================
// TRACE + PROOF CONSTRUCTION
// =============================================================================

/// Build a leaf AggregatorAir trace verifying one child proof.
pub fn build_aggregator_leaf_trace(
    cfg: &AggregatorConfig,
    child: &ParsedProof,
    child_type: ChildAirType,
) -> (winterfell::TraceTable<BaseElement>, AggregatorPublicInputs, VerificationResult) {
    let mut builder = VerifierTraceBuilder::new(cfg.trace_len);

    let result = append_proof_verification_with_options(&mut builder, child, child_type.clone(), true, None);
    builder.accept(result.valid);
    let trace = builder.finalize();

    // Params digest for the child proof being verified.
    let packed = ((child.fri_folding_factor as u64) << 32) | (child.grinding_factor as u64);
    let params_digest = [
        BaseElement::new(child.trace_len as u64),
        BaseElement::new(child.lde_blowup as u64),
        BaseElement::new(child.num_queries as u64),
        BaseElement::new(packed),
    ];

    let statement_hash = compute_statement_hash_sponge(child, &child_type);

    let pub_inputs = AggregatorPublicInputs {
        statement_hash,
        trace_commitment: child.trace_commitment,
        comp_commitment: child.comp_commitment,
        fri_commitments: child.fri_commitments.clone(),
        num_queries: child.num_queries,
        proof_trace_len: trace.length(),
        g_trace: child.g_trace,
        pub_result: child.pub_result,
        expected_checkpoint_count: AggregatorPublicInputs::compute_expected_checkpoints(
            child.num_queries,
            child.num_fri_layers,
        ),
        params_digest,
        expected_mode_counter: AggregatorPublicInputs::compute_expected_mode_counter(
            1,
            child.num_queries,
            child.num_fri_layers,
        ),
    };
    (trace, pub_inputs, result)
}

/// Prove a leaf AggregatorAir proof from an application proof.
pub fn prove_aggregator_leaf_from_app<A>(
    cfg: &AggregatorConfig,
    app_proof: Proof,
    app_pub_inputs: A::PublicInputs,
    child_type: ChildAirType,
) -> Result<(Proof, AggregatorPublicInputs, winterfell::TraceTable<BaseElement>), ProverError>
where
    A: Air<BaseField = BaseElement>,
    A::PublicInputs: Clone + ToElements<BaseElement> + 'static,
{
    let parsed = parse_proof::<A>(&app_proof, &app_pub_inputs);
    let (trace, pub_inputs, _res) = build_aggregator_leaf_trace(cfg, &parsed, child_type);

    let prover = AggregatorProver::with_pub_inputs(cfg.to_proof_options(), pub_inputs.clone());
    let proof = prover.prove(trace.clone())?;

    Ok((proof, pub_inputs, trace))
}

/// Build an internal AggregatorAir trace verifying two child AggregatorAir proofs and binding them.
pub fn build_aggregator_internal_trace(
    cfg: &AggregatorConfig,
    child0: &ParsedProof,
    child0_type: ChildAirType,
    child1: Option<(&ParsedProof, ChildAirType)>,
) -> (winterfell::TraceTable<BaseElement>, AggregatorPublicInputs, [BaseElement; 4]) {
    let mut builder = VerifierTraceBuilder::new(cfg.trace_len);

    // Verify child 0 (skip per-child statement binding; we bind combined at the end).
    let r0 = append_proof_verification_with_options(&mut builder, child0, child0_type.clone(), false, None);

    let r1 = if let Some((p1, ref t1)) = child1 {
        // Root-kind pool offset logic (kept from previous implementation).
        let child1_base_kind = 2u64 + (child0.fri_commitments.len() as u64);
        Some(append_proof_verification_with_options(
            &mut builder,
            p1,
            t1.clone(),
            false,
            Some(child1_base_kind),
        ))
    } else {
        None
    };

    // Bind both statement hashes.
    let mut combined = [BaseElement::ZERO; 8];
    combined[0..4].copy_from_slice(&r0.statement_hash);
    combined[4..8].copy_from_slice(
        &r1.as_ref()
            .map(|x| x.statement_hash)
            .unwrap_or([BaseElement::ZERO; 4]),
    );
    builder.absorb(&combined);
    builder.permute();
    let combined_hash = builder.squeeze();

    let _ = builder.verify_statement_hash(combined_hash);

    builder.accept(r0.valid && r1.as_ref().map(|x| x.valid).unwrap_or(true));
    let trace = builder.finalize();

    // Public inputs for the internal node: reuse the old scheme (root pool packing).
    // For now we require child0/child1 to share proof params policy; enforcement is a follow-up.
    let mut fri_commitments = child0.fri_commitments.clone();
    if let Some((p1, _)) = child1 {
        fri_commitments.push(p1.trace_commitment);
        fri_commitments.push(p1.comp_commitment);
        fri_commitments.extend_from_slice(&p1.fri_commitments);
    }

    let packed = ((child0.fri_folding_factor as u64) << 32) | (child0.grinding_factor as u64);
    let params_digest = [
        BaseElement::new(child0.trace_len as u64),
        BaseElement::new(child0.lde_blowup as u64),
        BaseElement::new(child0.num_queries as u64),
        BaseElement::new(packed),
    ];

    // Compute expected counters deterministically from child ParsedProofs.
    let num_children = if child1.is_some() { 2 } else { 1 };
    let mut expected_ckpt = AggregatorPublicInputs::compute_expected_checkpoints(
        child0.num_queries,
        child0.num_fri_layers,
    );
    if let Some((p1, _)) = child1 {
        expected_ckpt += AggregatorPublicInputs::compute_expected_checkpoints(p1.num_queries, p1.num_fri_layers);
    }
    // +1 for the combined statement hash check row.
    expected_ckpt += 1;

    let expected_mode = {
        // root_count includes both children.
        let root0 = child0.num_queries * (2 + child0.num_fri_layers);
        let mut root = root0;
        let link0 = child0.num_queries * child0.num_fri_layers.saturating_sub(1);
        let mut link = link0;
        if let Some((p1, _)) = child1 {
            root += p1.num_queries * (2 + p1.num_fri_layers);
            link += p1.num_queries * p1.num_fri_layers.saturating_sub(1);
        }
        (root << 32) + 1 + (num_children * 4096) + (link * 65536)
    };

    let pub_inputs = AggregatorPublicInputs {
        statement_hash: combined_hash,
        trace_commitment: child0.trace_commitment,
        comp_commitment: child0.comp_commitment,
        fri_commitments,
        num_queries: child0.num_queries,
        proof_trace_len: trace.length(),
        g_trace: child0.g_trace,
        pub_result: child0.pub_result,
        expected_checkpoint_count: expected_ckpt,
        params_digest,
        expected_mode_counter: expected_mode,
    };

    (trace, pub_inputs, combined_hash)
}

/// Prove an internal AggregatorAir node over one or two child ParsedProofs.
pub fn prove_aggregator_internal_from_parsed(
    cfg: &AggregatorConfig,
    child0: &ParsedProof,
    child0_type: ChildAirType,
    child1: Option<(&ParsedProof, ChildAirType)>,
) -> Result<(Proof, AggregatorPublicInputs, winterfell::TraceTable<BaseElement>), ProverError> {
    let (trace, pub_inputs, _combined) = build_aggregator_internal_trace(cfg, child0, child0_type, child1);

    let prover = AggregatorProver::with_pub_inputs(cfg.to_proof_options(), pub_inputs.clone());
    let proof = prover.prove(trace.clone())?;

    Ok((proof, pub_inputs, trace))
}

/// Convenience: parse an AggregatorAir proof into a `ParsedProof`.
pub fn parse_aggregator_proof(proof: &Proof, pub_inputs: &AggregatorPublicInputs) -> ParsedProof {
    parse_proof::<AggregatorAir>(proof, pub_inputs)
}
