//! Minimal VDF example for generating test STARK proofs
//!
//! This is adapted from vendor_winterfell/examples/src/vdf/regular
//! to create the smallest possible valid STARK proof for testing.

use winterfell::{
    crypto::{DefaultRandomCoin, ElementHasher, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, CompositionPoly, CompositionPolyTrace,
    ConstraintCompositionCoefficients, DefaultConstraintCommitment, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, PartitionOptions, Proof, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

const TRACE_WIDTH: usize = 2;
const ALPHA: u64 = 3;

// ===========================================================================================
// VDF AIR
// ===========================================================================================

pub struct VdfAir {
    context: AirContext<BaseElement>,
    result: BaseElement,
}

impl Air for VdfAir {
    type BaseField = BaseElement;
    type PublicInputs = BaseElement;

    fn new(trace_info: TraceInfo, pub_inputs: BaseElement, options: ProofOptions) -> Self {
        let degrees = vec![TransitionConstraintDegree::new(ALPHA as usize)];
        assert_eq!(TRACE_WIDTH, trace_info.width());

        VdfAir {
            context: AirContext::new(trace_info, degrees, 1, options),
            result: pub_inputs,
        }
    }

    fn context(&self) -> &AirContext<BaseElement> {
        &self.context
    }

    fn evaluate_transition<E: FieldElement + From<BaseElement>>(
        &self,
        frame: &EvaluationFrame<E>,
        _periodic_values: &[E],
        result: &mut [E],
    ) {
        let current = &frame.current();
        let next = &frame.next();

        // Constraint: next[0] = current[0]^3 + 1
        result[0] = next[0].clone() - (current[0].clone().exp(ALPHA.into()) + E::ONE);
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        vec![Assertion::single(
            1,
            self.context.trace_len() - 1,
            self.result,
        )]
    }
}

// ===========================================================================================
// VDF PROVER (Generic over hasher)
// ===========================================================================================

pub struct VdfProver<H: ElementHasher<BaseField = BaseElement> + Send + Sync> {
    options: ProofOptions,
    _hasher: core::marker::PhantomData<H>,
}

impl<H: ElementHasher<BaseField = BaseElement> + Send + Sync> VdfProver<H> {
    pub fn new(options: ProofOptions) -> Self {
        Self {
            options,
            _hasher: core::marker::PhantomData,
        }
    }
}

impl<H: ElementHasher<BaseField = BaseElement> + Send + Sync> Prover for VdfProver<H> {
    type BaseField = BaseElement;
    type Air = VdfAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = H;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> =
        DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;
    type ConstraintEvaluator<'a, E: FieldElement<BaseField = BaseElement>> =
        DefaultConstraintEvaluator<'a, Self::Air, E>;

    fn get_pub_inputs(&self, trace: &Self::Trace) -> BaseElement {
        let last_step = trace.length() - 1;
        trace.get(1, last_step)
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

// ===========================================================================================
// PUBLIC API
// ===========================================================================================

/// Build a minimal VDF trace for testing
///
/// Computes: result = start^(3^steps) + (steps-1)
pub fn build_vdf_trace(start: BaseElement, steps: usize) -> TraceTable<BaseElement> {
    let mut trace = TraceTable::new(TRACE_WIDTH, steps);
    trace.fill(
        |state| {
            state[0] = start;
            state[1] = start;
        },
        |_, state| {
            state[0] = state[0].exp(ALPHA.into()) + BaseElement::ONE;
            state[1] = state[0];
        },
    );
    trace
}

/// Generate a minimal VDF STARK proof for testing
///
/// # Arguments
/// * `start` - Starting value
/// * `steps` - Number of VDF iterations (should be power of 2 for efficiency)
///
/// # Returns
/// (proof, trace_table) where trace_table can be used to extract witness data

/// Generate VDF proof with RPO-256 hasher (for circuit compatibility!)
pub fn generate_test_vdf_proof_rpo(
    start: BaseElement,
    steps: usize,
) -> (Proof, TraceTable<BaseElement>) {
    const MAX_ATTEMPTS: usize = 8;
    let default_options = ProofOptions::new(
        2,  // minimal queries keep regression tests snappy
        8, // blowup to exercise domain logic
        0,  // grinding factor
        winterfell::FieldExtension::None,
        2,  // FRI folding factor
        31, // num FRI layers
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    let target_queries = default_options.num_queries();
    for attempt in 0..MAX_ATTEMPTS {
        let (proof, trace) =
            generate_test_vdf_proof_rpo_with_options(start, steps, default_options.clone());
        if proof.num_unique_queries as usize == target_queries {
            if attempt > 0 {
                eprintln!(
                    "VDF proof retries succeeded after {} attempt(s)",
                    attempt + 1
                );
            }
            return (proof, trace);
        } else {
            eprintln!(
                "Retrying VDF proof: only {} unique queries (expected {}), attempt {}/{}",
                proof.num_unique_queries,
                target_queries,
                attempt + 1,
                MAX_ATTEMPTS
            );
        }
    }

    panic!(
        "Unable to produce VDF proof with {} unique queries after {} attempts",
        default_options.num_queries(),
        MAX_ATTEMPTS
    );
}

pub fn generate_test_vdf_proof_rpo_with_options(
    start: BaseElement,
    steps: usize,
    options: ProofOptions,
) -> (Proof, TraceTable<BaseElement>) {
    let trace = build_vdf_trace(start, steps);

    // Use RPO-256 hasher to match circuit!
    type RpoHasher = winter_crypto::hashers::Rp64_256;
    let prover = VdfProver::<RpoHasher>::new(options);
    let proof = prover
        .prove(trace.clone())
        .expect("VDF proof with RPO-256 failed");

    (proof, trace)
}
