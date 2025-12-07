//! Cubic Fibonacci circuit for testing different STARK computations with same AirParams
//!
//! This computes a "cubic fibonacci" recurrence:
//!   next[0] = (current[0] + current[1])³
//!   next[1] = current[0]
//!
//! This is semantically completely different from VDF (x^3+1) but has the same:
//! - trace_width = 2
//! - constraint_degree = 3
//!
//! This proves that ANY computation with matching AirParams can use the same CRS.

use winterfell::{
    crypto::{DefaultRandomCoin, ElementHasher, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, CompositionPoly, CompositionPolyTrace,
    ConstraintCompositionCoefficients, DefaultConstraintCommitment, DefaultConstraintEvaluator,
    DefaultTraceLde, EvaluationFrame, PartitionOptions, Proof, ProofOptions, Prover, StarkDomain,
    Trace, TraceInfo, TracePolyTable, TraceTable, TransitionConstraintDegree,
};

/// Same TRACE_WIDTH as VDF to ensure matching AirParams
const TRACE_WIDTH: usize = 2;
/// Same degree as VDF to match constraint structure
const DEGREE: u64 = 3;

// ===========================================================================================
// CUBIC FIBONACCI AIR
// ===========================================================================================

pub struct CubicFibAir {
    context: AirContext<BaseElement>,
    result: BaseElement,
}

impl Air for CubicFibAir {
    type BaseField = BaseElement;
    type PublicInputs = BaseElement;

    fn new(trace_info: TraceInfo, pub_inputs: BaseElement, options: ProofOptions) -> Self {
        // Same degree as VDF to match num_constraint_composition_columns
        let degrees = vec![TransitionConstraintDegree::new(DEGREE as usize)];
        assert_eq!(TRACE_WIDTH, trace_info.width());

        CubicFibAir {
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

        // CUBIC FIBONACCI: next[0] = (current[0] + current[1])³
        // This is semantically completely different from VDF's next = current³ + 1
        let sum = current[0].clone() + current[1].clone();
        result[0] = next[0].clone() - sum.exp(DEGREE.into());
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
// CUBIC FIBONACCI PROVER
// ===========================================================================================

pub struct CubicFibProver<H: ElementHasher<BaseField = BaseElement> + Send + Sync> {
    options: ProofOptions,
    _hasher: core::marker::PhantomData<H>,
}

impl<H: ElementHasher<BaseField = BaseElement> + Send + Sync> CubicFibProver<H> {
    pub fn new(options: ProofOptions) -> Self {
        Self {
            options,
            _hasher: core::marker::PhantomData,
        }
    }
}

impl<H: ElementHasher<BaseField = BaseElement> + Send + Sync> Prover for CubicFibProver<H> {
    type BaseField = BaseElement;
    type Air = CubicFibAir;
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

/// Build a trace for Cubic Fibonacci: next[0] = (current[0] + current[1])³, next[1] = current[0]
///
/// Starting from (a, b), computes:
///   step 0: (a, b)
///   step 1: ((a+b)³, a)
///   step 2: (((a+b)³ + a)³, (a+b)³)
///   ...
pub fn build_cubic_fib_trace(start_a: BaseElement, start_b: BaseElement, steps: usize) -> TraceTable<BaseElement> {
    let mut trace = TraceTable::new(TRACE_WIDTH, steps);
    trace.fill(
        |state| {
            state[0] = start_a;
            state[1] = start_b;
        },
        |_, state| {
            let sum = state[0] + state[1];
            let new_val = sum.exp(DEGREE.into());
            state[1] = state[0];
            state[0] = new_val;
        },
    );
    trace
}

/// Generate a Cubic Fibonacci STARK proof with RPO-256 hasher
///
/// Uses the same proof options as VDF to ensure matching AirParams
pub fn generate_test_cubic_fib_proof_rpo(
    start_a: BaseElement,
    start_b: BaseElement,
    steps: usize,
) -> (Proof, TraceTable<BaseElement>) {
    const MAX_ATTEMPTS: usize = 8;
    // SAME options as VDF to ensure matching AirParams
    let default_options = ProofOptions::new(
        2,  // minimal queries (same as VDF)
        8,  // blowup (same as VDF)
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
            generate_test_cubic_fib_proof_rpo_with_options(start_a, start_b, steps, default_options.clone());
        if proof.num_unique_queries as usize == target_queries {
            if attempt > 0 {
                eprintln!(
                    "CubicFib proof retries succeeded after {} attempt(s)",
                    attempt + 1
                );
            }
            return (proof, trace);
        } else {
            eprintln!(
                "Retrying CubicFib proof: only {} unique queries (expected {}), attempt {}/{}",
                proof.num_unique_queries,
                target_queries,
                attempt + 1,
                MAX_ATTEMPTS
            );
        }
    }

    panic!(
        "Unable to produce CubicFib proof with {} unique queries after {} attempts",
        default_options.num_queries(),
        MAX_ATTEMPTS
    );
}

pub fn generate_test_cubic_fib_proof_rpo_with_options(
    start_a: BaseElement,
    start_b: BaseElement,
    steps: usize,
    options: ProofOptions,
) -> (Proof, TraceTable<BaseElement>) {
    let trace = build_cubic_fib_trace(start_a, start_b, steps);

    type RpoHasher = winter_crypto::hashers::Rp64_256;
    let prover = CubicFibProver::<RpoHasher>::new(options);
    let proof = prover
        .prove(trace.clone())
        .expect("CubicFib proof with RPO-256 failed");

    (proof, trace)
}

