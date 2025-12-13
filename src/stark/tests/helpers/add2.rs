//! Add2 AIR for recursion demos/tests.
//!
//! This proves a simple computation: starting from 0, add 2 each step.
//! The public input is the final output value, which is asserted at the last row.
//!
//! Trace layout (2 columns):
//! - col0: running value
//! - col1: equals `col0` after the transition (so last-row col1 is the final value)
//!
//! Constraints:
//! - c0: next[0] = current[0] + 2
//! - c1: next[1] = next[0]

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

pub struct Add2Air {
    context: AirContext<BaseElement>,
    result: BaseElement,
}

impl Air for Add2Air {
    type BaseField = BaseElement;
    type PublicInputs = BaseElement;

    fn new(trace_info: TraceInfo, pub_inputs: BaseElement, options: ProofOptions) -> Self {
        // 3 constraints:
        // - 2 are linear
        // - 1 is quadratic (degree-2 redundant check) to ensure comp_width >= 2
        //   for recursion scaffolding which expects at least 2 composition columns.
        let degrees = vec![
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(1),
            TransitionConstraintDegree::new(2),
        ];
        assert_eq!(TRACE_WIDTH, trace_info.width());
        Self {
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
        let current = frame.current();
        let next = frame.next();

        // c0: next[0] = current[0] + 2
        result[0] = next[0].clone() - (current[0].clone() + E::from(BaseElement::new(2)));
        // c1: next[1] = next[0]
        result[1] = next[1].clone() - next[0].clone();

        // c2: (next[0] - current[0] - 2)^2 = 0 (redundant, but forces degree-2)
        let d = next[0].clone() - (current[0].clone() + E::from(BaseElement::new(2)));
        result[2] = d.clone() * d;
    }

    fn get_assertions(&self) -> Vec<Assertion<BaseElement>> {
        // Boundary: last-row col1 equals public result.
        vec![Assertion::single(
            1,
            self.context.trace_len() - 1,
            self.result,
        )]
    }
}

pub struct Add2Prover<H: ElementHasher<BaseField = BaseElement> + Send + Sync> {
    options: ProofOptions,
    _hasher: core::marker::PhantomData<H>,
}

impl<H: ElementHasher<BaseField = BaseElement> + Send + Sync> Add2Prover<H> {
    pub fn new(options: ProofOptions) -> Self {
        Self {
            options,
            _hasher: core::marker::PhantomData,
        }
    }
}

impl<H: ElementHasher<BaseField = BaseElement> + Send + Sync> Prover for Add2Prover<H> {
    type BaseField = BaseElement;
    type Air = Add2Air;
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

pub fn build_add2_trace(start: BaseElement, steps: usize) -> TraceTable<BaseElement> {
    let mut trace = TraceTable::new(TRACE_WIDTH, steps);
    trace.fill(
        |state| {
            state[0] = start;
            state[1] = start;
        },
        |_, state| {
            state[0] = state[0] + BaseElement::new(2);
            state[1] = state[0];
        },
    );
    trace
}

pub fn generate_test_add2_proof_rpo_with_options(
    start: BaseElement,
    steps: usize,
    options: ProofOptions,
) -> (Proof, TraceTable<BaseElement>) {
    use winter_crypto::hashers::Rp64_256;
    let trace = build_add2_trace(start, steps);
    let prover = Add2Prover::<Rp64_256>::new(options);
    let proof = prover.prove(trace.clone()).expect("Add2 proof failed");
    (proof, trace)
}

