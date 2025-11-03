//! Minimal VDF example for generating test STARK proofs
//!
//! This is adapted from vendor_winterfell/examples/src/vdf/regular
//! to create the smallest possible valid STARK proof for testing.

use winterfell::{
    crypto::{DefaultRandomCoin, ElementHasher, MerkleTree},
    math::{fields::f64::BaseElement, FieldElement},
    matrix::ColMatrix,
    Air, AirContext, Assertion, AuxRandElements, ByteWriter, CompositionPoly,
    CompositionPolyTrace, ConstraintCompositionCoefficients, DefaultConstraintCommitment,
    DefaultConstraintEvaluator, DefaultTraceLde, EvaluationFrame, PartitionOptions, Proof,
    ProofOptions, Prover, StarkDomain, Trace, TraceInfo, TracePolyTable, TraceTable,
    TransitionConstraintDegree,
};

const TRACE_WIDTH: usize = 2;
const ALPHA: u64 = 3;
const INV_ALPHA: u64 = 12297829382473034411; // Inverse of 3 in Goldilocks

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
        vec![Assertion::single(1, self.context.trace_len() - 1, self.result)]
    }
}

// ===========================================================================================
// VDF PROVER
// ===========================================================================================

pub struct VdfProver {
    options: ProofOptions,
}

impl VdfProver {
    pub fn new(options: ProofOptions) -> Self {
        Self { options }
    }
}

impl Prover for VdfProver {
    type BaseField = BaseElement;
    type Air = VdfAir;
    type Trace = TraceTable<BaseElement>;
    type HashFn = winterfell::crypto::hashers::Blake3_256<BaseElement>;
    type VC = MerkleTree<Self::HashFn>;
    type RandomCoin = DefaultRandomCoin<Self::HashFn>;
    type TraceLde<E: FieldElement<BaseField = BaseElement>> = DefaultTraceLde<E, Self::HashFn, Self::VC>;
    type ConstraintCommitment<E: FieldElement<BaseField = BaseElement>> = DefaultConstraintCommitment<E, Self::HashFn, Self::VC>;
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
pub fn generate_test_vdf_proof(
    start: BaseElement,
    steps: usize,
) -> (Proof, TraceTable<BaseElement>) {
    // Build trace
    let trace = build_vdf_trace(start, steps);
    
    // Minimal proof options for fast testing
    let options = ProofOptions::new(
        28,  // num_queries
        8,   // blowup_factor (2^3)
        0,   // grinding_factor
        winterfell::FieldExtension::None,
        2,   // FRI folding factor (binary FRI to match circuit)
        31,  // FRI max remainder degree
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    // Prove
    let prover = VdfProver::new(options);
    let proof = prover.prove(trace.clone()).expect("VDF proof generation failed");
    
    (proof, trace)
}

/// Extract query leaf data from trace at specific positions
///
/// # Arguments
/// * `trace` - The execution trace
/// * `query_positions` - Indices to extract (from proof.queries)
///
/// # Returns  
/// Leaf data as [query_idx][limb_u64]
pub fn extract_query_leaves(
    trace: &TraceTable<BaseElement>,
    query_positions: &[usize],
) -> Vec<Vec<u64>> {
    query_positions
        .iter()
        .map(|&pos| {
            // Extract row at this position
            // For VDF with width=2, we get 2 GL elements per row
            let row: Vec<u64> = (0..trace.width())
                .map(|col| trace.get(col, pos).as_int())
                .collect();
            row
        })
        .collect()
}

