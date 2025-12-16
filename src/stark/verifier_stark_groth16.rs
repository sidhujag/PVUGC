//! Verifier STARK to Groth16 Integration
//!
//! This module bridges the Verifier STARK with the existing Groth16 wrapper,
//! completing the PVUGC recursive verification pipeline:
//!
//! ```text
//! Application STARK(s)
//!           ↓
//! Aggregator STARK proof (AggregatorAir)
//!           ↓
//! Verifier STARK proof (VerifierAir verifies AggregatorAir)
//!           ↓
//! FullStarkVerifierCircuit (R1CS verifies VerifierAir)
//!           ↓
//!        Groth16 (constant-size proof)
//! ```
//!
//! Key Properties:
//! - Groth16 trusted setup only depends on Verifier STARK parameters (FIXED)
//! - Verifier STARK can verify ANY Aggregator STARK (UNIVERSAL)
//! - Applications can have heterogeneous AIRs

use winterfell::{
    crypto::{DefaultRandomCoin, MerkleTree},
    math::{fields::f64::BaseElement, ToElements},
    Air, Proof, Prover,
};
use winter_crypto::hashers::Rp64_256;

use super::{
    aggregator_air::AggregatorPublicInputs,
    inner_stark_full::{AirParams, FullStarkVerifierCircuit},
    stark_proof_parser::{derive_query_positions, parse_proof_for_circuit_with_query_positions},
    verifier_air::{
        aggregator_integration::{RecursiveConfig, run_recursive_pipeline},
        prover::VerifierProver,
        VerifierAir, VerifierPublicInputs,
    },
    gadgets::{fri::FriTerminalKind, utils::CombinerKind},
    StarkInnerFr,
};

type Hasher = Rp64_256;
type RandomCoin = DefaultRandomCoin<Hasher>;
type VerifierMerkle = MerkleTree<Hasher>;

// ============================================================================
// FULL PIPELINE
// ============================================================================

/// Result of the Verifier STARK proving process
pub struct VerifierStarkResult {
    /// The Verifier STARK proof
    pub proof: Proof,
    /// Public inputs for the Verifier STARK
    pub pub_inputs: VerifierPublicInputs,
    /// The Groth16-ready circuit
    pub circuit: FullStarkVerifierCircuit,
    /// Statement hash that becomes Groth16's public input
    pub statement_hash: StarkInnerFr,
}

/// Generate a Verifier STARK proof from an Aggregator STARK proof (two-AIR design).
pub fn prove_verifier_stark(
    aggregator_proof: &Proof,
    aggregator_pub_inputs: &AggregatorPublicInputs,
    config: RecursiveConfig,
    child_type: crate::stark::verifier_air::ood_eval::ChildAirType,
) -> Result<VerifierStarkResult, String> {
    // Step 1: Build verification trace from Aggregator proof
    // NOTE: in the two-AIR design, VerifierAir is hardcoded to verify AggregatorAir proofs.
    // The child_type is kept in the signature for future-proofing, but is not currently used
    // by the AggregatorIntegration pipeline.
    let _ = child_type;
    let pipeline_result = run_recursive_pipeline(
        aggregator_proof,
        aggregator_pub_inputs,
        config.clone(),
    );

    // Step 2: Get Verifier STARK public inputs
    let verifier_pub_inputs = pipeline_result.verifier_pub_inputs;

    // Step 3: Create Verifier STARK prover with correct public inputs
    let verifier_prover = VerifierProver::with_pub_inputs(
        config.verifier_options.clone(),
        verifier_pub_inputs.clone(),
    );

    // Step 4: Generate Verifier STARK proof
    let verifier_proof = verifier_prover
        .prove(pipeline_result.verifier_trace.clone())
        .map_err(|e| format!("Verifier STARK proving failed: {:?}", e))?;

    // Step 5: Verify the Verifier STARK proof (sanity check)
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![config.verifier_options.clone()]);
    winterfell::verify::<VerifierAir, Hasher, RandomCoin, VerifierMerkle>(
        verifier_proof.clone(),
        verifier_pub_inputs.clone(),
        &acceptable,
    )
    .map_err(|e| format!("Verifier STARK verification failed: {:?}", e))?;

    // Step 6: Parse into Groth16-ready circuit
    // Derive params from actual proof (not fixed assumptions)
    let air = VerifierAir::new(
        verifier_proof.context.trace_info().clone(),
        verifier_pub_inputs.clone(),
        config.verifier_options.clone(),
    );
    
    let trace_len = verifier_proof.context.trace_info().length();
    let lde_domain_size = verifier_proof.context.lde_domain_size();
    let num_queries = verifier_proof.options().num_queries();
    let trace_width = verifier_proof.context.trace_info().main_trace_width();
    
    let lde_generator = air.lde_domain_generator().as_int();
    let domain_offset = air.domain_offset().as_int();
    let g_trace = air.trace_domain_generator().as_int();
    
    let coeffs_len = verifier_proof
        .fri_proof
        .clone()
        .parse_remainder::<BaseElement>()
        .map(|v: Vec<BaseElement>| v.len())
        .unwrap_or(0);
    let fri_terminal = if coeffs_len == 0 {
        FriTerminalKind::Constant
    } else {
        FriTerminalKind::Poly {
            degree: coeffs_len - 1,
        }
    };
    
    let comp_width = air.context().num_constraint_composition_columns();
    let num_constraints = verifier_proof.context.num_constraints();
    let fri_num_layers = verifier_proof
        .options()
        .to_fri_options()
        .num_fri_layers(lde_domain_size);
    
    let air_params = AirParams {
        trace_width,
        comp_width,
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: verifier_proof.options().to_fri_options().folding_factor(),
        fri_num_layers,
        lde_generator,
        domain_offset,
        g_lde: lde_generator,
        g_trace,
        combiner_kind: CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: num_constraints,
        grinding_factor: verifier_proof.options().grinding_factor(),
        aggregator_version: super::inner_stark_full::AGGREGATOR_VERSION,
    };

    let query_positions = derive_query_positions::<Hasher, VerifierAir>(
        &verifier_proof,
        &air,
        &verifier_pub_inputs,
    );

    let pub_inputs_u64: Vec<u64> = verifier_pub_inputs
        .to_elements()
        .iter()
        .map(|e| e.as_int())
        .collect();

    let circuit = parse_proof_for_circuit_with_query_positions::<Hasher, VerifierMerkle>(
        &verifier_proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    );

    let statement_hash = circuit.statement_hash;

    Ok(VerifierStarkResult {
        proof: verifier_proof,
        pub_inputs: verifier_pub_inputs,
        circuit,
        statement_hash,
    })
}

// (legacy integration tests removed: pipeline is now agg-proof (VerifierAir) -> R1CS directly)
