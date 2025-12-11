#![cfg(test)]

use std::{
    fs::File,
    io::{BufReader, BufWriter, Write},
    path::Path,
    sync::{Arc, Mutex},
};

use ark_bls12_377::Bls12_377;
use ark_groth16::{Groth16, ProvingKey, VerifyingKey};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use once_cell::sync::Lazy;
use winter_crypto::hashers::Rp64_256;
use winter_crypto::{DefaultRandomCoin, Digest, MerkleTree};
use winter_math::fields::f64::BaseElement;
use winter_math::{FieldElement, ToElements};
use winterfell::{Air, Proof, ProofOptions, Prover, Trace};

use super::aggregator_air::{generate_aggregator_proof, generate_verifying_aggregator_proof, AggregatorAir, AggregatorConfig};
use super::stark_proof_parser::{
    derive_query_positions, parse_proof_for_circuit_with_query_positions,
};
use super::verifier_air::proof_parser::parse_proof;
use super::tests::helpers::cubic_fib::{generate_test_cubic_fib_proof_rpo, CubicFibAir};
use super::tests::helpers::simple_vdf::{build_vdf_trace, generate_test_vdf_proof_rpo, VdfAir, VdfProver};
use super::{AirParams, FullStarkVerifierCircuit, StarkInnerFr};
use crate::stark::gadgets::fri::FriTerminalKind;
use crate::stark::gadgets::utils::CombinerKind;
use ark_snark::SNARK;

/// Default Aggregator configuration for tests
/// Uses test_fast() for speed, but can be overridden for security testing
pub fn default_aggregator_config() -> AggregatorConfig {
    AggregatorConfig::test_fast()
}

const INNER_CRS_CACHE: &str = "inner_crs_pk_vk.bin";
static INNER_CRS_KEYS: Lazy<
    Mutex<Option<(Arc<ProvingKey<Bls12_377>>, Arc<VerifyingKey<Bls12_377>>)>>,
> = Lazy::new(|| Mutex::new(None));

/// Load the Groth16 proving/verifying keys for the Full STARK verifier circuit, caching them on disk.
pub fn get_or_init_inner_crs_keys() -> (Arc<ProvingKey<Bls12_377>>, Arc<VerifyingKey<Bls12_377>>) {
    let mut guard = INNER_CRS_KEYS.lock().unwrap();
    if let Some((pk, vk)) = guard.as_ref() {
        return (Arc::clone(pk), Arc::clone(vk));
    }

    let (pk, vk) = load_or_build_inner_crs_keys();
    let pk_arc = Arc::new(pk);
    let vk_arc = Arc::new(vk);
    *guard = Some((Arc::clone(&pk_arc), Arc::clone(&vk_arc)));
    (pk_arc, vk_arc)
}

fn load_or_build_inner_crs_keys() -> (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) {
    if Path::new(INNER_CRS_CACHE).exists() {
        let file = File::open(INNER_CRS_CACHE).expect("failed to open cached inner CRS keys");
        let reader = BufReader::new(file);
        let (pk, vk): (ProvingKey<Bls12_377>, VerifyingKey<Bls12_377>) =
            CanonicalDeserialize::deserialize_uncompressed_unchecked(reader)
                .expect("failed to deserialize inner CRS keys");
        return (pk, vk);
    }

    // Use Aggregator STARK flow for the inner CRS
    // This ensures all app STARKs (VDF, CubicFib, etc.) go through the same Aggregator
    // The Aggregator has FIXED structure, making the quotient gap linear!
    let instance = build_vdf_recursive_stark_instance(3, 8);
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) =
        Groth16::<Bls12_377>::circuit_specific_setup(instance.circuit.clone(), &mut rng).unwrap();

    let file = File::create(INNER_CRS_CACHE).expect("failed to create inner CRS cache file");
    let mut writer = BufWriter::new(file);
    let serialized = (pk.clone(), vk.clone());
    serialized
        .serialize_uncompressed(&mut writer)
        .expect("failed to serialize STARK SNARK keys");
    writer.flush().expect("failed to flush STARK SNARK cache");

    (pk, vk)
}

/// Convenience wrapper that packages a Winterfell VDF proof into a Groth16-ready circuit.
#[derive(Clone)]
pub struct VdfStarkInstance {
    pub circuit: FullStarkVerifierCircuit,
    pub statement_hash: StarkInnerFr,
}

impl VdfStarkInstance {
    pub fn statement(&self) -> StarkInnerFr {
        self.statement_hash
    }
}

pub fn build_vdf_stark_instance(start_value: u64, steps: usize) -> VdfStarkInstance {
    let start = BaseElement::new(start_value);
    let (proof, trace) = generate_test_vdf_proof_rpo(start, steps);
    build_instance_from_proof::<VdfAir>(proof, trace)
}

pub fn build_cubic_fib_stark_instance(start_a: u64, start_b: u64, steps: usize) -> VdfStarkInstance {
    let a = BaseElement::new(start_a);
    let b = BaseElement::new(start_b);
    let (proof, trace) = generate_test_cubic_fib_proof_rpo(a, b, steps);
    build_instance_from_proof::<CubicFibAir>(proof, trace)
}

// ============================================================================
// AGGREGATOR STARK FLOW
// ============================================================================

/// Extract statement hash from an application STARK proof
/// This binds the application's public inputs and commitments to the Aggregator
fn extract_app_statement_hash<A: Air<BaseField = BaseElement>>(
    proof: &Proof,
    result: BaseElement,
) -> [BaseElement; 4] {
    let num_fri_layers = proof
        .options()
        .to_fri_options()
        .num_fri_layers(proof.context.lde_domain_size());

    let (trace_commitments, constraint_commitment, _) = proof
        .commitments
        .clone()
        .parse::<Rp64_256>(proof.context.trace_info().num_segments(), num_fri_layers)
        .expect("parse commitments");

    let trace_root = trace_commitments[0].as_bytes();
    let constraint_root = constraint_commitment.as_bytes();

    let mut hash = [BaseElement::ZERO; 4];
    
    // Element 0: Application result
    hash[0] = result;
    
    // Elements 1-3: Commitment bytes packed into field elements
    let mut bytes8 = [0u8; 8];
    bytes8.copy_from_slice(&trace_root[0..8]);
    hash[1] = BaseElement::new(u64::from_le_bytes(bytes8));
    bytes8.copy_from_slice(&trace_root[8..16]);
    hash[2] = BaseElement::new(u64::from_le_bytes(bytes8));
    bytes8.copy_from_slice(&constraint_root[0..8]);
    hash[3] = BaseElement::new(u64::from_le_bytes(bytes8));

    hash
}


/// Build an Aggregator STARK circuit with configurable trace length
/// 
/// This is useful for testing different FRI layer configurations.
/// Returns the circuit directly (not wrapped in VdfStarkInstance).
pub fn build_aggregator_circuit_with_trace_len(
    trace_len: usize,
) -> FullStarkVerifierCircuit {
    // Create custom config with the specified trace length
    let mut config = default_aggregator_config();
    config.trace_len = trace_len;
    
    // Scale queries for larger traces to ensure enough FRI layers
    if trace_len > 64 {
        config.num_queries = 8;
    } else if trace_len > 8 {
        config.num_queries = 4;
    }
    
    build_aggregator_circuit_with_config(&config)
}

/// Build an Aggregator STARK circuit with custom config
pub fn build_aggregator_circuit_with_config(
    config: &AggregatorConfig,
) -> FullStarkVerifierCircuit {
    // Create simple app statement hash
    let app_statement_hash = [
        BaseElement::new(1),
        BaseElement::new(2),
        BaseElement::new(3),
        BaseElement::new(4),
    ];
    
    let options = config.to_proof_options();
    
    let (proof, result, _) = 
        generate_aggregator_proof(app_statement_hash, config.trace_len, options.clone())
            .expect("Aggregator proof failed");
    
    // Verify Aggregator proof is valid
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![options]);
    winterfell::verify::<AggregatorAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        proof.clone(),
        result,
        &acceptable,
    )
    .expect("Aggregator verification failed");
    
    build_aggregator_instance(proof, result).circuit
}

/// Build a Groth16-ready instance from an Aggregator STARK proof
pub fn build_aggregator_instance(
    proof: Proof,
    pub_inputs: super::aggregator_air::AggregatorPublicInputs,
) -> VdfStarkInstance {
    let trace_len = proof.context.trace_info().length();
    let lde_domain_size = proof.context.lde_domain_size();
    let num_queries = proof.options().num_queries();
    let trace_width = proof.context.trace_info().main_trace_width();

    // Public inputs: all 13 elements from AggregatorPublicInputs
    // Order: result, children_root[4], initial_state[4], final_state[4]
    let pub_inputs_u64: Vec<u64> = pub_inputs.to_elements()
        .iter()
        .map(|e| e.as_int())
        .collect();
    
    // Create AIR to get domain parameters
    let air = AggregatorAir::new(
        proof.context.trace_info().clone(),
        pub_inputs,
        proof.options().clone(),
    );

    let lde_generator = air.lde_domain_generator().as_int();
    let domain_offset = air.domain_offset().as_int();
    let g_trace = air.trace_domain_generator().as_int();

    let coeffs_len = proof
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

    use super::AGGREGATOR_VERSION;

    let comp_width = air.context().num_constraint_composition_columns();
    let num_constraints = proof.context.num_constraints();
    let fri_num_layers = proof
        .options()
        .to_fri_options()
        .num_fri_layers(lde_domain_size);

    let air_params = AirParams {
        trace_width,
        comp_width,
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: 2,
        fri_num_layers,
        lde_generator,
        domain_offset,
        g_lde: lde_generator,
        g_trace,
        combiner_kind: CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: num_constraints,
        grinding_factor: proof.options().grinding_factor(),
        aggregator_version: AGGREGATOR_VERSION,
    };

    let query_positions = derive_query_positions::<Rp64_256, _>(&proof, &air, &pub_inputs);

    let circuit = parse_proof_for_circuit_with_query_positions::<Rp64_256, MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    );

    VdfStarkInstance {
        statement_hash: circuit.statement_hash,
        circuit,
    }
}

fn build_instance_from_proof<A>(
    proof: Proof,
    trace: winterfell::TraceTable<BaseElement>,
) -> VdfStarkInstance
where
    A: Air<BaseField = BaseElement, PublicInputs = BaseElement>,
{
    let trace_len = proof.context.trace_info().length();
    let lde_domain_size = proof.context.lde_domain_size();
    let num_queries = proof.options().num_queries();
    let trace_width = proof.context.trace_info().main_trace_width();

    let pub_inputs_u64 = vec![trace.get(1, trace.length() - 1).as_int()];
    let pub_inputs_fe = BaseElement::new(pub_inputs_u64[0]);
    let air = A::new(
        proof.context.trace_info().clone(),
        pub_inputs_fe,
        proof.options().clone(),
    );

    let lde_generator_from_air = air.lde_domain_generator().as_int();
    let domain_offset_from_air = air.domain_offset().as_int();
    let g_trace_from_air = air.trace_domain_generator().as_int();

    let coeffs_len = proof
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

    // In recursive STARK architecture, the Groth16 circuit only verifies
    // the aggregator STARK, so we use the fixed aggregator version
    use super::AGGREGATOR_VERSION;

    let air_params = AirParams {
        trace_width,
        comp_width: air.context().num_constraint_composition_columns(),
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: 2,
        fri_num_layers: proof
            .options()
            .to_fri_options()
            .num_fri_layers(lde_domain_size),
        lde_generator: lde_generator_from_air,
        domain_offset: domain_offset_from_air,
        g_lde: lde_generator_from_air,
        g_trace: g_trace_from_air,
        combiner_kind: CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: proof.context.num_constraints(),
        grinding_factor: proof.options().grinding_factor(),
        aggregator_version: AGGREGATOR_VERSION,
    };

    let acceptable_options =
        winterfell::AcceptableOptions::OptionSet(vec![proof.options().clone()]);
    winterfell::verify::<A, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        proof.clone(),
        pub_inputs_fe,
        &acceptable_options,
    )
    .expect("Winterfell verification failed");

    let query_positions = derive_query_positions::<Rp64_256, _>(&proof, &air, &pub_inputs_fe);

    let circuit = parse_proof_for_circuit_with_query_positions::<Rp64_256, MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    );

    VdfStarkInstance {
        statement_hash: circuit.statement_hash,
        circuit,
    }
}

// ============================================================================
// RECURSIVE STARK FLOW (App → Aggregator → Verifier STARK → Groth16)
// ============================================================================

/// Build a VDF instance using the full recursive STARK pipeline:
/// VDF STARK → Aggregator STARK → Verifier STARK → Groth16
///
/// Uses test configs for speed. For production, use `build_vdf_recursive_stark_instance_production`.
pub fn build_vdf_recursive_stark_instance(start_value: u64, steps: usize) -> VdfStarkInstance {
    use super::verifier_air::aggregator_integration::RecursiveConfig;
    build_vdf_recursive_stark_instance_with_config(start_value, steps, RecursiveConfig::test())
}

/// Build a VDF instance using production configs (128-bit security)
pub fn build_vdf_recursive_stark_instance_production(start_value: u64, steps: usize) -> VdfStarkInstance {
    use super::verifier_air::aggregator_integration::RecursiveConfig;
    build_vdf_recursive_stark_instance_with_config(start_value, steps, RecursiveConfig::production_128bit())
}

/// Build a VDF instance with meaningful FRI layers for testing FRI verification
/// 
/// Uses larger trace (256 rows) to generate actual FRI folding rounds.
/// This tests the complete FRI verification path in VerifierAir.
pub fn build_vdf_recursive_stark_instance_with_fri(start_value: u64, steps: usize) -> VdfStarkInstance {
    use super::verifier_air::aggregator_integration::RecursiveConfig;
    build_vdf_recursive_stark_instance_with_config(start_value, steps, RecursiveConfig::test_with_fri())
}

/// Build a VDF instance with custom RecursiveConfig
fn build_vdf_recursive_stark_instance_with_config(
    start_value: u64, 
    steps: usize,
    recursive_config: super::verifier_air::aggregator_integration::RecursiveConfig,
) -> VdfStarkInstance {
    use super::verifier_stark_groth16::prove_verifier_stark;
    
    // Step 1: Generate VDF STARK proof
    let start = BaseElement::new(start_value);
    let vdf_trace = build_vdf_trace(start, steps);
    
    let vdf_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    
    let vdf_prover = VdfProver::<Rp64_256>::new(vdf_options.clone());
    let vdf_proof = vdf_prover.prove(vdf_trace.clone()).expect("VDF proof failed");
    let vdf_result = vdf_trace.get(1, vdf_trace.length() - 1);
    
    // Verify VDF proof
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![vdf_options]);
    winterfell::verify::<VdfAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        vdf_proof.clone(),
        vdf_result,
        &acceptable,
    )
    .expect("VDF verification failed");
    
    // Step 2: Extract statement hash from VDF proof
    let app_statement_hash = extract_app_statement_hash::<VdfAir>(&vdf_proof, vdf_result);
    
    // Step 3: Generate Aggregator STARK proof (uses config from RecursiveConfig)
    let agg_config = &recursive_config.aggregator_config;
    let agg_options = agg_config.to_proof_options();
    let (agg_proof, agg_pub_inputs, _) = 
        generate_aggregator_proof(app_statement_hash, agg_config.trace_len, agg_options.clone())
            .expect("Aggregator proof failed");
    
    // Step 4: Generate Verifier STARK proof (recursive STARK)
    let verifier_result = prove_verifier_stark(&agg_proof, &agg_pub_inputs, recursive_config)
        .expect("Verifier STARK proof failed");
    
    VdfStarkInstance {
        statement_hash: verifier_result.statement_hash,
        circuit: verifier_result.circuit,
    }
}

// ============================================================================
// VERIFYING AGGREGATOR FLOW (2 App proofs → Verifying Aggregator → Groth16)
// ============================================================================

/// Build a verifying aggregator instance that ACTUALLY VERIFIES 2 VDF proofs
/// 
/// Architecture:
/// ```text
/// VDF STARK 0 ─┐
///              ├─→ Verifying Aggregator (verifies both in AIR) ──→ Groth16
/// VDF STARK 1 ─┘
/// ```
/// 
/// The Aggregator's trace contains the VERIFICATION of both VDF proofs,
/// so OOD evaluation uses VerifierAir constraints (not VDF constraints).
pub fn build_verifying_aggregator_instance(
    start0: u64, steps0: usize,
    start1: u64, steps1: usize,
) -> VdfStarkInstance {
    use super::verifier_air::VerifierAir;
    
    // Step 1: Generate first VDF proof
    let vdf0_start = BaseElement::new(start0);
    let vdf0_trace = build_vdf_trace(vdf0_start, steps0);
    let vdf0_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let vdf0_prover = VdfProver::<Rp64_256>::new(vdf0_options.clone());
    let vdf0_proof = vdf0_prover.prove(vdf0_trace.clone()).expect("VDF 0 proof failed");
    let vdf0_result = vdf0_trace.get(1, vdf0_trace.length() - 1);
    
    // Verify VDF 0
    let acceptable0 = winterfell::AcceptableOptions::OptionSet(vec![vdf0_options.clone()]);
    winterfell::verify::<VdfAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        vdf0_proof.clone(),
        vdf0_result,
        &acceptable0,
    ).expect("VDF 0 verification failed");
    
    // Step 2: Generate second VDF proof
    let vdf1_start = BaseElement::new(start1);
    let vdf1_trace = build_vdf_trace(vdf1_start, steps1);
    let vdf1_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let vdf1_prover = VdfProver::<Rp64_256>::new(vdf1_options.clone());
    let vdf1_proof = vdf1_prover.prove(vdf1_trace.clone()).expect("VDF 1 proof failed");
    let vdf1_result = vdf1_trace.get(1, vdf1_trace.length() - 1);
    
    // Verify VDF 1
    let acceptable1 = winterfell::AcceptableOptions::OptionSet(vec![vdf1_options.clone()]);
    winterfell::verify::<VdfAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        vdf1_proof.clone(),
        vdf1_result,
        &acceptable1,
    ).expect("VDF 1 verification failed");
    
    // Step 3: Parse proofs for the verifying aggregator
    let parsed0 = parse_proof::<VdfAir>(&vdf0_proof, &vdf0_result);
    let parsed1 = parse_proof::<VdfAir>(&vdf1_proof, &vdf1_result);
    
    // Step 4: Generate Verifying Aggregator proof
    // This proof uses VerifierAir constraints (27 columns)
    // NOTE: VerifierAir has degree-7 constraints (RPO S-box), so needs blowup >= 64
    let agg_options = ProofOptions::new(
        2, 64, 0,  // blowup=64 for degree-7 constraints
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    let (agg_proof, agg_pub_inputs, _agg_trace) = 
        generate_verifying_aggregator_proof(&parsed0, &parsed1, agg_options.clone())
            .expect("Verifying Aggregator proof failed");
    
    // Verify the aggregator proof (sanity check)
    let acceptable_agg = winterfell::AcceptableOptions::OptionSet(vec![agg_options]);
    winterfell::verify::<VerifierAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    ).expect("Verifying Aggregator verification failed");
    
    // Step 5: Build the Groth16 circuit
    // This circuit verifies the VerifierAir proof (NOT VdfAir!)
    build_verifier_air_instance(agg_proof, agg_pub_inputs)
}

/// Build a Groth16 instance from a VerifierAir proof
fn build_verifier_air_instance(
    proof: Proof,
    pub_inputs: super::verifier_air::VerifierPublicInputs,
) -> VdfStarkInstance {
    use super::verifier_air::VerifierAir;
    
    let trace_len = proof.context.trace_info().length();
    let lde_domain_size = proof.context.lde_domain_size();
    let num_queries = proof.options().num_queries();
    let trace_width = proof.context.trace_info().main_trace_width();
    
    // Create AIR for domain parameters
    let air = VerifierAir::new(
        proof.context.trace_info().clone(),
        pub_inputs.clone(),
        proof.options().clone(),
    );
    
    let lde_generator = air.lde_domain_generator().as_int();
    let domain_offset = air.domain_offset().as_int();
    let g_trace = air.trace_domain_generator().as_int();
    
    let coeffs_len = proof
        .fri_proof
        .clone()
        .parse_remainder::<BaseElement>()
        .map(|v: Vec<BaseElement>| v.len())
        .unwrap_or(0);
    let fri_terminal = if coeffs_len == 0 {
        FriTerminalKind::Constant
    } else {
        FriTerminalKind::Poly { degree: coeffs_len - 1 }
    };
    
    // Use same version constant (circuit format indicator)
    use super::AGGREGATOR_VERSION;
    
    let comp_width = air.context().num_constraint_composition_columns();
    let num_constraints = proof.context.num_constraints();
    let fri_num_layers = proof
        .options()
        .to_fri_options()
        .num_fri_layers(lde_domain_size);
    
    let air_params = AirParams {
        trace_width,
        comp_width,
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: 2,
        fri_num_layers,
        lde_generator,
        domain_offset,
        g_lde: lde_generator,
        g_trace,
        combiner_kind: CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: num_constraints,
        grinding_factor: proof.options().grinding_factor(),
        aggregator_version: AGGREGATOR_VERSION,
    };
    
    // Convert public inputs to u64 for circuit
    let pub_inputs_u64: Vec<u64> = pub_inputs.to_elements()
        .iter()
        .map(|e| e.as_int())
        .collect();
    
    let query_positions = derive_query_positions::<Rp64_256, _>(&proof, &air, &pub_inputs);
    
    let circuit = parse_proof_for_circuit_with_query_positions::<Rp64_256, MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    );
    
    VdfStarkInstance {
        statement_hash: circuit.statement_hash,
        circuit,
    }
}

/// Build a CubicFib instance using the full recursive STARK pipeline:
/// CubicFib STARK → Aggregator STARK → Verifier STARK → Groth16
///
/// Uses test configs for speed. For production, use `build_cubic_fib_recursive_stark_instance_production`.
pub fn build_cubic_fib_recursive_stark_instance(a: u64, b: u64, steps: usize) -> VdfStarkInstance {
    use super::verifier_air::aggregator_integration::RecursiveConfig;
    build_cubic_fib_recursive_stark_instance_with_config(a, b, steps, RecursiveConfig::test())
}

/// Build a CubicFib instance using production configs (128-bit security)
pub fn build_cubic_fib_recursive_stark_instance_production(a: u64, b: u64, steps: usize) -> VdfStarkInstance {
    use super::verifier_air::aggregator_integration::RecursiveConfig;
    build_cubic_fib_recursive_stark_instance_with_config(a, b, steps, RecursiveConfig::production_128bit())
}

/// Build a CubicFib instance with custom RecursiveConfig
fn build_cubic_fib_recursive_stark_instance_with_config(
    a: u64, 
    b: u64, 
    steps: usize,
    recursive_config: super::verifier_air::aggregator_integration::RecursiveConfig,
) -> VdfStarkInstance {
    use super::tests::helpers::cubic_fib::{build_cubic_fib_trace, CubicFibProver};
    use super::verifier_stark_groth16::prove_verifier_stark;
    
    // Step 1: Generate CubicFib STARK proof
    let a_elem = BaseElement::new(a);
    let b_elem = BaseElement::new(b);
    let fib_trace = build_cubic_fib_trace(a_elem, b_elem, steps);
    
    let fib_options = ProofOptions::new(
        2, 8, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );
    
    let fib_prover = CubicFibProver::<Rp64_256>::new(fib_options.clone());
    let fib_proof = fib_prover.prove(fib_trace.clone()).expect("CubicFib proof failed");
    let fib_result = fib_trace.get(1, fib_trace.length() - 1);
    
    // Verify CubicFib proof
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![fib_options]);
    winterfell::verify::<CubicFibAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        fib_proof.clone(),
        fib_result,
        &acceptable,
    )
    .expect("CubicFib verification failed");
    
    // Step 2: Extract statement hash from CubicFib proof
    let app_statement_hash = extract_app_statement_hash::<CubicFibAir>(&fib_proof, fib_result);
    
    // Step 3: Generate Aggregator STARK proof (uses config from RecursiveConfig)
    let agg_config = &recursive_config.aggregator_config;
    let agg_options = agg_config.to_proof_options();
    let (agg_proof, agg_pub_inputs, _) = 
        generate_aggregator_proof(app_statement_hash, agg_config.trace_len, agg_options.clone())
            .expect("Aggregator proof failed");
    
    // Step 4: Generate Verifier STARK proof (recursive STARK)
    let verifier_result = prove_verifier_stark(&agg_proof, &agg_pub_inputs, recursive_config)
        .expect("Verifier STARK proof failed");
    
    VdfStarkInstance {
        statement_hash: verifier_result.statement_hash,
        circuit: verifier_result.circuit,
    }
}
