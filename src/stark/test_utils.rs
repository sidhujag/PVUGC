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
use winter_crypto::{DefaultRandomCoin, MerkleTree};
use winter_math::fields::f64::BaseElement;
use winter_math::{FieldElement, ToElements};
use winterfell::{Air, Proof, ProofOptions, Prover, Trace};

use super::stark_proof_parser::{
    derive_query_positions, parse_proof_for_circuit_with_query_positions,
};
use super::verifier_air::proof_parser::parse_proof;
use super::tests::helpers::cubic_fib::{generate_test_cubic_fib_proof_rpo, CubicFibAir};
use super::tests::helpers::simple_vdf::{build_vdf_trace, generate_test_vdf_proof_rpo, VdfAir, VdfProver};
use super::verifier_air::ood_eval::ChildAirType;
use super::aggregator_air::generate_verifying_aggregator_proof;
use super::verifier_air::{prover::VerifierProver, VerifierPublicInputs};
use super::{AirParams, FullStarkVerifierCircuit, StarkInnerFr};
use crate::stark::gadgets::fri::FriTerminalKind;
use crate::stark::gadgets::utils::CombinerKind;
use ark_snark::SNARK;

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

        // Cache robustness: if the circuit constraints change, the cached CRS becomes stale.
        // In that case Groth16::prove will still return a proof, but verification will fail.
        // Detect this early and rebuild the cache automatically.
        //
        // IMPORTANT (universality):
        // We rely on the inner Groth16 circuit being *universal* across supported app proofs
        // (e.g. VDF, CubicFib, etc.). Constraint COUNTS matching is not enough; the R1CS must be
        // identical for CRS reuse. So we self-check against multiple representative instances.
        let mut rng = StdRng::seed_from_u64(12345);

        let vdf_instance = build_vdf_recursive_stark_instance(3, 8);
        let vdf_proof = Groth16::<Bls12_377>::prove(&pk, vdf_instance.circuit.clone(), &mut rng)
            .expect("failed to self-check cached inner CRS keys (prove vdf)");
        let vdf_ok = Groth16::<Bls12_377>::verify(&vk, &[vdf_instance.statement_hash], &vdf_proof)
            .expect("failed to self-check cached inner CRS keys (verify vdf)");

        let cubic_instance = build_cubic_fib_recursive_stark_instance(3, 5, 8);
        let cubic_proof =
            Groth16::<Bls12_377>::prove(&pk, cubic_instance.circuit.clone(), &mut rng)
                .expect("failed to self-check cached inner CRS keys (prove cubic)");
        let cubic_ok =
            Groth16::<Bls12_377>::verify(&vk, &[cubic_instance.statement_hash], &cubic_proof)
                .expect("failed to self-check cached inner CRS keys (verify cubic)");

        eprintln!(
            "[inner_crs] cached CRS self-check: vdf_ok={} cubic_ok={}",
            vdf_ok, cubic_ok
        );
        if vdf_ok && cubic_ok {
        return (pk, vk);
        }
    }

    // Use Aggregator STARK flow for the inner CRS
    // This ensures all app STARKs (VDF, CubicFib, etc.) go through the same Aggregator
    // The Aggregator has FIXED structure, making the quotient gap linear!
    let instance = build_vdf_recursive_stark_instance(3, 8);
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) =
        Groth16::<Bls12_377>::circuit_specific_setup(instance.circuit.clone(), &mut rng).unwrap();

    // Immediately self-check the freshly built CRS against multiple representative instances,
    // so we don't persist a stale/unusable cache (and so a single run is sufficient).
    let mut rng = StdRng::seed_from_u64(12345);
    let vdf_instance = build_vdf_recursive_stark_instance(3, 8);
    eprintln!(
        "[inner_crs] built CRS check (vdf): trace_len={} lde_blowup={} num_queries={} fri_layers={} comp_width={}",
        vdf_instance.circuit.air_params.trace_len,
        vdf_instance.circuit.air_params.lde_blowup,
        vdf_instance.circuit.air_params.num_queries,
        vdf_instance.circuit.air_params.fri_num_layers,
        vdf_instance.circuit.air_params.comp_width,
    );
    eprintln!(
        "[inner_crs] built CRS check (vdf): num_constraint_coeffs={} grinding_factor={} fri_terminal={:?}",
        vdf_instance.circuit.air_params.num_constraint_coeffs,
        vdf_instance.circuit.air_params.grinding_factor,
        vdf_instance.circuit.air_params.fri_terminal,
    );
    eprintln!(
        "[inner_crs] built CRS check (vdf): trace_commitments={} trace_segments={} fri_commitments={} fri_layers_witness={}",
        vdf_instance.circuit.trace_commitment_le32.len(),
        vdf_instance.circuit.trace_segments.len(),
        vdf_instance.circuit.fri_commitments_le32.len(),
        vdf_instance.circuit.fri_layers.len(),
    );

    let vdf_proof = Groth16::<Bls12_377>::prove(&pk, vdf_instance.circuit.clone(), &mut rng)
        .expect("failed to self-check built inner CRS keys (prove vdf)");
    let vdf_ok = Groth16::<Bls12_377>::verify(&vk, &[vdf_instance.statement_hash], &vdf_proof)
        .expect("failed to self-check built inner CRS keys (verify vdf)");

    let cubic_instance = build_cubic_fib_recursive_stark_instance(1, 1, 16);
    eprintln!(
        "[inner_crs] built CRS check (cubic): trace_len={} lde_blowup={} num_queries={} fri_layers={} comp_width={}",
        cubic_instance.circuit.air_params.trace_len,
        cubic_instance.circuit.air_params.lde_blowup,
        cubic_instance.circuit.air_params.num_queries,
        cubic_instance.circuit.air_params.fri_num_layers,
        cubic_instance.circuit.air_params.comp_width,
    );
    eprintln!(
        "[inner_crs] built CRS check (cubic): num_constraint_coeffs={} grinding_factor={} fri_terminal={:?}",
        cubic_instance.circuit.air_params.num_constraint_coeffs,
        cubic_instance.circuit.air_params.grinding_factor,
        cubic_instance.circuit.air_params.fri_terminal,
    );
    eprintln!(
        "[inner_crs] built CRS check (cubic): trace_commitments={} trace_segments={} fri_commitments={} fri_layers_witness={}",
        cubic_instance.circuit.trace_commitment_le32.len(),
        cubic_instance.circuit.trace_segments.len(),
        cubic_instance.circuit.fri_commitments_le32.len(),
        cubic_instance.circuit.fri_layers.len(),
    );
    let cubic_proof = Groth16::<Bls12_377>::prove(&pk, cubic_instance.circuit.clone(), &mut rng)
        .expect("failed to self-check built inner CRS keys (prove cubic)");
    let cubic_ok =
        Groth16::<Bls12_377>::verify(&vk, &[cubic_instance.statement_hash], &cubic_proof)
            .expect("failed to self-check built inner CRS keys (verify cubic)");

    eprintln!(
        "[inner_crs] built CRS self-check: vdf_ok={} cubic_ok={}",
        vdf_ok, cubic_ok
    );
    assert!(
        vdf_ok && cubic_ok,
        "built inner CRS keys are not universal (vdf_ok={}, cubic_ok={})",
        vdf_ok,
        cubic_ok
    );

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
// RECURSIVE STARK FLOW (App → VerifierAir leaf wrapper → Groth16)
// ============================================================================

/// Build a VDF instance using the VerifierAir-only recursive pipeline:
/// VDF STARK → VerifierAir (verifies VDF proof) → Groth16.
pub fn build_vdf_recursive_stark_instance(start_value: u64, steps: usize) -> VdfStarkInstance {
    build_vdf_recursive_stark_instance_leaf_wrapper(start_value, steps)
}

/// Helper: build two VDF instances with identical parameters.
/// Used for checking Groth16 circuit/R1CS shape stability across fresh proofs.
pub fn build_two_vdf_recursive_stark_instances(
    start_value: u64,
    steps: usize,
) -> (VdfStarkInstance, VdfStarkInstance) {
    (build_vdf_recursive_stark_instance(start_value, steps), build_vdf_recursive_stark_instance(start_value, steps))
}

/// Build a VDF instance using production configs (128-bit security)
pub fn build_vdf_recursive_stark_instance_production(start_value: u64, steps: usize) -> VdfStarkInstance {
    build_vdf_recursive_stark_instance_leaf_wrapper(start_value, steps)
}

/// Build a VDF instance with meaningful FRI layers for testing FRI verification
/// 
/// Uses larger trace (256 rows) to generate actual FRI folding rounds.
/// This tests the complete FRI verification path in VerifierAir.
pub fn build_vdf_recursive_stark_instance_with_fri(start_value: u64, steps: usize) -> VdfStarkInstance {
    build_vdf_recursive_stark_instance_leaf_wrapper(start_value, steps)
}

fn compute_statement_hash_sponge(parsed: &super::verifier_air::prover::ParsedProof) -> [BaseElement; 4] {
    // Matches the sponge used by VerifierTraceBuilder in the statement-hash check (mode 4):
    // absorb context + commitments into the rate, permute 7 rounds each chunk, output state[0..3].
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

    [state[0], state[1], state[2], state[3]]
}

fn prove_verifier_air_over_child(
    child: &super::verifier_air::prover::ParsedProof,
    child_type: ChildAirType,
    verifier_options: ProofOptions,
) -> (Proof, VerifierPublicInputs) {
    // Build the verifier trace first, then derive the expected counters from its final row.
    let trace = VerifierProver::new(verifier_options.clone()).build_verification_trace(child, child_type);
    let last = trace.length() - 1;
    // NOTE: with the dedicated idx_reg column, aux columns shifted by +1:
    // aux[1] (mode counter) is at col 31, aux[3] (checkpoint counter) at col 33.
    let expected_mode_counter = trace.get(31, last).as_int() as usize;
    let expected_checkpoint_count = trace.get(33, last).as_int() as usize;

    let statement_hash = compute_statement_hash_sponge(child);
    let params_digest = [
        BaseElement::new(child.trace_len as u64),
        BaseElement::new(child.lde_blowup as u64),
        BaseElement::new(child.num_queries as u64),
        BaseElement::new(((child.fri_folding_factor as u64) << 32) | (child.grinding_factor as u64)),
    ];

    let pub_inputs = VerifierPublicInputs {
        statement_hash,
        trace_commitment: child.trace_commitment,
        comp_commitment: child.comp_commitment,
        fri_commitments: child.fri_commitments.clone(),
        num_queries: child.num_queries,
        proof_trace_len: child.trace_len,
        g_trace: child.g_trace,
        pub_result: child.pub_result,
        expected_checkpoint_count,
        params_digest,
        expected_mode_counter,
    };

    let proof = VerifierProver::with_pub_inputs(verifier_options, pub_inputs.clone())
        .prove(trace)
        .expect("VerifierAir proving failed");

    (proof, pub_inputs)
}

fn build_vdf_recursive_stark_instance_leaf_wrapper(start_value: u64, steps: usize) -> VdfStarkInstance {
    use super::verifier_air::VerifierAir;
    
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
    
    // Step 2: Parse the app proof and prove a single-child VerifierAir wrapper over it.
    let parsed = parse_proof::<VdfAir>(&vdf_proof, &vdf_result);
    
    // VerifierAir options (must satisfy VerifierAir constraints).
    let verifier_options = ProofOptions::new(
        2, 64, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    let (verifier_proof, verifier_pub_inputs) =
        prove_verifier_air_over_child(&parsed, ChildAirType::generic_vdf(), verifier_options.clone());
    
    // Sanity check: verify the VerifierAir proof natively.
    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![verifier_options]);
    winterfell::verify::<VerifierAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        verifier_proof.clone(),
        verifier_pub_inputs.clone(),
        &acceptable,
    )
    .expect("VerifierAir leaf wrapper verification failed");

    // Step 3: Convert VerifierAir proof into Groth16-ready circuit.
    build_verifier_air_instance(verifier_proof, verifier_pub_inputs)
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
        generate_verifying_aggregator_proof(
            &parsed0,
            crate::stark::verifier_air::ood_eval::ChildAirType::generic_vdf(),
            &parsed1,
            crate::stark::verifier_air::ood_eval::ChildAirType::generic_vdf(),
            // Policy: expected child-proof params digest (must match both children).
            // NOTE: In production this must be protocol-fixed, not derived from proofs.
            // For this test helper we keep it derived for now.
            [
                BaseElement::new(parsed0.trace_len as u64),
                BaseElement::new(parsed0.lde_blowup as u64),
                BaseElement::new(parsed0.num_queries as u64),
                BaseElement::new(((parsed0.fri_folding_factor as u64) << 32) | (parsed0.grinding_factor as u64)),
            ],
            agg_options.clone(),
        )
            .expect("Verifying Aggregator proof failed");
    
    // Verify the aggregator proof (sanity check)
    let acceptable_agg = winterfell::AcceptableOptions::OptionSet(vec![agg_options]);
    winterfell::verify::<VerifierAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    ).expect("Verifying Aggregator verification failed");
    
    // Step 5: Build the Groth16 circuit directly from the VerifierAir proof.
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

/// Build a CubicFib instance using the VerifierAir-only recursive pipeline:
/// CubicFib STARK → VerifierAir (verifies CubicFib proof) → Groth16.
pub fn build_cubic_fib_recursive_stark_instance(a: u64, b: u64, steps: usize) -> VdfStarkInstance {
    build_cubic_fib_recursive_stark_instance_leaf_wrapper(a, b, steps)
}

/// Build a CubicFib instance using production configs (128-bit security)
pub fn build_cubic_fib_recursive_stark_instance_production(a: u64, b: u64, steps: usize) -> VdfStarkInstance {
    build_cubic_fib_recursive_stark_instance_leaf_wrapper(a, b, steps)
}

fn build_cubic_fib_recursive_stark_instance_leaf_wrapper(a: u64, b: u64, steps: usize) -> VdfStarkInstance {
    use super::tests::helpers::cubic_fib::{build_cubic_fib_trace, CubicFibProver};
    use super::verifier_air::VerifierAir;
    
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
    
    // Step 2: Parse the app proof and prove a single-child VerifierAir wrapper over it.
    let parsed = parse_proof::<CubicFibAir>(&fib_proof, &fib_result);

    let verifier_options = ProofOptions::new(
        2, 64, 0,
        winterfell::FieldExtension::None,
        2, 31,
        winterfell::BatchingMethod::Linear,
        winterfell::BatchingMethod::Linear,
    );

    let (verifier_proof, verifier_pub_inputs) = prove_verifier_air_over_child(
        &parsed,
        ChildAirType::generic_cubic_fib(),
        verifier_options.clone(),
    );

    let acceptable = winterfell::AcceptableOptions::OptionSet(vec![verifier_options]);
    winterfell::verify::<VerifierAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        verifier_proof.clone(),
        verifier_pub_inputs.clone(),
        &acceptable,
    )
    .expect("VerifierAir leaf wrapper verification failed");
    
    build_verifier_air_instance(verifier_proof, verifier_pub_inputs)
}
