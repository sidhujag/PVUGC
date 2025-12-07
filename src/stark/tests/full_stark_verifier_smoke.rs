use crate::outer_compressed::{cycles::Bls12Bw6Cycle, RecursionCycle};
use crate::stark::inner_stark_full::AirParams;
use crate::stark::stark_proof_parser::parse_proof_for_circuit_with_query_positions;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use winter_crypto::hashers::Rp64_256; // RPO-256 hasher
use winter_math::fields::f64::BaseElement;
use winterfell::{Air, Trace};

use super::helpers::simple_vdf::{generate_test_vdf_proof_rpo, VdfAir};

#[test]
fn full_stark_verifier_smoke() {
    // 1) Generate a real Winterfell STARK proof with RPO-256 hasher
    let start = BaseElement::new(3);
    let steps = 8;
    let (proof, trace): (winterfell::Proof, winterfell::TraceTable<BaseElement>) =
        generate_test_vdf_proof_rpo(start, steps);

    run_full_stark_verifier(proof, trace);
}

type StarkCycle = Bls12Bw6Cycle;
type StarkInnerE = <StarkCycle as RecursionCycle>::InnerE;

fn run_full_stark_verifier(proof: winterfell::Proof, trace: winterfell::TraceTable<BaseElement>) {
    // 2) Set up AIR parameters (must match what proof actually contains!)
    let proof_options = proof.options();

    let trace_len = proof.context.trace_info().length();
    let lde_domain_size = proof.context.lde_domain_size();
    let num_queries = proof_options.num_queries();

    // Get actual widths from proof context
    let trace_width = proof.context.trace_info().main_trace_width();

    // Create AIR early to get correct domain parameters
    let pub_inputs_u64 = vec![trace.get(1, trace.length() - 1).as_int()];
    let pub_inputs_fe = BaseElement::new(pub_inputs_u64[0]);
    let air = VdfAir::new(
        proof.context.trace_info().clone(),
        pub_inputs_fe,
        proof.options().clone(),
    );

    // Get domain parameters from AIR (NOT from manual calculation!)
    let lde_generator_from_air = air.lde_domain_generator().as_int();
    let domain_offset_from_air = air.domain_offset().as_int();
    let g_trace_from_air = air.trace_domain_generator().as_int();

    // Determine FRI terminal kind
    let coeffs_len = proof
        .fri_proof
        .clone()
        .parse_remainder::<BaseElement>()
        .map(|v: Vec<BaseElement>| v.len())
        .unwrap_or(0);
    let fri_terminal = if coeffs_len == 0 {
        crate::stark::gadgets::fri::FriTerminalKind::Constant
    } else {
        crate::stark::gadgets::fri::FriTerminalKind::Poly {
            degree: coeffs_len - 1,
        }
    };

    let air_params = AirParams {
        trace_width,
        comp_width: air.context().num_constraint_composition_columns(),
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: 2,
        fri_num_layers: proof_options
            .to_fri_options()
            .num_fri_layers(lde_domain_size),
        lde_generator: lde_generator_from_air, // From AIR!
        domain_offset: domain_offset_from_air, // From AIR!
        g_lde: lde_generator_from_air,
        g_trace: g_trace_from_air, // Trace domain generator from AIR!
        combiner_kind: crate::stark::gadgets::utils::CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: proof.context.num_constraints(),
        grinding_factor: proof.options().grinding_factor(),
    };

    // 3) Derive query positions using Winterfell's verifier logic

    // FIRST: Verify the proof is valid using Winterfell's own verifier
    // This ensures the proof is well-formed
    use winterfell::{verify, AcceptableOptions};
    let acceptable_options = AcceptableOptions::OptionSet(vec![proof.options().clone()]);
    verify::<
        VdfAir,
        Rp64_256,
        winter_crypto::DefaultRandomCoin<Rp64_256>,
        winter_crypto::MerkleTree<Rp64_256>,
    >(proof.clone(), pub_inputs_fe, &acceptable_options)
    .expect("Winterfell verification failed");

    // Derive query positions
    let query_positions = crate::stark::stark_proof_parser::derive_query_positions::<Rp64_256, _>(
        &proof,
        &air,
        &pub_inputs_fe,
    );

    let num_positions = query_positions.len();

    // Parse proof using RPO-256 with the correct query positions
    let circuit = parse_proof_for_circuit_with_query_positions::<
        Rp64_256,
        winter_crypto::MerkleTree<Rp64_256>,
    >(&proof, pub_inputs_u64, air_params, query_positions);

    // 4) First synthesize once to confirm non-empty CS before Groth16 setup
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    println!("Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    println!("  Queries: {}", num_positions);
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");

    // 5) Generate Groth16 proof (this will measure constraints!)
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) = Groth16::<StarkInnerE>::circuit_specific_setup(circuit.clone(), &mut rng)
        .expect("Groth16 setup");

    // Save public input before moving circuit
    let pub_input = vec![circuit.statement_hash];
    let proof_inner = Groth16::<StarkInnerE>::prove(&pk, circuit, &mut rng).expect("Groth16 prove");

    // 6) Verify
    let valid = Groth16::<StarkInnerE>::verify(&vk, &pub_input, &proof_inner).expect("verify");

    assert!(valid, "Full STARK verifier proof should verify");
}
