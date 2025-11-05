use arkworks_groth16::inner_stark_full::AirParams;
use arkworks_groth16::stark_proof_parser::parse_proof_for_circuit;
use arkworks_groth16::outer_compressed::InnerE;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use winter_crypto::hashers::Rp64_256;  // RPO-256 hasher
use winter_math::fields::f64::BaseElement;
use winterfell::Trace;

mod helpers;
use helpers::simple_vdf::generate_test_vdf_proof_rpo;

#[test]
#[ignore]  // Expensive test
fn full_stark_verifier_smoke() {
    // 1) Generate a real Winterfell STARK proof with RPO-256 hasher (matches circuit!)
    let start = BaseElement::new(3);
    let steps = 16;
    let (proof, trace): (winterfell::Proof, winterfell::TraceTable<BaseElement>) = generate_test_vdf_proof_rpo(start, steps);
    
    // 2) Set up AIR parameters (must match what proof actually contains!)
    eprintln!("Proof context: {:?}", proof.context);
    let proof_options = proof.options();
    
    let trace_len = proof.context.trace_info().length();
    let lde_domain_size = proof.context.lde_domain_size();
    let num_queries = proof_options.num_queries();
    
    // Get actual widths from proof context
    let trace_width = proof.context.trace_info().main_trace_width();
    
    // Compute g_lde from trace generator
    let lde_generator = 7u64;  // Goldilocks generator
    let g_lde = {
        use winter_math::FieldElement;
        let g = BaseElement::new(lde_generator);
        let g_lde = g.exp((trace_len as u64).into());
        g_lde.as_int()
    };
    
    // Determine FRI terminal kind from proof structure by checking remainder
    let coeffs_len = proof.fri_proof.clone()
        .parse_remainder::<BaseElement>()
        .map(|v: Vec<BaseElement>| v.len())
        .unwrap_or(0);
    let fri_terminal = if coeffs_len == 0 {
        arkworks_groth16::gadgets::fri::FriTerminalKind::Constant
    } else {
        arkworks_groth16::gadgets::fri::FriTerminalKind::Poly { degree: coeffs_len - 1 }
    };
    
    let air_params = AirParams {
        trace_width,
        comp_width: 0,  // Will be auto-detected from proof data
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries,
        fri_folding_factor: 2,
        fri_num_layers: proof_options.to_fri_options().num_fri_layers(lde_domain_size),
        lde_generator,
        domain_offset: 1,  // Standard for Goldilocks
        g_lde,
        combiner_kind: arkworks_groth16::gadgets::combiner::CombinerKind::RandomRho,
        fri_terminal,
        num_constraint_coeffs: proof.context.num_constraints(),
    };
    
    eprintln!("AIR params: trace_len={}, lde_blowup={}, queries={}, fri_layers={}",
        air_params.trace_len, air_params.lde_blowup, air_params.num_queries, air_params.fri_num_layers);
    
    // 3) Parse proof into circuit format
    // NO hooks, NO winterfell modifications!
    let pub_inputs_u64 = vec![trace.get(1, trace.length() - 1).as_int()];
    
    // Parse proof using RPO-256 (matches how proof was generated!)
    let circuit = parse_proof_for_circuit::<Rp64_256, winter_crypto::MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
    );
    
    eprintln!("Parsed proof successfully!");
    eprintln!("  Trace queries: {}", circuit.trace_queries.len());
    eprintln!("  Comp queries: {}", circuit.comp_queries.len());
    eprintln!("  FRI layers: {}", circuit.fri_layers.len());
    eprintln!("  OOD trace current: {} values", circuit.ood_trace_current.len());

    // 4) First synthesize once to confirm non-empty CS before Groth16 setup
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    circuit.clone().generate_constraints(cs.clone()).expect("generate constraints");
    eprintln!("Circuit statistics:");
    eprintln!("  Constraints: {}", cs.num_constraints());
    eprintln!("  Witness variables: {}", cs.num_witness_variables());
    eprintln!("  Instance variables: {}", cs.num_instance_variables());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");

    // 5) Generate Groth16 proof (this will measure constraints!)
    let mut rng = StdRng::seed_from_u64(42);
    eprintln!("Setting up Groth16...");
    let (pk, vk) = Groth16::<InnerE>::circuit_specific_setup(circuit.clone(), &mut rng)
        .expect("Groth16 setup");
    eprintln!("Groth16 setup complete!");
    eprintln!("  VK gamma_abc_g1.len() = {} (public inputs + 1)", vk.gamma_abc_g1.len());
    
    // Save public input before moving circuit
    let pub_input = vec![circuit.statement_hash];
    
    eprintln!("Proving...");
    let proof_inner = Groth16::<InnerE>::prove(&pk, circuit, &mut rng)
        .expect("Groth16 prove");
    
    eprintln!("SUCCESS: Full STARK verifier proof generated!");
    
    // 6) Verify
    let valid = Groth16::<InnerE>::verify(&vk, &pub_input, &proof_inner)
        .expect("verify");
    
    assert!(valid, "Full STARK verifier proof should verify");
    eprintln!("✅ Verification PASSED!");
}

