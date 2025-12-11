//! Full STARK Verifier Smoke Test
//!
//! Tests the complete pipeline:
//! VDF STARK → Aggregator STARK → Groth16
//! VDF STARK (×2) → Verifying Aggregator → Groth16

use crate::outer_compressed::{cycles::Bls12Bw6Cycle, RecursionCycle};
use crate::stark::test_utils::{
    build_vdf_recursive_stark_instance,
    build_vdf_recursive_stark_instance_with_fri,
    build_verifying_aggregator_instance,
    get_or_init_inner_crs_keys,
};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;

type StarkCycle = Bls12Bw6Cycle;
type StarkInnerE = <StarkCycle as RecursionCycle>::InnerE;

/// Debug test to identify which constraint fails with FRI layers
#[test]
#[ignore]
fn debug_verifier_air_constraints_with_fri() {
    use crate::stark::aggregator_air::{
        AggregatorConfig, generate_aggregator_proof,
    };
    use crate::stark::verifier_air::{
        aggregator_integration::{RecursiveConfig, run_recursive_pipeline},
        constraints::evaluate_all,
        VERIFIER_TRACE_WIDTH,
    };
    use crate::stark::tests::helpers::simple_vdf::{
        build_vdf_trace, VdfAir, VdfProver,
    };
    use winter_crypto::hashers::Rp64_256;
    use winter_crypto::{DefaultRandomCoin, MerkleTree};
    use winterfell::{
        math::{fields::f64::BaseElement, FieldElement},
        ProofOptions, Prover, Trace, EvaluationFrame,
    };
    
    println!("\n=== DEBUG: VerifierAir Constraint Check with FRI ===\n");
    
    // Step 1: Generate VDF proof
    let start = BaseElement::new(3);
    let vdf_trace = build_vdf_trace(start, 8);
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
    ).expect("VDF verification failed");
    println!("✓ VDF proof verified");
    
    // Step 2: Extract statement hash
    let app_statement_hash = [
        BaseElement::new(1), BaseElement::new(2),
        BaseElement::new(3), BaseElement::new(4),
    ];
    
    // Step 3: Generate Aggregator proof with FRI layers
    let agg_config = AggregatorConfig::test_with_fri();
    println!("Aggregator config: trace_len={}, num_queries={}, fri_max_remainder={}",
        agg_config.trace_len, agg_config.num_queries, agg_config.fri_max_remainder);
    
    let agg_options = agg_config.to_proof_options();
    let (agg_proof, agg_pub_inputs, _) = generate_aggregator_proof(
        app_statement_hash,
        agg_config.trace_len,
        agg_options.clone(),
    ).expect("Aggregator proof failed");
    println!("✓ Aggregator proof generated");
    
    // Verify Aggregator proof
    use crate::stark::aggregator_air::AggregatorAir;
    let acceptable_agg = winterfell::AcceptableOptions::OptionSet(vec![agg_options.clone()]);
    winterfell::verify::<AggregatorAir, Rp64_256, DefaultRandomCoin<Rp64_256>, MerkleTree<Rp64_256>>(
        agg_proof.clone(),
        agg_pub_inputs.clone(),
        &acceptable_agg,
    ).expect("Aggregator verification failed");
    println!("✓ Aggregator proof verified by Winterfell");
    
    // Parse proof to check FRI layers
    use crate::stark::verifier_air::proof_parser::parse_proof;
    let parsed = parse_proof::<AggregatorAir>(&agg_proof, &agg_pub_inputs);
    println!("Parsed proof: num_fri_layers={}, fri_layers.len()={}", 
        parsed.num_fri_layers, parsed.fri_layers.len());
    assert!(parsed.num_fri_layers > 0, "Must have FRI layers for this test!");
    assert_eq!(parsed.fri_layers.len(), parsed.num_fri_layers, "FRI layers count mismatch");
    
    // Step 4: Build VerifierAir trace
    let recursive_config = RecursiveConfig::test_with_fri();
    let pipeline_result = run_recursive_pipeline(
        &agg_proof,
        &agg_pub_inputs,
        recursive_config.clone(),
    );
    
    let trace = &pipeline_result.verifier_trace;
    let trace_len = trace.length();
    println!("✓ VerifierAir trace built: {} rows x {} columns", trace_len, trace.width());
    
    // Step 5: Check each constraint at each row
    let mut constraint_results = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
    let mut failing_rows: Vec<(usize, Vec<usize>)> = Vec::new();
    
    for row in 0..trace_len - 1 {
        // Build evaluation frame
        let mut current_row = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        let mut next_row = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        
        for col in 0..VERIFIER_TRACE_WIDTH {
            current_row[col] = trace.get(col, row);
            next_row[col] = trace.get(col, row + 1);
        }
        
        let frame = EvaluationFrame::from_rows(current_row.clone(), next_row.clone());
        
        // Evaluate constraints
        let periodic_values: Vec<BaseElement> = vec![]; // Empty for now
        evaluate_all(&frame, &periodic_values, &mut constraint_results, &pipeline_result.verifier_pub_inputs);
        
        // Check which constraints fail
        let mut row_failures: Vec<usize> = Vec::new();
        for (i, &result) in constraint_results.iter().enumerate() {
            if result != BaseElement::ZERO {
                row_failures.push(i);
            }
        }
        
        if !row_failures.is_empty() {
            failing_rows.push((row, row_failures.clone()));
            
            // Print first few failures in detail
            if failing_rows.len() <= 5 {
                println!("\n--- Row {} failing constraints: {:?} ---", row, row_failures);
                println!("  Current selectors: s0={}, s1={}, s2={}", 
                    current_row[0], current_row[1], current_row[2]);
                println!("  Next selectors: s0={}, s1={}, s2={}", 
                    next_row[0], next_row[1], next_row[2]);
                println!("  aux[0]={}, aux[1]={}, aux[2]={}, aux[3]={}",
                    current_row[23], current_row[24], current_row[25], current_row[26]);
                
                // Print hash state (columns 3-14)
                println!("  Current hash_state[0-3]: {:?}", 
                    &current_row[3..7].iter().map(|x| x.as_int()).collect::<Vec<_>>());
                // Print FRI columns (15-22)
                println!("  Current FRI[0-7]: {:?}", 
                    &current_row[15..23].iter().map(|x| x.as_int()).collect::<Vec<_>>());
                println!("  Next FRI[0-7]: {:?}", 
                    &next_row[15..23].iter().map(|x| x.as_int()).collect::<Vec<_>>());
                
                for &fail_idx in &row_failures {
                    println!("  Constraint {} = {:?}", fail_idx, constraint_results[fail_idx]);
                }
            }
        }
    }
    
    if failing_rows.is_empty() {
        println!("\n✅ All constraints satisfied at all rows!");
    } else {
        println!("\n❌ {} rows have failing constraints", failing_rows.len());
        
        // Categorize failures
        let mut constraint_failure_count = vec![0usize; VERIFIER_TRACE_WIDTH];
        for (_, failures) in &failing_rows {
            for &idx in failures {
                constraint_failure_count[idx] += 1;
            }
        }
        
        println!("\nConstraint failure summary:");
        for (idx, count) in constraint_failure_count.iter().enumerate() {
            if *count > 0 {
                let name = match idx {
                    0..=2 => "Selector binary",
                    3..=14 => "Hash state",
                    15..=22 => "FRI/DEEP working",
                    23 => "aux[0] round counter",
                    24 => "aux[1]",
                    25 => "aux[2]",
                    26 => "aux[3] acceptance",
                    _ => "Unknown",
                };
                println!("  Constraint {} ({}): {} failures", idx, name, count);
            }
        }
    }
    
    assert!(failing_rows.is_empty(), "Constraints should be satisfied");
}

#[test]
fn full_stark_verifier_smoke() {
    // Complete pipeline: VDF → Aggregator → Groth16
    
    // 1) Build VDF → Aggregator → Groth16 circuit
    let instance = build_vdf_recursive_stark_instance(3, 8);
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    
    println!("Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    assert!(cs.is_satisfied().unwrap(), "Circuit must be satisfied");

    // Generate Groth16 proof using cached CRS keys
    let mut rng = StdRng::seed_from_u64(42);
    let (pk, vk) = get_or_init_inner_crs_keys();

    let pub_input = vec![instance.statement_hash];
    let proof = Groth16::<StarkInnerE>::prove(&pk, instance.circuit, &mut rng)
        .expect("Groth16 prove");
    // Verify Groth16 proof
    let valid = Groth16::<StarkInnerE>::verify(&vk, &pub_input, &proof).expect("verify");

    assert!(valid, "Full STARK verifier proof should verify");
}

/// Test the FULL STARK verifier with meaningful FRI layers
/// 
/// This is the critical test that verifies FRI folding is actually checked.
/// Uses larger trace (256 rows) to generate ~8 FRI layers.
#[test]
#[ignore] // Takes ~30-60 seconds, run with: cargo test full_stark_verifier_with_fri_smoke --release -- --ignored
fn full_stark_verifier_with_fri_smoke() {
    println!("\n=== Full STARK Verifier with FRI Layers ===\n");
    
    // Build with FRI config (trace_len=256, ~8 FRI layers)
    let instance = build_vdf_recursive_stark_instance_with_fri(3, 8);
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    
    println!("Circuit Statistics (with FRI):");
    println!("  Total Constraints: {}", cs.num_constraints());
    println!("  (Should be significantly larger than no-FRI version due to FRI verification)");
    
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    assert!(cs.is_satisfied().unwrap(), "Circuit with FRI must be satisfied");
    
    // The constraint count should be notably higher due to FRI verification
    // No-FRI version has ~3M constraints, with FRI should be ~5-10M+
    println!("\n✅ Full STARK verifier with FRI layers passed!");
}

/// Test the verifying aggregator pipeline:
/// VDF STARK 0 + VDF STARK 1 → Verifying Aggregator → Groth16
/// 
/// This tests that:
/// 1. The Aggregator ACTUALLY VERIFIES both VDF proofs in its trace
/// 2. The Aggregator proof uses VerifierAir constraints (27 columns)
/// 3. The Groth16 circuit correctly verifies the VerifierAir proof
#[test]
fn verifying_aggregator_smoke() {
    // Two VDF proofs with different parameters
    let instance = build_verifying_aggregator_instance(
        3, 8,   // VDF 0: start=3, steps=8
        7, 8,   // VDF 1: start=7, steps=8
    );
    
    // Synthesize to check constraints
    use ark_relations::r1cs::ConstraintSynthesizer;
    use ark_relations::r1cs::ConstraintSystem;
    let cs = ConstraintSystem::new_ref();
    instance
        .circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    
    println!("Verifying Aggregator Circuit Statistics:");
    println!("  Total Constraints: {}", cs.num_constraints());
    assert!(cs.num_constraints() > 0, "Synthesized CS is empty");
    assert!(cs.is_satisfied().unwrap(), "Verifying Aggregator circuit must be satisfied");
}
