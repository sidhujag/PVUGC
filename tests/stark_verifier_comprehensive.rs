///! Comprehensive STARK verifier tests
///! 
///! Tests:
///! 1. Different trace sizes (forcing FRI layers > 0)
///! 2. Negative cases (tampered proofs should fail)
///! 3. Different proof parameters

use arkworks_groth16::inner_stark_full::AirParams;
use arkworks_groth16::stark_proof_parser::parse_proof_for_circuit_with_query_positions;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
use winter_crypto::hashers::Rp64_256;
use winter_math::fields::f64::BaseElement;
use winterfell::{Trace, Air};

mod helpers;
use helpers::simple_vdf::{generate_test_vdf_proof_rpo, VdfAir};

fn test_proof_verification(steps: usize, expected_fri_layers: usize) -> bool {
    eprintln!("\n=== Testing with steps={} (expecting {} FRI layers) ===", steps, expected_fri_layers);
    
    let start = BaseElement::new(3);
    let (proof, trace) = generate_test_vdf_proof_rpo(start, steps);
    
    let pub_inputs_u64 = vec![trace.get(1, trace.length() - 1).as_int()];
    let pub_inputs_fe = BaseElement::new(pub_inputs_u64[0]);
    let air = VdfAir::new(proof.context.trace_info().clone(), pub_inputs_fe, proof.options().clone());
    
    // Get domain parameters from AIR
    let lde_domain_size = proof.context.lde_domain_size();
    let trace_len = proof.context.trace_info().length();
    let actual_fri_layers = proof.options().to_fri_options().num_fri_layers(lde_domain_size);
    

    assert_eq!(actual_fri_layers, expected_fri_layers, 
        "FRI layer count mismatch! Expected {}, got {}", expected_fri_layers, actual_fri_layers);
    
    // FIRST: Verify with Winterfell to ensure proof is valid
    use winterfell::{verify, AcceptableOptions};
    let acceptable_options = AcceptableOptions::OptionSet(vec![proof.options().clone()]);
    verify::<VdfAir, Rp64_256, winter_crypto::DefaultRandomCoin<Rp64_256>, winter_crypto::MerkleTree<Rp64_256>>(
        proof.clone(),
        pub_inputs_fe,
        &acceptable_options,
    ).expect("Winterfell verification should pass");

    let air_params = AirParams {
        trace_width: 2,
        comp_width: 0,
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries: proof.options().num_queries(),
        fri_folding_factor: 2,
        fri_num_layers: actual_fri_layers,
        lde_generator: air.lde_domain_generator().as_int(),
        domain_offset: air.domain_offset().as_int(),
        g_lde: air.lde_domain_generator().as_int(),
        g_trace: air.trace_domain_generator().as_int(),
        combiner_kind: arkworks_groth16::gadgets::utils::CombinerKind::RandomRho,
        fri_terminal: {
            let coeffs_len = proof.fri_proof.clone()
                .parse_remainder::<BaseElement>()
                .map(|v: Vec<BaseElement>| v.len())
                .unwrap_or(0);
            if coeffs_len == 0 {
                arkworks_groth16::gadgets::fri::FriTerminalKind::Constant
            } else {
                arkworks_groth16::gadgets::fri::FriTerminalKind::Poly { degree: coeffs_len - 1 }
            }
        },
        num_constraint_coeffs: proof.context.num_constraints(),
    };
    
    // Derive query positions
    use winter_crypto::{ElementHasher, RandomCoin};
    use winter_math::ToElements;
    use winter_crypto::DefaultRandomCoin;
    
    let mut public_coin_seed = proof.context.to_elements();
    public_coin_seed.append(&mut pub_inputs_fe.to_elements());
    let mut public_coin = DefaultRandomCoin::<Rp64_256>::new(&public_coin_seed);
    
    let (trace_commitments, constraint_commitment, fri_commitments) = proof.commitments
        .clone()
        .parse::<Rp64_256>(air.trace_info().num_segments(), actual_fri_layers)
        .expect("parse commitments");
    
    public_coin.reseed(trace_commitments[0]);
    let _ = air.get_constraint_composition_coefficients::<BaseElement, _>(&mut public_coin).unwrap();
    public_coin.reseed(constraint_commitment);
    let _ = public_coin.draw::<BaseElement>().unwrap();
    
    let (trace_ood_frame, constraint_ood_frame) = proof.ood_frame.clone()
        .parse::<BaseElement>(
            air.trace_info().main_trace_width(),
            air.trace_info().aux_segment_width(),
            air.context().num_constraint_composition_columns()
        )
        .unwrap();
    
    use winter_air::proof::merge_ood_evaluations;
    let ood_evals = merge_ood_evaluations(&trace_ood_frame, &constraint_ood_frame);
    public_coin.reseed(Rp64_256::hash_elements(&ood_evals));
    
    let _ = air.get_deep_composition_coefficients::<BaseElement, _>(&mut public_coin).unwrap();
    
    for (i, fri_root) in fri_commitments.iter().enumerate() {
        public_coin.reseed(*fri_root);
        if i < actual_fri_layers {
            let _ = public_coin.draw::<BaseElement>().unwrap();
        }
    }
    
    let mut query_positions = public_coin.draw_integers(
        air.options().num_queries(),
        air.lde_domain_size(),
        proof.pow_nonce,
    ).unwrap();
    query_positions.sort_unstable();
    query_positions.dedup();
    
    let circuit = parse_proof_for_circuit_with_query_positions::<Rp64_256, winter_crypto::MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    );
    
    // Synthesize and check
    let cs = ConstraintSystem::new_ref();
    circuit.clone().generate_constraints(cs.clone()).expect("generate constraints");
    eprintln!("Total constraints: {}", cs.num_constraints());
    
    let is_satisfied = cs.is_satisfied().unwrap_or(false);
    if !is_satisfied {
        let which = cs.which_is_unsatisfied();
        eprintln!("  First failing constraint: {:?}", which);
    }
    
    is_satisfied
}

#[test]
#[ignore]
fn test_fri_no_layers() {
    assert!(test_proof_verification(8, 0), "Should verify proof with 0 FRI layers");
}

#[test]
#[ignore]
fn test_fri_one_layer() {
    // steps=64 gives 1 FRI layer
    assert!(test_proof_verification(64, 1), "Should verify proof with 1 FRI layer");
}

#[test]
#[ignore]
fn test_fri_two_layers() {
    // Need even larger trace for 2+ FRI layers
    assert!(test_proof_verification(128, 2), "Should verify proof with 2 FRI layers");
}

#[test]
#[ignore]
fn test_large_trace() {
    // Very large trace
    assert!(test_proof_verification(256, 3), "Should verify proof with 3 FRI layers");
}

// Negative tests: tamper batch metadata and roots

fn build_circuit(steps: usize, expected_fri_layers: usize) -> arkworks_groth16::inner_stark_full::FullStarkVerifierCircuit {
    use winter_crypto::hashers::Rp64_256;
    use winterfell::{Trace, Air};
    let start = BaseElement::new(3);
    let (proof, trace) = generate_test_vdf_proof_rpo(start, steps);
    let pub_inputs_u64 = vec![trace.get(1, trace.length() - 1).as_int()];
    let pub_inputs_fe = BaseElement::new(pub_inputs_u64[0]);
    let air = VdfAir::new(proof.context.trace_info().clone(), pub_inputs_fe, proof.options().clone());
    let lde_domain_size = proof.context.lde_domain_size();
    let trace_len = proof.context.trace_info().length();
    let actual_fri_layers = proof.options().to_fri_options().num_fri_layers(lde_domain_size);
    assert_eq!(actual_fri_layers, expected_fri_layers);
    let air_params = AirParams {
        trace_width: 2,
        comp_width: 0,
        trace_len,
        lde_blowup: lde_domain_size / trace_len,
        num_queries: proof.options().num_queries(),
        fri_folding_factor: 2,
        fri_num_layers: actual_fri_layers,
        lde_generator: air.lde_domain_generator().as_int(),
        domain_offset: air.domain_offset().as_int(),
        g_lde: air.lde_domain_generator().as_int(),
        g_trace: air.trace_domain_generator().as_int(),
        combiner_kind: arkworks_groth16::gadgets::utils::CombinerKind::RandomRho,
        fri_terminal: {
            let coeffs_len = proof.fri_proof.clone()
                .parse_remainder::<BaseElement>()
                .map(|v: Vec<BaseElement>| v.len())
                .unwrap_or(0);
            if coeffs_len == 0 {
                arkworks_groth16::gadgets::fri::FriTerminalKind::Constant
            } else {
                arkworks_groth16::gadgets::fri::FriTerminalKind::Poly { degree: coeffs_len - 1 }
            }
        },
        num_constraint_coeffs: proof.context.num_constraints(),
    };
    use winter_crypto::{ElementHasher, RandomCoin};
    use winter_math::ToElements;
    use winter_crypto::DefaultRandomCoin;
    let mut public_coin_seed = proof.context.to_elements();
    public_coin_seed.append(&mut pub_inputs_fe.to_elements());
    let mut public_coin = DefaultRandomCoin::<Rp64_256>::new(&public_coin_seed);
    let (trace_commitments, constraint_commitment, fri_commitments) = proof.commitments
        .clone()
        .parse::<Rp64_256>(air.trace_info().num_segments(), actual_fri_layers)
        .expect("parse commitments");
    public_coin.reseed(trace_commitments[0]);
    let _ = air.get_constraint_composition_coefficients::<BaseElement, _>(&mut public_coin).unwrap();
    public_coin.reseed(constraint_commitment);
    let _ = public_coin.draw::<BaseElement>().unwrap();
    let (trace_ood_frame, constraint_ood_frame) = proof.ood_frame.clone()
        .parse::<BaseElement>(
            air.trace_info().main_trace_width(),
            air.trace_info().aux_segment_width(),
            air.context().num_constraint_composition_columns()
        )
        .unwrap();
    use winter_air::proof::merge_ood_evaluations;
    let ood_evals = merge_ood_evaluations(&trace_ood_frame, &constraint_ood_frame);
    public_coin.reseed(Rp64_256::hash_elements(&ood_evals));
    let _ = air.get_deep_composition_coefficients::<BaseElement, _>(&mut public_coin).unwrap();
    for (i, fri_root) in fri_commitments.iter().enumerate() {
        public_coin.reseed(*fri_root);
        if i < actual_fri_layers {
            let _ = public_coin.draw::<BaseElement>().unwrap();
        }
    }
    let mut query_positions = public_coin.draw_integers(
        air.options().num_queries(),
        air.lde_domain_size(),
        proof.pow_nonce,
    ).unwrap();
    query_positions.sort_unstable();
    query_positions.dedup();
    parse_proof_for_circuit_with_query_positions::<Rp64_256, winter_crypto::MerkleTree<Rp64_256>>(
        &proof,
        pub_inputs_u64,
        air_params,
        query_positions,
    )
}

#[test]
#[ignore]
fn test_adversarial_tamper_trace_nodes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    // Flip one byte in first trace batch node if exists
    if let Some(first_vec) = circuit.trace_batch_nodes.get_mut(0) {
        if let Some(first) = first_vec.get_mut(0) {
            first[0] ^= 0x01;
        }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok());
    assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[ignore]
fn test_adversarial_tamper_fri_nodes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(128, 2);
    // Flip one byte in first FRI layer's nodes
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        if let Some(first_vec) = layer.batch_nodes.get_mut(0) {
            if let Some(first) = first_vec.get_mut(0) {
                first[0] ^= 0x02;
            }
        }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok());
    assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[ignore]
fn test_adversarial_omit_trace_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    circuit.trace_batch_nodes.clear();
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    } // Err is acceptable (Unsatisfiable)
}

#[test]
#[ignore]
fn test_adversarial_omit_comp_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    circuit.comp_batch_nodes.clear();
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[ignore]
fn test_adversarial_omit_fri_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(128, 2);
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        layer.batch_nodes.clear();
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[ignore]
fn test_adversarial_omit_fri_unique_values() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(128, 2);
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        layer.unique_values.clear();
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[ignore]
fn test_adversarial_omit_fri_unique_indexes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(128, 2);
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        layer.unique_indexes.clear();
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[ignore]
fn test_adversarial_wrong_positions_commitment() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    // Tamper query positions (break binding)
    if let Some(first) = circuit.query_positions.get_mut(0) {
        *first ^= 1usize;
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok());
    assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[ignore]
fn test_adversarial_tamper_comp_nodes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    if let Some(first_vec) = circuit.comp_batch_nodes.get_mut(0) {
        if let Some(first) = first_vec.get_mut(0) { first[0] ^= 0x01; }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

#[test]
#[ignore]
fn test_adversarial_tamper_trace_row_value() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    if let Some(q) = circuit.trace_queries.get_mut(0) { if let Some(v) = q.values.get_mut(0) { *v ^= 1; } }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

#[test]
#[ignore]
fn test_adversarial_tamper_comp_row_value() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    if let Some(q) = circuit.comp_queries.get_mut(0) { if let Some(v) = q.values.get_mut(0) { *v ^= 1; } }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

#[test]
#[ignore]
fn test_adversarial_tamper_ood_values() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    if let Some(v) = circuit.ood_trace_current.get_mut(0) { *v ^= 1; }
    if let Some(v) = circuit.ood_comp.get_mut(0) { *v ^= 1; }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

#[test]
#[ignore]
fn test_adversarial_tamper_trace_root_bytes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    if let Some(b) = circuit.trace_commitment_le32.get_mut(0) { *b ^= 1; }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

#[test]
#[ignore]
fn test_adversarial_tamper_comp_root_bytes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(64, 1);
    if let Some(b) = circuit.comp_commitment_le32.get_mut(0) { *b ^= 1; }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

#[test]
#[ignore]
fn test_adversarial_tamper_fri_root_bytes() {
    use ark_relations::r1cs::{ConstraintSystem, ConstraintSynthesizer};
    let mut circuit = build_circuit(128, 2);
    if let Some(root) = circuit.fri_commitments_le32.get_mut(0) { root[0] ^= 1; }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res { assert!(!cs.is_satisfied().unwrap_or(true)); }
}

