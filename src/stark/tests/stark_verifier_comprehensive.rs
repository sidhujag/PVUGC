///! Comprehensive STARK verifier tests
///!
///! Tests the Groth16 circuit verifying the recursive STARK pipeline:
///! VDF STARK → Aggregator STARK → Verifier STARK → Groth16
///!
///! The Groth16 circuit now verifies VerifierAir (27 columns), which itself
///! verifies Aggregator proofs. Tests are organized as:
///! 1. Positive tests: Valid proofs with different trace sizes
///! 2. Negative tests: Tampered proofs should fail
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
use serial_test::serial;

use crate::stark::test_utils::build_vdf_recursive_stark_instance;

/// Build a valid recursive STARK circuit with specified VDF steps
/// 
/// Uses the full pipeline: VDF → Aggregator → Verifier STARK → Groth16
fn build_recursive_circuit_with_steps(steps: usize) -> crate::stark::inner_stark_full::FullStarkVerifierCircuit {
    build_vdf_recursive_stark_instance(3, steps).circuit
}

/// Build a default recursive STARK circuit for adversarial tests
fn build_circuit() -> crate::stark::inner_stark_full::FullStarkVerifierCircuit {
    build_recursive_circuit_with_steps(8)
}

/// Test that the full recursive STARK pipeline produces a valid circuit
fn test_recursive_verification_with_steps(steps: usize) -> bool {
    eprintln!("\n=== Testing Recursive STARK Pipeline (VDF steps={}) ===", steps);

    let circuit = build_recursive_circuit_with_steps(steps);

    eprintln!("  Trace width: {}", circuit.air_params.trace_width);
    eprintln!("  Trace length: {}", circuit.air_params.trace_len);
    eprintln!("  FRI layers: {}", circuit.air_params.fri_num_layers);

    // Synthesize and check
    let cs = ConstraintSystem::new_ref();
    circuit
        .clone()
        .generate_constraints(cs.clone())
        .expect("generate constraints");
    eprintln!("  Total constraints: {}", cs.num_constraints());

    let is_satisfied = cs.is_satisfied().unwrap_or(false);
    if !is_satisfied {
        let which = cs.which_is_unsatisfied();
        eprintln!("  First failing constraint: {:?}", which);
    }

    is_satisfied
}

// --- Positive tests: different VDF trace sizes ---
// These ensure the pipeline works with varying input complexity

#[test]
#[serial]
fn test_small_trace() {
    // Minimal VDF steps (8 steps)
    assert!(
        test_recursive_verification_with_steps(8),
        "Should verify recursive STARK with small VDF trace"
    );
}

#[test]
#[serial]
fn test_medium_trace() {
    // Medium VDF steps (16 steps)
    assert!(
        test_recursive_verification_with_steps(16),
        "Should verify recursive STARK with medium VDF trace"
    );
}

#[test]
#[serial]
fn test_large_trace() {
    // Larger VDF steps (32 steps)
    assert!(
        test_recursive_verification_with_steps(32),
        "Should verify recursive STARK with larger VDF trace"
    );
}

#[test]
#[serial]
fn test_xlarge_trace() {
    // Even larger VDF steps (64 steps) - more FRI layers expected
    assert!(
        test_recursive_verification_with_steps(64),
        "Should verify recursive STARK with xlarge VDF trace"
    );
}

// --- Negative tests: tamper batch metadata and roots ---

#[test]
#[serial]
fn test_adversarial_tamper_trace_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    // Flip one byte in first trace batch node if exists
    if let Some(segment) = circuit.trace_segments.get_mut(0) {
        if let Some(first_vec) = segment.batch_nodes.get_mut(0) {
            if let Some(first) = first_vec.get_mut(0) {
                first[0] ^= 0x01;
            }
        }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if res.is_ok() {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
    // Err is also acceptable (detected early as Unsatisfiable)
}

#[test]
#[serial]
fn test_adversarial_tamper_fri_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    // Flip one byte in first FRI layer's nodes if exists
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
#[serial]
fn test_adversarial_omit_trace_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    for segment in &mut circuit.trace_segments {
        segment.batch_nodes.clear();
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    } // Err is acceptable (Unsatisfiable)
}

#[test]
#[serial]
fn test_adversarial_omit_comp_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    circuit.comp_batch_nodes.clear();
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_omit_fri_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
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
#[serial]
fn test_adversarial_omit_fri_unique_values() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
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
#[serial]
fn test_adversarial_omit_fri_unique_indexes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
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
#[serial]
fn test_adversarial_wrong_positions_commitment() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
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
#[serial]
fn test_adversarial_low_pow_nonce() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    
    // Build a valid recursive STARK circuit
    let mut circuit = build_circuit();
    
    // Set grinding factor high and corrupt the nonce
    circuit.air_params.grinding_factor = 16;
    circuit.pow_nonce ^= 0xFFFF_FFFF;

    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok());
    // The bad nonce should fail the leading zeros check
    assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_comp_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(first_vec) = circuit.comp_batch_nodes.get_mut(0) {
        if let Some(first) = first_vec.get_mut(0) {
            first[0] ^= 0x01;
        }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_tamper_trace_row_value() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(segment) = circuit.trace_segments.get_mut(0) {
        if let Some(query) = segment.queries.get_mut(0) {
            if let Some(value) = query.values.get_mut(0) {
                *value ^= 1;
            }
        }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_tamper_comp_row_value() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(q) = circuit.comp_queries.get_mut(0) {
        if let Some(v) = q.values.get_mut(0) {
            *v ^= 1;
        }
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_tamper_ood_values() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(v) = circuit.ood_trace_current.get_mut(0) {
        *v ^= 1;
    }
    if let Some(v) = circuit.ood_comp.get_mut(0) {
        *v ^= 1;
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_tamper_trace_root_bytes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(root) = circuit.trace_commitment_le32.get_mut(0) {
        root[0] ^= 1;
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_tamper_comp_root_bytes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(b) = circuit.comp_commitment_le32.get_mut(0) {
        *b ^= 1;
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_tamper_fri_root_bytes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    if let Some(root) = circuit.fri_commitments_le32.get_mut(0) {
        root[0] ^= 1;
    }
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if let Ok(_) = res {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_missing_fri_layers() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    // Check if we actually have FRI layers to clear
    let original_count = circuit.fri_layers.len();
    if original_count > 0 && circuit.air_params.fri_num_layers > 0 {
        // Remove FRI layers from witness to attempt bypass
        circuit.fri_layers.clear();
        let cs = ConstraintSystem::new_ref();
        let res = circuit.generate_constraints(cs.clone());
        // With enforced layer count, this should error out during synthesis
        assert!(res.is_err(), "Missing FRI layers should be rejected");
    }
    // If no FRI layers expected, the test doesn't apply
}
