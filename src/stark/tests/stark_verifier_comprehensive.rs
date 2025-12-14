///! Comprehensive STARK verifier tests
///!
///! Tests the Groth16 circuit verifying the recursive STARK pipeline (VerifierAir-only):
///! VDF STARK → VerifierAir (verifies VDF) → Groth16
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
/// Uses the full pipeline: VDF → VerifierAir → Groth16
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

    // Enable constraint tracing so `which_is_unsatisfied()` can report a helpful label.
    // Keep the guard alive for the whole test.
    use ark_relations::r1cs::ConstraintLayer;
    use tracing_subscriber::layer::SubscriberExt;
    use tracing_subscriber::Registry;
    let subscriber = Registry::default().with(ConstraintLayer::default());
    let _guard = tracing::subscriber::set_default(subscriber);

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
    let mut mutated = false;
    if let Some(segment) = circuit.trace_segments.get_mut(0) {
        if let Some(first_vec) = segment.batch_nodes.get_mut(0) {
            if let Some(first) = first_vec.get_mut(0) {
                first[0] ^= 0x01;
                mutated = true;
            }
        }
    }
    assert!(mutated, "test did not mutate any trace batch node (unexpected empty witness)");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
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
    let mut had_nodes = false;
    for segment in &mut circuit.trace_segments {
        had_nodes |= !segment.batch_nodes.is_empty();
        segment.batch_nodes.clear();
    }
    assert!(had_nodes, "test did not actually omit any trace batch nodes");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    // Either the circuit rejects the witness during synthesis, or constraints become unsatisfied.
    if res.is_ok() {
        assert!(!cs.is_satisfied().unwrap_or(true));
    } else {
        // rejected early (acceptable)
    }
}

#[test]
#[serial]
fn test_adversarial_omit_comp_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let had_nodes = !circuit.comp_batch_nodes.is_empty();
    circuit.comp_batch_nodes.clear();
    assert!(had_nodes, "test did not actually omit any comp batch nodes");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    if res.is_ok() {
        assert!(!cs.is_satisfied().unwrap_or(true));
    }
}

#[test]
#[serial]
fn test_adversarial_omit_fri_batch_nodes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut had_nodes = false;
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        had_nodes = !layer.batch_nodes.is_empty();
        layer.batch_nodes.clear();
    }
    assert!(had_nodes, "test did not actually omit any FRI batch nodes");
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
    let mut had_values = false;
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        had_values = !layer.unique_values.is_empty();
        layer.unique_values.clear();
    }
    assert!(had_values, "test did not actually omit any FRI unique values");
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
    let mut had_indexes = false;
    if let Some(layer) = circuit.fri_layers.get_mut(0) {
        had_indexes = !layer.unique_indexes.is_empty();
        layer.unique_indexes.clear();
    }
    assert!(had_indexes, "test did not actually omit any FRI unique indexes");
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
    let mut mutated = false;
    if let Some(first_vec) = circuit.comp_batch_nodes.get_mut(0) {
        if let Some(first) = first_vec.get_mut(0) {
            first[0] ^= 0x01;
            mutated = true;
        }
    }
    assert!(mutated, "test did not mutate any comp batch node");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_trace_row_value() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut mutated = false;
    if let Some(segment) = circuit.trace_segments.get_mut(0) {
        if let Some(query) = segment.queries.get_mut(0) {
            if let Some(value) = query.values.get_mut(0) {
                *value ^= 1;
                mutated = true;
            }
        }
    }
    assert!(mutated, "test did not mutate any trace query value");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_comp_row_value() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut mutated = false;
    if let Some(q) = circuit.comp_queries.get_mut(0) {
        if let Some(v) = q.values.get_mut(0) {
            *v ^= 1;
            mutated = true;
        }
    }
    assert!(mutated, "test did not mutate any comp query value");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_ood_values() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut mutated = false;
    if let Some(v) = circuit.ood_trace_current.get_mut(0) {
        *v ^= 1;
        mutated = true;
    }
    if let Some(v) = circuit.ood_comp.get_mut(0) {
        *v ^= 1;
        mutated = true;
    }
    assert!(mutated, "test did not mutate any OOD value");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_trace_root_bytes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut mutated = false;
    if let Some(root) = circuit.trace_commitment_le32.get_mut(0) {
        root[0] ^= 1;
        mutated = true;
    }
    assert!(mutated, "test did not mutate any trace root bytes");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_comp_root_bytes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut mutated = false;
    if let Some(b) = circuit.comp_commitment_le32.get_mut(0) {
        *b ^= 1;
        mutated = true;
    }
    assert!(mutated, "test did not mutate any comp root bytes");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_tamper_fri_root_bytes() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    let mut circuit = build_circuit();
    let mut mutated = false;
    if let Some(root) = circuit.fri_commitments_le32.get_mut(0) {
        root[0] ^= 1;
        mutated = true;
    }
    assert!(mutated, "test did not mutate any FRI root bytes");
    let cs = ConstraintSystem::new_ref();
    let res = circuit.generate_constraints(cs.clone());
    assert!(res.is_ok(), "synthesis should succeed; we want constraints to catch tampering");
        assert!(!cs.is_satisfied().unwrap_or(true));
}

#[test]
#[serial]
fn test_adversarial_missing_fri_layers() {
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem};
    // Build a circuit which MUST have FRI layers.
    // Using 64 steps guarantees non-trivial FRI in this pipeline.
    let mut circuit = build_recursive_circuit_with_steps(64);
    assert!(circuit.air_params.fri_num_layers > 0, "test requires FRI layers");
    assert!(!circuit.fri_layers.is_empty(), "test requires witness FRI layers");

        // Remove FRI layers from witness to attempt bypass
        circuit.fri_layers.clear();
        let cs = ConstraintSystem::new_ref();
        let res = circuit.generate_constraints(cs.clone());
        // With enforced layer count, this should error out during synthesis
        assert!(res.is_err(), "Missing FRI layers should be rejected");
}
