//! SP1 End-to-End Integration Test
//!
//! This test demonstrates the full flow:
//! 1. SP1 generates a Groth16 proof (using our BLS12-377 fork)
//! 2. sp1_bridge deserializes and computes armed_digest
//! 3. Outer circuit verifies the inner proof
//! 4. PVUGC decap extracts the key
//!
//! **Architecture:**
//! - SP1 SDK generates proofs (calls gnark internally)
//! - sp1_bridge deserializes gnark output → arkworks types
//! - Outer circuit wraps the SP1 proof on BW6-761

use ark_bls12_377::{Bls12_377, Fr as Fr377};
use ark_ff::UniformRand;
use ark_groth16::{prepare_verifying_key, Groth16, Proof};
use ark_std::rand::SeedableRng;
use ark_std::rand::rngs::StdRng;
use sha2::{Digest, Sha256};

use sp1_sdk::{ProverClient, SP1Stdin, HashableKey, Prover};

use arkworks_groth16::sp1_bridge::{
    Sp1PublicInputs,
    decode_sp1_proof_hex,
    decode_sp1_public_input,
    parse_gnark_proof_bls12_377, parse_gnark_vk_bls12_377,
};
use arkworks_groth16::outer_compressed::{
    Bls12Bw6Cycle, OuterCircuit, RecursionCycle, OuterScalar,
    setup_outer_params_for, fr_inner_to_outer_for,
};

/// Simple fibonacci program for SP1
/// This is the ELF binary that SP1 will execute and prove
const FIBONACCI_ELF: &[u8] = test_artifacts::FIBONACCI_ELF;

#[test]
#[ignore] // Run with: cargo test test_sp1_fibonacci_mock -- --ignored
fn test_sp1_fibonacci_mock() {
    println!("\n=== SP1 Fibonacci Mock Test ===\n");
    
    // Create SP1 mock prover (no actual proof generation)
    let client = ProverClient::builder().mock().build();
    
    // Setup input
    let mut stdin = SP1Stdin::new();
    stdin.write(&10u32); // Compute fib(10)
    
    // Execute program in mock mode
    println!("Executing SP1 program (mock mode)...");
    let (_pk, vk) = client.setup(FIBONACCI_ELF);
    
    // Execute to get public values
    let (public_values, _) = client.execute(FIBONACCI_ELF, &stdin).run().expect("execution failed");
    println!("  ✓ Program executed");
    println!("  Public values: {:?}", public_values.as_slice());
    let vk_hash: String = vk.bytes32();
    println!("  VKey hash: {}", vk_hash);
    
    // In mock mode, we can verify the execution completed correctly
    // Real Groth16 proving would require: client.prove(&pk, &stdin).groth16().run()
    println!("\n  Note: For actual Groth16 proof, use prover network or run with:");
    println!("    SP1_PROVER=network cargo test test_sp1_fibonacci_groth16 -- --ignored");
}

#[test]
#[ignore] // Run with: SP1_PROVER=network cargo test test_sp1_fibonacci_groth16 -- --ignored
fn test_sp1_fibonacci_groth16() {
    println!("\n=== SP1 Fibonacci Groth16 Proof Test ===\n");
    
    // Create SP1 prover from environment (network or local)
    let client = ProverClient::from_env();
    
    // Setup input
    let mut stdin = SP1Stdin::new();
    stdin.write(&10u32); // Compute fib(10)
    
    // Generate proof
    println!("Generating SP1 Groth16 proof...");
    let (pk, vk) = client.setup(FIBONACCI_ELF);
    let proof = client.prove(&pk, &stdin).groth16().run().expect("proving failed");
    
    println!("  ✓ SP1 proof generated");
    println!("  VKey hash: {}", vk.bytes32());
    
    // Get raw proof bytes for bridge
    let raw_proof = proof.bytes();
    println!("  Raw proof size: {} bytes", raw_proof.len());
    
    // Verify with SP1
    client.verify(&proof, &vk).expect("verification failed");
    println!("  ✓ SP1 verification passed");
}

/// Full E2E test with simulated inner proof
/// This test verifies the full PVUGC pipeline works with SP1's proof structure
#[test]
fn test_sp1_to_pvugc_simulated() {
    use arkworks_groth16::pvugc_outer::{
        build_pvugc_setup_from_pk_for,
        build_column_bases_outer_for,
        arm_columns_outer_for,
        compute_target_outer_for,
        compute_r_to_rho_outer_for,
    };
    use arkworks_groth16::prover_lean::prove_lean_with_randomizers;
    use arkworks_groth16::decap::build_commitments;
    use arkworks_groth16::ct::gt_eq_ct;
    use ark_groth16::Groth16;
    use ark_snark::SNARK;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
    
    println!("\n=== SP1 → PVUGC Simulated E2E Test (2 public inputs) ===\n");
    
    let mut rng = StdRng::seed_from_u64(42);
    type Cycle = Bls12Bw6Cycle;
    
    // Step 1: Create a mock "inner" circuit that mimics SP1's structure
    // SP1's Groth16 wrapper has 2 public inputs: vkey_hash, committed_values_digest
    #[derive(Clone)]
    struct MockSp1InnerCircuit {
        vkey_hash: Option<Fr377>,
        committed_values_digest: Option<Fr377>,
    }
    
    impl ConstraintSynthesizer<Fr377> for MockSp1InnerCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr377>) -> Result<(), SynthesisError> {
            use ark_r1cs_std::prelude::*;
            use ark_r1cs_std::fields::fp::FpVar;
            
            // SP1's 2 public inputs
            let vkey_hash = FpVar::new_input(cs.clone(), || {
                self.vkey_hash.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let committed_values_digest = FpVar::new_input(cs.clone(), || {
                self.committed_values_digest.ok_or(SynthesisError::AssignmentMissing)
            })?;
            
            // Add some constraints to simulate SP1's wrapper (simplified)
            let sum = &vkey_hash + &committed_values_digest;
            let _ = &sum * &sum; // Just to have some constraints
            
            Ok(())
        }
    }
    
    println!("Step 1: Setting up mock SP1 inner circuit (2 public inputs)...");
    
    // SP1's actual public inputs (no hashing needed!)
    let vkey_hash = Fr377::from(67890u64);     // SP1 program's vkey hash
    let committed_values_digest = Fr377::from(11111u64); // Program outputs
    
    let inner_circuit = MockSp1InnerCircuit {
        vkey_hash: Some(vkey_hash),
        committed_values_digest: Some(committed_values_digest),
    };
    
    // Generate inner keys and proof
    let (inner_pk, inner_vk) = Groth16::<Bls12_377>::circuit_specific_setup(
        inner_circuit.clone(),
        &mut rng,
    ).expect("inner setup failed");
    
    let inner_proof = Groth16::<Bls12_377>::prove(&inner_pk, inner_circuit.clone(), &mut rng)
        .expect("inner prove failed");
    
    // Verify inner proof with 2 public inputs
    let inner_public_inputs = vec![vkey_hash, committed_values_digest];
    assert!(
        Groth16::<Bls12_377>::verify(&inner_vk, &inner_public_inputs, &inner_proof).unwrap(),
        "Inner proof verification failed"
    );
    println!("  ✓ Mock inner proof generated and verified");
    println!("  vkey_hash: {:?}", vkey_hash);
    println!("  committed_values_digest: {:?}", committed_values_digest);
    
    // Step 2: Setup outer circuit
    println!("\nStep 2: Setting up outer circuit...");
    let (pk_outer, vk_outer) = setup_outer_params_for::<Cycle>(
        &inner_vk,
        inner_public_inputs.len(),
        &mut rng,
    ).expect("outer setup failed");
    
    // Create inner proof generator for PVUGC setup
    let inner_proof_for_gen = inner_proof.clone();
    let inner_proof_generator = move |_x: &[Fr377]| -> Proof<Bls12_377> {
        inner_proof_for_gen.clone()
    };
    
    let (pvugc_vk, lean_pk) = build_pvugc_setup_from_pk_for::<Cycle, _>(
        &pk_outer,
        &inner_vk,
        inner_proof_generator,
    );
    println!("  ✓ Outer circuit setup complete");
    
    // Step 3: Generate outer proof
    println!("\nStep 3: Generating outer proof...");
    let circuit = OuterCircuit::<Cycle>::new(
        inner_vk.clone(),
        inner_public_inputs.clone(),
        inner_proof.clone(),
    );
    
    let r = OuterScalar::<Cycle>::rand(&mut rng);
    let s = OuterScalar::<Cycle>::rand(&mut rng);
    
    let (proof_outer, assignment) = prove_lean_with_randomizers(&lean_pk, circuit, r, s)
        .expect("lean prove failed");
    println!("  ✓ Outer proof generated");
    
    // Step 4: PVUGC decap
    println!("\nStep 4: PVUGC decapsulation...");
    
    let x_outer: Vec<OuterScalar<Cycle>> = inner_public_inputs
        .iter()
        .map(|x| fr_inner_to_outer_for::<Cycle>(x))
        .collect();
    
    let bases = build_column_bases_outer_for::<Cycle>(&pvugc_vk, &vk_outer, &x_outer);
    let rho = OuterScalar::<Cycle>::rand(&mut rng);
    let col_arms = arm_columns_outer_for::<Cycle>(&bases, &rho);
    
    let num_instance = vk_outer.gamma_abc_g1.len();
    let commitments = build_commitments::<<Cycle as RecursionCycle>::OuterE>(
        &proof_outer.a,
        &proof_outer.c,
        &s,
        &assignment,
        num_instance,
    );
    
    let k_decapped = arkworks_groth16::decap::decap(&commitments, &col_arms)
        .expect("decap failed");
    
    let r_target = compute_target_outer_for::<Cycle>(&vk_outer, &pvugc_vk, &inner_public_inputs);
    let k_expected = compute_r_to_rho_outer_for::<Cycle>(&r_target, &rho);
    
    assert!(
        gt_eq_ct::<<Cycle as RecursionCycle>::OuterE>(&k_decapped, &k_expected),
        "Decapped key doesn't match expected R^ρ!"
    );
    println!("  ✓ K_decapped == R^ρ verified!");
    
    println!("\n=== SP1 → PVUGC Simulated E2E Test PASSED ===");
}

#[test]
#[ignore] // Run with: SP1_PROVER=network cargo test test_sp1_to_pvugc_real -- --ignored
fn test_sp1_to_pvugc_real() {
    println!("\n=== SP1 → PVUGC Real E2E Test ===\n");
    
    let _rng = StdRng::seed_from_u64(42);
    
    // Ensure SP1 can find Groth16 wrapper artifacts locally (pk/vk/r1cs).
    //
    // SP1 expects artifacts under:
    //   $SP1_GROTH16_CIRCUIT_PATH/<SP1_CIRCUIT_VERSION>/
    // but this repo keeps test artifacts at:
    //   sp1-keys/test/
    // so we create a versioned subdir and copy/link the artifacts there, then point SP1 at it.
    use std::path::PathBuf;
    let version = sp1_sdk::SP1_CIRCUIT_VERSION.trim();
    let base = PathBuf::from("sp1-keys").join("test");
    let versioned = base.join(version);
    std::fs::create_dir_all(&versioned).expect("create groth16 artifacts dir");

    // Copy the artifacts into the versioned subdir expected by `SP1_GROTH16_CIRCUIT_PATH`.
    // Note: `groth16_witness.json` is part of the artifact bundle SP1 generates/consumes.
    for name in [
        "groth16_circuit.bin",
        "groth16_pk.bin",
        "groth16_vk.bin",
        "constraints.json",
        "groth16_witness.json",
    ] {
        let src = base.join(name);
        let dst = versioned.join(name);
        if !dst.exists() {
            std::fs::copy(&src, &dst).expect("copy groth16 artifact");
        }
    }

    std::env::set_var("SP1_GROTH16_CIRCUIT_PATH", &base);

    // Step 1: Generate real SP1 Groth16 proof
    println!("Step 1: Generating SP1 Groth16 proof...");
    let client = ProverClient::from_env();
    
    let mut stdin = SP1Stdin::new();
    stdin.write(&10u32);
    
    let (pk, vk) = client.setup(FIBONACCI_ELF);
    let sp1_proof = client.prove(&pk, &stdin).groth16().run().expect("proving failed");
    println!("  ✓ SP1 proof generated");
    println!("  Program vkey_hash: {}", vk.bytes32());
    
    // Step 2: Bridge to arkworks
    println!("\nStep 2: Bridging to arkworks...");

    // Extract the gnark `WriteRawTo` proof bytes from SP1 (hex).
    // This is the canonical bridge format in this repo (not Solidity encoding).
    let (raw_proof_hex, public_inputs_hex, groth16_vkey_hash) = match &sp1_proof.proof {
        sp1_sdk::SP1Proof::Groth16(p) => (p.raw_proof.clone(), p.public_inputs.clone(), p.groth16_vkey_hash),
        other => panic!("expected Groth16 proof, got {other}"),
    };

    let proof_bytes = decode_sp1_proof_hex(&raw_proof_hex).expect("decode raw_proof hex");
    let inner_proof = parse_gnark_proof_bls12_377(&proof_bytes).expect("parse gnark raw proof");

    // Load the Groth16 verifying key from the *same artifacts dir SP1 used*.
    //
    // - If SP1_DEV=1: SP1 builds artifacts in ~/.sp1/circuits/dev
    // - Else: SP1 loads artifacts from $SP1_GROTH16_CIRCUIT_PATH/<SP1_CIRCUIT_VERSION>/
    let is_dev = std::env::var("SP1_DEV")
        .map(|v| v == "1" || v.to_lowercase() == "true")
        .unwrap_or(false);
    let artifacts_dir = if is_dev {
        let home = std::env::var_os("HOME").expect("HOME not set");
        std::path::PathBuf::from(home)
            .join(".sp1")
            .join("circuits")
            .join("dev")
    } else {
        versioned.clone()
    };
    let groth16_vk_path = artifacts_dir.join("groth16_vk.bin");
    let vk_bytes = std::fs::read(&groth16_vk_path).unwrap_or_else(|e| {
        panic!("read groth16_vk.bin at {}: {e}", groth16_vk_path.display())
    });
    let vk_hash = Sha256::digest(&vk_bytes);
    println!(
        "  Groth16 VK bytes: {} (sha256[0..4]={:02x}{:02x}{:02x}{:02x}, proof.groth16_vkey_hash[0..4]={:02x}{:02x}{:02x}{:02x})",
        vk_bytes.len(),
        vk_hash[0], vk_hash[1], vk_hash[2], vk_hash[3],
        groth16_vkey_hash[0], groth16_vkey_hash[1], groth16_vkey_hash[2], groth16_vkey_hash[3],
    );
    let inner_vk = parse_gnark_vk_bls12_377(&vk_bytes).expect("parse gnark raw vk");

    // Decode SP1's two public inputs.
    let vkey_hash_fe = decode_sp1_public_input(&public_inputs_hex[0]).expect("decode vkey_hash");
    let committed_values_digest_fe =
        decode_sp1_public_input(&public_inputs_hex[1]).expect("decode committed_values_digest");
    let inner_public_inputs = vec![vkey_hash_fe, committed_values_digest_fe];

    // Sanity checks: ensure VK expects exactly these public inputs.
    assert_eq!(
        inner_vk.gamma_abc_g1.len(),
        1 + inner_public_inputs.len(),
        "VK IC length mismatch: gamma_abc_g1.len() must equal 1 + num_public_inputs"
    );
    println!(
        "  Decoded public inputs (decimal): vkey_hash={}, committed_values_digest={}",
        inner_public_inputs[0],
        inner_public_inputs[1],
    );

    // Verify in arkworks (this is the bridge correctness check).
    let inner_pvk = prepare_verifying_key(&inner_vk);
    assert!(
        Groth16::<Bls12_377>::verify_proof(&inner_pvk, &inner_proof, &inner_public_inputs).unwrap(),
        "arkworks verification failed for bridged gnark proof"
    );
    println!("  ✓ Bridged gnark proof verified in arkworks");

    println!("\n=== SP1 → PVUGC Real E2E Test (bridge verify) PASSED ===");
}

#[test]
fn test_sp1_public_inputs() {
    println!("\n=== SP1 Public Inputs Test ===\n");
    
    // SP1's 2 public inputs - no hashing needed, PVUGC handles both directly
    let vkey_hash_1 = Fr377::from(100u64);
    let vkey_hash_2 = Fr377::from(200u64);
    let claim_1 = Fr377::from(1000u64);
    let claim_2 = Fr377::from(2000u64);
    
    let inputs_1 = Sp1PublicInputs::new(vkey_hash_1, claim_1);
    let inputs_2 = Sp1PublicInputs::new(vkey_hash_2, claim_1);
    let inputs_3 = Sp1PublicInputs::new(vkey_hash_1, claim_2);
    
    // Different inputs should produce different vectors
    assert_ne!(inputs_1.to_vec(), inputs_2.to_vec(), "Different vkey_hash should differ");
    assert_ne!(inputs_1.to_vec(), inputs_3.to_vec(), "Different claim should differ");
    
    // Test as_slice
    let slice = inputs_1.as_slice();
    assert_eq!(slice[0], vkey_hash_1);
    assert_eq!(slice[1], claim_1);
    
    // Test to_vec produces correct length (2 elements)
    assert_eq!(inputs_1.to_vec().len(), 2);
    
    println!("✓ Sp1PublicInputs correctly handles 2 public inputs");
    println!("  - vkey_hash: identifies SP1 program");
    println!("  - committed_values_digest: binds program outputs");
}
