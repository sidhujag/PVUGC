//! End-to-End Test for One-Sided GS PVUGC

use arkworks_groth16::*;
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use arkworks_groth16::ppe::PvugcVk;
use ark_bls12_381::{Bls12_381, Fr};
use ark_std::{UniformRand, rand::rngs::StdRng, rand::SeedableRng};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::alloc::AllocVar;

type E = Bls12_381;

// Test circuit: x = y²
#[derive(Clone)]
struct SquareCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for SquareCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let y_var = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let y_squared = &y_var * &y_var;
        x_var.enforce_equal(&y_squared)?;
        
        Ok(())
    }
}

#[test]
fn test_one_sided_pvugc_proof_agnostic() {
    let mut rng = StdRng::seed_from_u64(0);
    
    
    // Vault setup (statement = public input)
    let vault_utxo = vec![Fr::from(25u64)];  // x = y² = 5² = 25
    
    // Setup Groth16 for the circuit
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    
    // === DEPOSIT TIME ===
    
    // Build PVUGC VK wrapper
    let pvugc_vk = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    
    // Generate ρ
    let rho = Fr::rand(&mut rng);
    
    // Generate gamma (identity for tests - simple and deterministic)
    // TODO: Production should use derive_gamma_rademacher for compression
    let gamma = {
        let n = pvugc_vk.b_g2_query.len() + 1;
        (0..n).map(|i| {
            let mut row = vec![Fr::from(0u64); n];
            row[i] = Fr::from(1u64);
            row
        }).collect::<Vec<_>>()
    };
    
    // Use the API for setup and arming
    let (rows, arms, _r, k_expected) = OneSidedPvugc::setup_and_arm(
        &pvugc_vk,
        &vk,
        &vault_utxo,
        &rho,
        gamma.clone(),
    );
    
    // PoCE-Across for verification
    let mut all_bases = rows.u_rows.clone();
    all_bases.extend(&rows.w_rows);
    let mut all_arms = arms.u_rows_rho.clone();
    all_arms.extend(&arms.w_rows_rho);
    let poce_proof: PoceAcrossProof<E> = prove_poce_across(&all_bases, &all_arms, &rho, &mut rng);
    assert!(verify_poce_across(&all_bases, &all_arms, &poce_proof));
    
    // === SPEND TIME - PROOF 1 ===
    
    // Use coefficient recorder to capture real b_j via HOOKED prover
    let mut recorder1 = SimpleCoeffRecorder::<E>::new();
    let proof1 = Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder1).unwrap();
    
    // Use API to build commitments and bundle
    let commitments1 = recorder1.build_commitments(&pvugc_vk, &gamma);
    let bundle1 = PvugcBundle {
        groth16_proof: proof1.clone(),
        dlrep_b: recorder1.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder1.create_dlrep_tie(&gamma, &mut rng),
        gs_commitments: commitments1.clone(),
    };
    
    // Verify using OneSidedPvugc (checks PPE equation)
    assert!(OneSidedPvugc::verify(&bundle1, &pvugc_vk, &vk, &vault_utxo, &gamma));
    
    let k1 = OneSidedPvugc::decapsulate(&commitments1, &arms);
    
    // === SPEND TIME - PROOF 2 ===
    
    let mut recorder2 = SimpleCoeffRecorder::<E>::new();
    let proof2 = Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder2).unwrap();
    
    // Use API to build commitments and bundle
    let commitments2 = recorder2.build_commitments(&pvugc_vk, &gamma);
    let bundle2 = PvugcBundle {
        groth16_proof: proof2.clone(),
        dlrep_b: recorder2.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder2.create_dlrep_tie(&gamma, &mut rng),
        gs_commitments: commitments2.clone(),
    };
    
    // Verify using OneSidedPvugc (checks PPE equation)
    assert!(OneSidedPvugc::verify(&bundle2, &pvugc_vk, &vk, &vault_utxo, &gamma));
    
    let k2 = OneSidedPvugc::decapsulate(&commitments2, &arms);
    
    // === PROOF-AGNOSTIC PROPERTY ===
    
    assert_eq!(k1, k2);
    assert_eq!(k1, k_expected);
    
    
    // === TEST: DIFFERENT STATEMENT PRODUCES DIFFERENT K ===
    
    // Different vault UTXO = different statement = different R
    let vault2_utxo = vec![Fr::from(49u64)];  // x = 7² = 49
    
    // Setup new circuit for x=49
    let circuit2 = SquareCircuit {
        x: Some(Fr::from(49u64)),
        y: Some(Fr::from(7u64)),
    };
    
    let (pk2, vk2) = Groth16::<E>::circuit_specific_setup(circuit2.clone(), &mut rng).unwrap();
    let pvugc_vk2 = PvugcVk {
        beta_g2: vk2.beta_g2,
        delta_g2: vk2.delta_g2,
        b_g2_query: pk2.b_g2_query.clone(),
    };
    
    // Generate proof for vault 2
    let mut recorder_vault2 = SimpleCoeffRecorder::<E>::new();
    let proof_vault2 = Groth16::<E>::create_random_proof_with_hook(
        circuit2, &pk2, &mut rng, &mut recorder_vault2
    ).unwrap();
    
    // Build commitments and bundle for vault 2
    let commitments_vault2 = recorder_vault2.build_commitments(&pvugc_vk2, &gamma);
    let bundle_vault2 = PvugcBundle {
        groth16_proof: proof_vault2.clone(),
        dlrep_b: recorder_vault2.create_dlrep_b(&pvugc_vk2, &mut rng),
        dlrep_tie: recorder_vault2.create_dlrep_tie(&gamma, &mut rng),
        gs_commitments: commitments_vault2.clone(),
    };
    
    // VERIFY vault2's bundle
    assert!(OneSidedPvugc::verify(&bundle_vault2, &pvugc_vk2, &vk2, &vault2_utxo, &gamma));
    
    // Setup arms for vault 2 (uses SAME ρ but different VK bases)
    let (y_bases2, delta2, _) = build_one_sided_ppe(&pvugc_vk2, &vk2, &vault2_utxo);
    let rows2: RowBases<E> = build_row_bases_from_vk(&y_bases2, delta2, gamma.clone());
    let arms2 = arm_rows(&rows2, &rho);  // SAME ρ!
    
    // Decap vault2's proof
    let k_vault2_decap = OneSidedPvugc::decapsulate(&commitments_vault2, &arms2);
    
    // Compute expected R for vault 2
    let r_vault2 = compute_groth16_target(&vk2, &vault2_utxo);
    let k_vault2_expected = OneSidedPvugc::compute_r_to_rho(&r_vault2, &rho);
    
    // Verify vault2 decap matches its expected R^ρ
    assert_eq!(k_vault2_decap, k_vault2_expected, "Vault2 decap should match R₂^ρ");
    
    // Different statements should produce different K
    // Even though we use SAME ρ!
    assert_ne!(k1, k_vault2_decap, "Different vaults MUST produce different keys!");
}

#[test]
fn test_delta_sign_sanity() {
    let mut rng = StdRng::seed_from_u64(42);
    let vault_utxo = vec![Fr::from(25u64)];
    let circuit = SquareCircuit { x: Some(Fr::from(25u64)), y: Some(Fr::from(5u64)) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };
    let rho = Fr::rand(&mut rng);
    
    // Setup gamma (identity matrix)
    let gamma = {
        let n = pvugc_vk.b_g2_query.len() + 1;
        (0..n)
            .map(|i| {
                let mut row = vec![Fr::from(0u64); n];
                row[i] = Fr::from(1u64);
                row
            })
            .collect::<Vec<_>>()
    };
    
    // Use API for setup and arming
    let (_rows, arms, _r, k_expected) = OneSidedPvugc::setup_and_arm(
        &pvugc_vk,
        &vk,
        &vault_utxo,
        &rho,
        gamma.clone(),
    );

    // Hooked proof and commitments
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit.clone(), &pk, &mut rng, &mut recorder).unwrap();
    assert!(Groth16::<E>::verify(&vk, &vault_utxo, &proof).unwrap());
    
    let commitments = recorder.build_commitments(&pvugc_vk, &gamma);

    // Correct sign → K_good == R^ρ
    let k_good = OneSidedPvugc::decapsulate(&commitments, &arms);
    assert_eq!(k_good, k_expected);
}

#[test]
fn test_r_computation_deterministic() {
    let mut rng = StdRng::seed_from_u64(1);
    
    
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    let vault_utxo = vec![Fr::from(12345u64)];
    
    // Compute R twice
    let r1 = compute_groth16_target(&vk, &vault_utxo);
    let r2 = compute_groth16_target(&vk, &vault_utxo);
    
    assert_eq!(r1, r2);
}

#[test]
fn test_different_vaults_different_r() {
    let mut rng = StdRng::seed_from_u64(2);
    
    
    let circuit = SquareCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (_pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    
    let vault1 = vec![Fr::from(12345u64)];
    let vault2 = vec![Fr::from(67890u64)];
    
    let r1 = compute_groth16_target(&vk, &vault1);
    let r2 = compute_groth16_target(&vk, &vault2);
    
    assert_ne!(r1, r2);
}

#[test]
fn test_witness_independence() {
    use ark_std::UniformRand;
    
    let mut rng = StdRng::seed_from_u64(300);
    
    
    // Addition circuit
    #[derive(Clone)]
    struct AddCircuit {
        pub x: Option<Fr>,
        pub y: Option<Fr>,
        pub z: Option<Fr>,
    }
    
    impl ConstraintSynthesizer<Fr> for AddCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
            let x_var = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
            let y_var = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
            let z_var = FpVar::new_witness(cs.clone(), || self.z.ok_or(SynthesisError::AssignmentMissing))?;
            let sum = &y_var + &z_var;
            x_var.enforce_equal(&sum)?;
            Ok(())
        }
    }
    
    let public_x = vec![Fr::from(11u64)];
    
    // Witness 1: y=4, z=7 (4+7=11)
    let circuit1 = AddCircuit {
        x: Some(public_x[0]),  // Use public_x
        y: Some(Fr::from(4u64)),
        z: Some(Fr::from(7u64)),
    };
    
    // Witness 2: y=5, z=6 (5+6=11)
    let circuit2 = AddCircuit {
        x: Some(public_x[0]),  // Same public_x
        y: Some(Fr::from(5u64)),
        z: Some(Fr::from(6u64)),
    };
    
    // ONE setup (same pk, vk for both witnesses)
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit1.clone(), &mut rng).unwrap();
    
    // Compute R = e(α,β)·e(L(x),γ) from (vk, public_x)
    let r_statement = compute_groth16_target(&vk, &public_x);
    
    
    let pvugc_vk = PvugcVk {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: pk.b_g2_query.clone(),
    };
    
    let rho = Fr::rand(&mut rng);
    
    // Generate gamma (identity for tests - simple and deterministic)
    // TODO: Production should use derive_gamma_rademacher for compression
    let gamma = {
        let n = pvugc_vk.b_g2_query.len() + 1;
        (0..n).map(|i| {
            let mut row = vec![Fr::from(0u64); n];
            row[i] = Fr::from(1u64);
            row
        }).collect::<Vec<_>>()
    };
    
    let (_, arms, _, k_expected) = OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk, &public_x, &rho, gamma.clone());
    
    let mut recorder1 = SimpleCoeffRecorder::<E>::new();
    let proof1 = Groth16::<E>::create_random_proof_with_hook(circuit1, &pk, &mut rng, &mut recorder1).unwrap();
    
    let commitments1 = recorder1.build_commitments(&pvugc_vk, &gamma);
    let bundle1 = PvugcBundle {
        groth16_proof: proof1,
        dlrep_b: recorder1.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder1.create_dlrep_tie(&gamma, &mut rng),
        gs_commitments: commitments1.clone(),
    };
    
    assert!(OneSidedPvugc::verify(&bundle1, &pvugc_vk, &vk, &public_x, &gamma));
    let k1 = OneSidedPvugc::decapsulate(&commitments1, &arms);
    
    let mut recorder2 = SimpleCoeffRecorder::<E>::new();
    let proof2 = Groth16::<E>::create_random_proof_with_hook(circuit2, &pk, &mut rng, &mut recorder2).unwrap();
    
    let commitments2 = recorder2.build_commitments(&pvugc_vk, &gamma);
    let bundle2 = PvugcBundle {
        groth16_proof: proof2,
        dlrep_b: recorder2.create_dlrep_b(&pvugc_vk, &mut rng),
        dlrep_tie: recorder2.create_dlrep_tie(&gamma, &mut rng),
        gs_commitments: commitments2.clone(),
    };
    
    assert!(OneSidedPvugc::verify(&bundle2, &pvugc_vk, &vk, &public_x, &gamma));
    let k2 = OneSidedPvugc::decapsulate(&commitments2, &arms);
    
    // Since R = compute_groth16_target(vk, public_x) doesn't use witnesses:
    // R is the SAME for both proofs
    assert_eq!(k1, k2, "WITNESS-INDEPENDENT: Different witnesses → Same K!");
    
    // Verify both equal expected R^ρ (from statement)
    let k_expected_r = OneSidedPvugc::compute_r_to_rho(&r_statement, &rho);
    assert_eq!(k1, k_expected_r, "K₁ should equal R^ρ");
    assert_eq!(k2, k_expected_r, "K₂ should equal R^ρ");
    assert_eq!(k1, k_expected, "Should match setup_and_arm");
    
}
