//! Test that the coefficient recorder actually captures data from Groth16 prover

use ark_bls12_381::{Bls12_381, Fr};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::SeedableRng;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::alloc::AllocVar;
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use ark_ec::{CurveGroup, AffineRepr};

type E = Bls12_381;

#[derive(Clone)]
struct TestCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let y_var = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let y_squared = &y_var * &y_var;
        x_var.enforce_equal(&y_squared)?;
        Ok(())
    }
}

#[test]
fn test_recorder_captures_a() {
    let mut rng = StdRng::seed_from_u64(200);
    
    
    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    
    // Create recorder
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    
    // Before proving: should be empty
    assert!(recorder.get_coefficients().is_none());
    
    // Prove with hook
    let proof = Groth16::<E>::create_random_proof_with_hook(
        circuit.clone(),
        &pk,
        &mut rng,
        &mut recorder,
    ).unwrap();
    
    
    // After proving: check if A was captured
    let coeffs = recorder.get_coefficients();
    assert!(coeffs.is_some(), "Recorder should have captured coefficients!");
    
    let _coeffs = coeffs.unwrap();
    
    // Check if we have A
    assert!(recorder.has_a(), "A should be recorded");
    
    // Verify it's actually the same A from the proof
    // (Can't directly check without knowing internal structure, but we can verify proof is valid)
    assert!(Groth16::<E>::verify(&vk, &[Fr::from(25u64)], &proof).unwrap());
}

#[test]
fn test_recorder_captures_c() {
    let mut rng = StdRng::seed_from_u64(201);
    
    
    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (pk, _vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    
    let _proof = Groth16::<E>::create_random_proof_with_hook(
        circuit,
        &pk,
        &mut rng,
        &mut recorder,
    ).unwrap();
    
    // Check if C was captured
    assert!(recorder.has_c(), "C should be recorded");
    
    // Check negation works
    let c = recorder.get_c().expect("C should exist");
    let neg_c = recorder.get_neg_c().expect("Should be able to get -C");
    
    // Verify: C + (-C) = 0  
    let sum = c.into_group() + neg_c.into_group();
    assert!(sum.into_affine().is_zero());
}

#[test]
fn test_recorder_aggregates_correctly() {
    let mut rng = StdRng::seed_from_u64(202);
    
    
    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };
    
    let (pk, _vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    
    let mut recorder = SimpleCoeffRecorder::<E>::new();
    
    let _proof = Groth16::<E>::create_random_proof_with_hook(
        circuit,
        &pk,
        &mut rng,
        &mut recorder,
    ).unwrap();
    
    
    // Get coefficients through public API
    let coeffs = recorder.get_coefficients().expect("Should have coefficients");
    let n = coeffs.b.len();
    
    // Test aggregation with small identity matrix
    let gamma: Vec<Vec<Fr>> = (0..n.min(3)).map(|i| {
        let mut row = vec![Fr::from(0u64); n];
        row[i] = Fr::from(1u64);
        row
    }).collect();
    
    let x_b_agg = recorder.get_aggregated_x_b(&gamma);
    
    assert_eq!(x_b_agg.len(), n.min(3));
    
}

