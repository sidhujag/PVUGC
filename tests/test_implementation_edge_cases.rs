//! Security tests for implementation edge cases

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::pairing::Pairing;
use ark_ec::AffineRepr;
use ark_ff::{One, Zero};
use ark_groth16::Groth16;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, SynthesisError,
};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::ppe::{compute_groth16_target, extract_y_bases, PvugcVk};

#[derive(Clone)]
struct TestCircuit {
    pub x: Option<Fr>,
    pub y: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for TestCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let x = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let y = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let y_squared = &y * &y;
        x.enforce_equal(&y_squared)?;

        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

#[test]
fn test_constant_one_is_public() {
    use ark_std::rand::SeedableRng;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(0);

    let circuit = TestCircuit {
        x: Some(Fr::from(25u64)),
        y: Some(Fr::from(5u64)),
    };

    // Generate CRS
    let (pk, vk) = Groth16::<E>::circuit_specific_setup_pvugc(circuit, &mut rng).unwrap();

    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    let y_bases = extract_y_bases(&pvugc_vk);
    
    assert!(y_bases.len() > 1);
    assert_eq!(y_bases[0], vk.beta_g2);
}

#[test]
fn test_ic_zero_rejected() {
    use ark_std::rand::SeedableRng;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(1);

    let circuit = TestCircuit {
        x: Some(Fr::from(36u64)),
        y: Some(Fr::from(6u64)),
    };

    let (_pk, vk) = Groth16::<E>::circuit_specific_setup_pvugc(circuit, &mut rng).unwrap();

    let normal_input = vec![Fr::from(36u64)];
    assert!(compute_groth16_target(&vk, &normal_input).is_ok());

    let mut bad_vk = vk.clone();
    bad_vk.gamma_abc_g1_raw = vec![<E as Pairing>::G1Affine::identity(); 2];

    let result = compute_groth16_target(&bad_vk, &normal_input);
    assert!(result.is_err());
}

#[test]
fn test_degenerate_target_rejected() {
    use ark_std::rand::SeedableRng;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(2);

    let circuit = TestCircuit {
        x: Some(Fr::from(49u64)),
        y: Some(Fr::from(7u64)),
    };

    let (_pk, vk) = Groth16::<E>::circuit_specific_setup_pvugc(circuit, &mut rng).unwrap();

    let r = compute_groth16_target(&vk, &vec![Fr::from(49u64)]).unwrap();
    
    assert!(!r.0.is_zero());
    assert!(!r.0.is_one());
}

#[test]
fn test_enforce_public_outputs_prevents_floating_one() {
    let cs = ConstraintSystem::<Fr>::new_ref();
    cs.set_optimization_goal(ark_relations::r1cs::OptimizationGoal::Constraints);

    let _x1 = cs.new_input_variable(|| Ok(Fr::from(10u64))).unwrap();
    let _x2 = cs.new_input_variable(|| Ok(Fr::from(20u64))).unwrap();

    enforce_public_inputs_are_outputs(cs.clone()).unwrap();

    assert!(cs.num_constraints() >= 3);
}

#[test]
fn test_gamma_g2_rejection() {
    use ark_std::rand::SeedableRng;
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(3);

    let circuit = TestCircuit {
        x: Some(Fr::from(64u64)),
        y: Some(Fr::from(8u64)),
    };

    let (pk, vk) = Groth16::<E>::circuit_specific_setup_pvugc(circuit, &mut rng).unwrap();

    let pvugc_vk = PvugcVk::<E> {
        beta_g2: vk.beta_g2,
        delta_g2: vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()),
    };

    let y_bases = extract_y_bases(&pvugc_vk);

    for y in &y_bases {
        assert_ne!(*y, vk.gamma_g2);
    }
}

