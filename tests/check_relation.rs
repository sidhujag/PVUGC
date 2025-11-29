
use ark_bls12_377::Bls12_377;
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::alloc::AllocVar;

#[derive(Clone)]
struct TestCircuit {
    x: Option<ark_bls12_377::Fr>,
}

impl ConstraintSynthesizer<ark_bls12_377::Fr> for TestCircuit {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<ark_bls12_377::Fr>,
    ) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let w_var = FpVar::new_witness(cs.clone(), || Ok(ark_bls12_377::Fr::from(2u64)))?;
        x_var.mul_equals(&w_var, &w_var)?; 
        Ok(())
    }
}

#[test]
fn test_relation() {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    let circuit = TestCircuit { x: None };
    let (pk, vk) = Groth16::<Bls12_377>::circuit_specific_setup(circuit, &mut rng).unwrap();

    println!("pk.a_query len: {}", pk.a_query.len());
    println!("vk.gamma_abc_g1 len: {}", vk.gamma_abc_g1.len());

    // Check first public input (index 1, index 0 is '1')
    let a_1 = pk.a_query[1];
    let ic_1 = vk.gamma_abc_g1[1];

    println!("A_1: {:?}", a_1);
    println!("IC_1: {:?}", ic_1);

    if a_1 == ic_1 {
        println!("A_1 == IC_1");
    } else {
        println!("A_1 != IC_1");
    }
    
    assert_ne!(a_1, ic_1, "A_1 should NOT match IC_1 in standard Groth16");
}

