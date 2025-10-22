//! Outer-Compressed: Proof-of-Proof Recursion
//!
//! This module implements the outer circuit that verifies an inner Groth16 proof
//! inside a small R1CS, producing a constant-size outer proof that PVUGC can operate on.
//!
//! Architecture (BLS12-377/BW6-761 cycle):
//! - Inner curve: BLS12-377 (application circuit)
//! - Outer curve: BW6-761 (verifier circuit)
//! - PVUGC runs on the OUTER proof (constant-size right-legs)
//!

use ark_ec::pairing::Pairing;
use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_relations::r1cs::SynthesisError;

// Curve types for recursion (BLS12-377/BW6-761 cycle)
pub type InnerE  = ark_bls12_377::Bls12_377;
pub type OuterE  = ark_bw6_761::BW6_761;
pub type InnerFr = <InnerE as Pairing>::ScalarField;
pub type OuterFr = <OuterE as Pairing>::ScalarField;

use ark_groth16::constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar};
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    pairing::bls12::PairingVar as Bls12PairingVar,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef};
use ark_crypto_primitives::snark::constraints::{SNARKGadget, BooleanInputVar};
use ark_ff::{PrimeField, BigInteger};

// BLS12 pairing gadget for verifying inner (BLS12-377) proofs in outer (BW6-761) circuit
type InnerPV = Bls12PairingVar<ark_bls12_377::Config>;

/// Helper: Convert InnerFr (BLS12-377 Fr) to OuterFr (BW6-761 Fr = BLS12-377 Fq)
/// 
/// Uses bytes as intermediate since ToConstraintField doesn't support cross-field conversion.
/// This is safe because BW6-761's scalar field equals BLS12-377's base field (2-cycle property).
pub fn fr_inner_to_outer(x: &InnerFr) -> OuterFr {
    let bytes = x.into_bigint().to_bytes_le();
    OuterFr::from_le_bytes_mod_order(&bytes)
}

/// Outer circuit: proves "Groth16::verify(vk_inner, x_inner, proof_inner) == true"
///
/// This circuit is a small R1CS whose only job is to verify a Groth16 proof from the inner curve.
/// By running PVUGC on this OUTER proof (not the inner), we get constant-size arms/pairings.
#[derive(Clone)]
pub struct OuterCircuit {
    /// Inner verifying key (treated as constant in the circuit)
    pub vk_inner: VerifyingKey<InnerE>,
    
    /// Public inputs to the inner circuit (mapped to outer field)
    pub x_inner: Vec<InnerFr>,
    
    /// Inner Groth16 proof (provided as witness)
    pub proof_inner: Proof<InnerE>,
}

impl ConstraintSynthesizer<OuterFr> for OuterCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<OuterFr>) -> Result<(), SynthesisError> {
        // 1) Allocate inner VK as constant (parameters)
        let vk_var = VerifyingKeyVar::<InnerE, InnerPV>::new_constant(cs.clone(), &self.vk_inner)?;
        
        // 2) Allocate inner proof as witness
        let proof_var = ProofVar::<InnerE, InnerPV>::new_witness(cs.clone(), || Ok(self.proof_inner))?;
        
        // 3) Allocate inner public inputs wrapped in BooleanInputVar
        //    The gadget takes native InnerFr values and converts to OuterFr constraints internally
        //    F = InnerFr (native field), CF = OuterFr (constraint field)
        // 
        // NOTE: BooleanInputVar creates a HASH of the inputs as a single public input
        let input_var = BooleanInputVar::<InnerFr, OuterFr>::new_input(
            cs.clone(),
            || Ok(self.x_inner.clone())
        )?;
        
        // Debug: Print the actual public input that was created
        #[cfg(test)]
        {
            let instance = cs.borrow().unwrap().instance_assignment.clone();
            eprintln!("         OuterCircuit: instance_assignment.len() = {}", instance.len());
            if instance.len() > 1 {
                eprintln!("         OuterCircuit: instance[1] = {:?}", instance[1]);
            }
        }
        
        // 4) Verify inner proof inside outer circuit
        let ok = Groth16VerifierGadget::<InnerE, InnerPV>::verify(&vk_var, &input_var, &proof_var)?;
        ok.enforce_equal(&Boolean::TRUE)?;
        
        Ok(())
    }
}

/// Setup outer Groth16 parameters for a given inner VK and public input count
///
/// This is done once per inner circuit (when VK changes).
/// The resulting outer PK/VK can be used for any inner proofs with the same VK.
pub fn setup_outer_params(
    vk_inner: &VerifyingKey<InnerE>,
    n_inputs: usize,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(ark_groth16::ProvingKey<OuterE>, VerifyingKey<OuterE>), SynthesisError> {
    // Create dummy circuit for parameter generation (shape-only)
    let dummy_x = vec![InnerFr::from(0u64); n_inputs];
    let dummy_proof = Proof::<InnerE> {
        a: Default::default(),
        b: Default::default(),
        c: Default::default(),
    };
    
    let circuit = OuterCircuit {
        vk_inner: vk_inner.clone(),
        x_inner: dummy_x,
        proof_inner: dummy_proof,
    };
    
    // Generate parameters
    use ark_snark::SNARK;
    let (pk, vk) = Groth16::<OuterE>::circuit_specific_setup(circuit, rng)?;
    
    Ok((pk, vk))
}

/// Prove outer circuit (generate proof-of-proof)
///
/// Takes an inner proof and produces an outer proof that verifies it.
/// Also returns the actual public inputs used for verification.
pub fn prove_outer(
    pk_outer: &ark_groth16::ProvingKey<OuterE>,
    vk_inner: &VerifyingKey<InnerE>,
    x_inner: &[InnerFr],
    proof_inner: &Proof<InnerE>,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(Proof<OuterE>, VerifyingKey<OuterE>, Vec<OuterFr>), SynthesisError> {
    let circuit = OuterCircuit {
        vk_inner: vk_inner.clone(),
        x_inner: x_inner.to_vec(),
        proof_inner: proof_inner.clone(),
    };
    
    // For BooleanInputVar, the public input is actually the value converted to OuterFr
    // BooleanInputVar creates a simple conversion, not a hash
    let public_inputs = if x_inner.is_empty() {
        vec![]
    } else {
        // Convert each inner input to outer field
        x_inner.iter().map(fr_inner_to_outer).collect::<Vec<_>>()
    };
    
    eprintln!("         prove_outer: extracted public_inputs = {:?}", public_inputs);
    
    use ark_snark::SNARK;
    let proof_outer = Groth16::<OuterE>::prove(pk_outer, circuit, rng)?;
    let vk_outer = pk_outer.vk.clone();
    
    Ok((proof_outer, vk_outer, public_inputs))
}

/// Verify outer Groth16 proof (standard verification)
///
/// This verifies that the outer proof is valid.
/// The outer proof's statement is "inner proof is valid".
/// 
/// IMPORTANT: The BooleanInputVar creates a single hash of all inner public inputs
/// as the outer public input, not the raw values themselves.
pub fn verify_outer(
    vk_outer: &VerifyingKey<OuterE>,
    x_inner: &[InnerFr],
    proof_outer: &Proof<OuterE>,
) -> Result<bool, SynthesisError> {
    // BooleanInputVar creates public inputs by converting InnerFr to OuterFr
    let x_outer: Vec<OuterFr> = x_inner.iter().map(fr_inner_to_outer).collect();
    
    use ark_snark::SNARK;
    let pvk = Groth16::<OuterE>::process_vk(vk_outer)?;
    Groth16::<OuterE>::verify_with_processed_vk(&pvk, &x_outer, proof_outer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;
    
    // Use shared AddCircuit and global fixture
    use crate::test_circuits::AddCircuit;
    use crate::test_fixtures::get_fixture;
    
    #[test]
    fn test_outer_circuit_setup_and_verify() {
        let mut rng = StdRng::seed_from_u64(12345);
        let fixture = get_fixture();
        let (pk_outer, vk_outer) = setup_outer_params(&fixture.vk_inner, 1, &mut rng).unwrap();
        
        let x = InnerFr::from(11u64);
        let public_x = vec![x];
        let circuit_inner = AddCircuit::with_public_input(x);
        
        use ark_snark::SNARK;
        let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).unwrap();
        let pvk_inner = Groth16::<InnerE>::process_vk(&fixture.vk_inner).unwrap();
        assert!(Groth16::<InnerE>::verify_with_processed_vk(&pvk_inner, &public_x, &proof_inner).unwrap());
        
        let (proof_outer, _, actual_public_inputs) = prove_outer(&pk_outer, &fixture.vk_inner, &public_x, &proof_inner, &mut rng).unwrap();
        let pvk = Groth16::<OuterE>::process_vk(&vk_outer).unwrap();
        let verification_result = Groth16::<OuterE>::verify_with_processed_vk(&pvk, &actual_public_inputs, &proof_outer);
        
        assert!(verification_result.unwrap(), "Outer proof verification failed");
    }
    
    #[test]
    #[ignore]
    fn test_pvugc_on_outer_proof_e2e() {
        use ark_snark::SNARK;
        use ark_std::rand::rngs::StdRng;
        use ark_std::rand::SeedableRng;
        use ark_std::UniformRand;
        
        let mut rng = StdRng::seed_from_u64(99999);
        let fixture = get_fixture();
        let (pk_outer, vk_outer) = setup_outer_params(&fixture.vk_inner, 1, &mut rng).unwrap();
        
        let x = InnerFr::from(42u64);
        let public_x = vec![x];
        let circuit_inner = AddCircuit::with_public_input(x);
        let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).unwrap();
        
        let rho = OuterFr::rand(&mut rng);
        let pvugc_vk = crate::ppe::PvugcVk::<OuterE> {
            beta_g2: vk_outer.beta_g2,
            delta_g2: vk_outer.delta_g2,
            b_g2_query: std::sync::Arc::new(pk_outer.b_g2_query.clone()),
        };
        
        let mut y_cols = vec![pvugc_vk.beta_g2];
        y_cols.extend_from_slice(&pvugc_vk.b_g2_query);
        let bases = crate::arming::ColumnBases::<OuterE> { 
            y_cols, 
            delta: pvugc_vk.delta_g2 
        };
        let col_arms = crate::arming::arm_columns(&bases, &rho);
        
        let outer_circuit = OuterCircuit {
            vk_inner: fixture.vk_inner.as_ref().clone(),
            x_inner: public_x.clone(),
            proof_inner: proof_inner.clone(),
        };
        
        use crate::coeff_recorder::SimpleCoeffRecorder;
        let mut recorder = SimpleCoeffRecorder::<OuterE>::new();
        let proof_outer = ark_groth16::Groth16::<OuterE>::create_random_proof_with_hook(
            outer_circuit,
            &pk_outer,
            &mut rng,
            &mut recorder,
        ).unwrap();
        
        assert!(verify_outer(&vk_outer, &public_x, &proof_outer).unwrap());
        
        let gs_commitments = recorder.build_commitments();
        let k_decapped = crate::decap::decap(&gs_commitments, &col_arms);
        
        let r = crate::pvugc_outer::compute_target_outer(&vk_outer, &public_x);
        let k_expected = crate::pvugc_outer::compute_r_to_rho_outer(&r, &rho);
        
        assert_eq!(k_decapped, k_expected, "Decapsulated K doesn't match R^ρ!");
    }
}

