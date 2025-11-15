#![no_main]

// Goal: For two different verifying keys (different setups), with the SAME public input x
// and SAME ρ, we must have K1 = R(vk1, x)^ρ != K2 = R(vk2, x)^ρ (cross-circuit statement dependence).

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::pairing::PairingOutput;
use ark_std::rand::SeedableRng;
use ark_ff::Field;
use ark_ff::PrimeField;
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_snark::SNARK;

use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::ppe::compute_groth16_target;

// Circuit: enforce x = y^2
#[derive(Clone)]
struct SqCircuit { pub x: Option<Fr>, pub y: Option<Fr> }

impl ConstraintSynthesizer<Fr> for SqCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        use ark_r1cs_std::eq::EqGadget;
        use ark_r1cs_std::fields::fp::FpVar;
        let x = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let y = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let y2 = &y * &y;
        x.enforce_equal(&y2)?;
        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

fn take_bytes<const N: usize>(data: &mut &[u8]) -> Option<[u8; N]> {
    if data.len() < N { return None; }
    let (take, rest) = data.split_at(N);
    *data = rest;
    let mut arr = [0u8; N];
    arr.copy_from_slice(take);
    Some(arr)
}

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    // Public input x, rho, and two setup seeds
    let xb = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let rhob = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let s1b = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let s2b = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let x = Fr::from_le_bytes_mod_order(&xb);
    let rho = Fr::from_le_bytes_mod_order(&rhob);
    let seed1 = u64::from_le_bytes(s1b);
    let mut seed2 = u64::from_le_bytes(s2b);
    if seed1 == seed2 { seed2 ^= 0x9e3779b97f4a7c15; }

    // Build two different VKs via circuit-specific setups with different randomness
    let mut rng1 = ark_std::rand::rngs::StdRng::seed_from_u64(seed1);
    let mut rng2 = ark_std::rand::rngs::StdRng::seed_from_u64(seed2);

    // Choose a witness y such that x = y^2 for validity; if no such y, we'll still compute R, which is defined for any x
    // For efficiency, use provided x directly as public input; y only affects proving, which we don't do here.
    let circuit = SqCircuit { x: Some(x), y: None };
    let (_pk1, vk1) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng1).unwrap();
    let (_pk2, vk2) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng2).unwrap();

    // Compute K_i = R(vk_i, x)^rho
    let r1 = compute_groth16_target::<E>(&vk1, &[x]).expect("compute_groth16_target");
    let r2 = compute_groth16_target::<E>(&vk2, &[x]).expect("compute_groth16_target");
    let k1 = PairingOutput::<E>(r1.0.pow(rho.into_bigint()));
    let k2 = PairingOutput::<E>(r2.0.pow(rho.into_bigint()));

    if k1 == k2 {
        panic!("Cross-circuit collision: K1 == K2 for different VKs with same (x,rho)");
    }
});


