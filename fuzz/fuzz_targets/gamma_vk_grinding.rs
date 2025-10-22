#![no_main]

// Goal: Simulate VK grinding against Γ derivation and assert structural validation holds.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;

use arkworks_groth16::ppe::{PvugcVk, derive_gamma_secure, validate_gamma_structure};

#[derive(Clone)]
struct SqCircuit { pub x: Option<Fr>, pub y: Option<Fr> }

impl ConstraintSynthesizer<Fr> for SqCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        use ark_r1cs_std::eq::EqGadget;
        let x = FpVar::new_input(cs.clone(), || self.x.ok_or(SynthesisError::AssignmentMissing))?;
        let y = FpVar::new_witness(cs.clone(), || self.y.ok_or(SynthesisError::AssignmentMissing))?;
        let y2 = &y * &y;
        x.enforce_equal(&y2)?;
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
    let seedb = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let extrab = if let Some(a) = take_bytes::<16>(&mut data) { a } else { return; };
    let rowsb = if let Some(a) = take_bytes::<1>(&mut data) { a } else { return; };
    let andkb = if let Some(a) = take_bytes::<1>(&mut data) { a } else { return; };
    let seed = u64::from_le_bytes(seedb);
    let rows = (rowsb[0] as usize % 6) + 2; // 2..=7
    let and_k = ((andkb[0] as usize) % 3) + 2; // 2..=4 candidates
    let extra = &extrab;

    // Grind VKs by different seeds; we won't actually iterate here but derive from fuzzer input
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let circuit = SqCircuit { x: Some(Fr::from(1u64)), y: Some(Fr::from(1u64)) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit, &mut rng).unwrap();
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: std::sync::Arc::new(pk.b_g2_query.clone()) };

    let gamma = derive_gamma_secure::<E>(&pvugc_vk, &vk, extra, rows, and_k, 2, true, true, 3);
    assert!(validate_gamma_structure::<E>(&gamma, 2, true, true));
});


