#![no_main]

// Goal: Attempt linear recombinations of row commitments and try to forge matching DLREP proofs.
// Expectation: Full verification must fail.

use libfuzzer_sys::fuzz_target;

use ark_bls12_381::{Bls12_381 as E, Fr};
use ark_ec::{pairing::Pairing, AffineRepr};
use ark_ff::{PrimeField, Field};
use ark_groth16::Groth16;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::fields::fp::FpVar;
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;
use ark_std::Zero;

use arkworks_groth16::api::{OneSidedPvugc, PvugcBundle};
use arkworks_groth16::coeff_recorder::SimpleCoeffRecorder;
use arkworks_groth16::ppe::PvugcVk;

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

fn small(b: u8) -> i64 { (b % 5) as i64 - 2 }

fuzz_target!(|data: &[u8]| {
    let mut data = data;
    let yb = if let Some(a) = take_bytes::<32>(&mut data) { a } else { return; };
    let seedb = if let Some(a) = take_bytes::<8>(&mut data) { a } else { return; };
    let y = Fr::from_le_bytes_mod_order(&yb);
    let x = y.square();
    let seed = u64::from_le_bytes(seedb);

    // Setup and produce a valid bundle
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let circuit = SqCircuit { x: Some(x), y: Some(y) };
    let (pk, vk) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let pvugc_vk = PvugcVk::<E> { beta_g2: vk.beta_g2, delta_g2: vk.delta_g2, b_g2_query: pk.b_g2_query.clone() };

    let mut rec = SimpleCoeffRecorder::<E>::new();
    let proof = Groth16::<E>::create_random_proof_with_hook(circuit, &pk, &mut rng, &mut rec).unwrap();
    let mut commitments = rec.build_commitments();
    let dlrep_b = rec.create_dlrep_b(&pvugc_vk, &mut rng);
    let dlrep_tie = rec.create_dlrep_tie(&mut rng);

    let bundle = PvugcBundle { groth16_proof: proof, dlrep_b, dlrep_tie, gs_commitments: commitments.clone() };
    assert!(OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &[x]));

    // Linear recombination of two rows (if available): C'_0 = a*C_0 + b*C_1
    if commitments.x_b_cols.len() < 2 { return; }
    let a = small(take_bytes::<1>(&mut data).unwrap_or([0])[0]);
    let b = small(take_bytes::<1>(&mut data).unwrap_or([0])[0]);
    if a == 0 && b == 0 { return; }

    use ark_ec::CurveGroup;
    let (c0a, c0b) = commitments.x_b_cols[0];
    let (c1a, c1b) = commitments.x_b_cols[1];
    let c0a_new = (c0a.into_group() * Fr::from(a) + c1a.into_group() * Fr::from(b)).into_affine();
    let c0b_new = (c0b.into_group() * Fr::from(a) + c1b.into_group() * Fr::from(b)).into_affine();
    commitments.x_b_cols[0] = (c0a_new, c0b_new);

    // Attempt to forge consistent DLREP proofs with the same public bases
    let fake_u = Fr::from_le_bytes_mod_order(&take_bytes::<32>(&mut data).unwrap_or([1;32]));
    let a_g1 = bundle.groth16_proof.a;
    let mut x_agg = <E as Pairing>::G1::zero();
    for (c_limb0, _) in &commitments.x_b_cols { x_agg += c_limb0.into_group(); }
    let x_agg = x_agg.into_affine();
    let forged_tie = arkworks_groth16::dlrep::prove_tie_aggregated::<E, _>(a_g1, x_agg, fake_u, &mut rng);

    let bundle_forged = PvugcBundle { groth16_proof: bundle.groth16_proof, dlrep_b: bundle.dlrep_b, dlrep_tie: forged_tie, gs_commitments: commitments };
    if OneSidedPvugc::verify(&bundle_forged, &pvugc_vk, &vk, &[x]) {
        panic!("Linear recombination with forged tie accepted");
    }
});


