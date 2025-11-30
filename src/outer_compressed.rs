//! Outer-Compressed: Proof-of-Proof Recursion
//!
//! This module implements the outer circuit that verifies an inner Groth16 proof
//! inside a small R1CS, producing a constant-size outer proof that PVUGC can operate on.
//!
//! The implementation is parameterised over a *recursion cycle* (two pairing-friendly
//! curves whose scalar/base fields line up).  The default continues to be the
//! BLS12-377/BW6-761 cycle, but a lightweight MNT4-298/MNT6-298 pair is also exposed
//! for experimentation.  Switching cycles lets downstream callers trade security for
//! faster recursion-friendly parameter generation.

use crate::api::enforce_public_inputs_are_outputs;
use crate::ppe::PvugcVk;
use ark_crypto_primitives::snark::{BooleanInputVar, SNARKGadget};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField, Field};
use ark_groth16::constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar};
use ark_groth16::{Groth16, Proof, VerifyingKey};
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::{alloc::AllocVar, eq::EqGadget, pairing::PairingVar as PairingVarTrait};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use core::marker::PhantomData;

/// Trait describing a recursion-friendly pairing cycle.
///
/// The inner curve hosts the application circuit.  The outer curve hosts a verifier
/// gadget for the inner proof, yielding a constant-size outer Groth16 proof that PVUGC
/// can work with regardless of the application circuit size.
pub trait RecursionCycle: 'static + Send + Sync {
    type ConstraintField: PrimeField;
    type InnerE: Pairing<BaseField = Self::ConstraintField>;
    type OuterE: Pairing<ScalarField = Self::ConstraintField>;
    type InnerPairingVar: PairingVarTrait<Self::InnerE>;

    /// Human-readable name for logging/test output.
    fn name() -> &'static str;
}

/// Helper type aliases for a given cycle.
pub type InnerScalar<C> = <<C as RecursionCycle>::InnerE as Pairing>::ScalarField;
pub type OuterScalar<C> = <C as RecursionCycle>::ConstraintField;
pub type InnerProof<C> = Proof<<C as RecursionCycle>::InnerE>;
pub type OuterProof<C> = Proof<<C as RecursionCycle>::OuterE>;
pub type InnerVk<C> = VerifyingKey<<C as RecursionCycle>::InnerE>;
pub type OuterVk<C> = VerifyingKey<<C as RecursionCycle>::OuterE>;
pub type OuterPk<C> = ark_groth16::ProvingKey<<C as RecursionCycle>::OuterE>;

/// Available recursion cycles.
pub mod cycles {
    use super::*;
    use ark_r1cs_std::pairing::{
        bls12::PairingVar as Bls12PairingVar, mnt4::PairingVar as Mnt4PairingVar,
    };

    /// Default security: inner BLS12-377, outer BW6-761 (Arkworks two-cycle).
    #[derive(Debug, Clone, Copy)]
    pub struct Bls12Bw6Cycle;

    impl RecursionCycle for Bls12Bw6Cycle {
        type ConstraintField = ark_bls12_377::Fq;
        type InnerE = ark_bls12_377::Bls12_377;
        type OuterE = ark_bw6_761::BW6_761;
        type InnerPairingVar = Bls12PairingVar<ark_bls12_377::Config>;

        fn name() -> &'static str {
            "BLS12-377/BW6-761"
        }
    }

    /// Low-security (≈100-bit) experimental cycle: inner MNT4-298, outer MNT6-298.
    #[derive(Debug, Clone, Copy)]
    pub struct Mnt4Mnt6Cycle;

    impl RecursionCycle for Mnt4Mnt6Cycle {
        type ConstraintField = ark_mnt4_298::Fq;
        type InnerE = ark_mnt4_298::MNT4_298;
        type OuterE = ark_mnt6_298::MNT6_298;
        type InnerPairingVar = Mnt4PairingVar<ark_mnt4_298::Config>;

        fn name() -> &'static str {
            "MNT4-298/MNT6-298"
        }
    }
}

pub use cycles::{Bls12Bw6Cycle, Mnt4Mnt6Cycle};

/// Default cycle used across the crate unless otherwise specified.
pub type DefaultCycle = Mnt4Mnt6Cycle;

/// Convenience aliases for the default recursion cycle.
pub type InnerE = <DefaultCycle as RecursionCycle>::InnerE;
pub type OuterE = <DefaultCycle as RecursionCycle>::OuterE;
pub type InnerFr = InnerScalar<DefaultCycle>;
pub type OuterFr = OuterScalar<DefaultCycle>;
pub type InnerProofDefault = InnerProof<DefaultCycle>;
pub type OuterProofDefault = OuterProof<DefaultCycle>;
pub type InnerVkDefault = InnerVk<DefaultCycle>;
pub type OuterVkDefault = OuterVk<DefaultCycle>;
pub type OuterPkDefault = OuterPk<DefaultCycle>;

/// Convert an inner scalar field element into the outer scalar field for the provided cycle.
pub fn fr_inner_to_outer_for<C: RecursionCycle>(x: &InnerScalar<C>) -> OuterScalar<C> {
    let bytes = x.into_bigint().to_bytes_le();
    OuterScalar::<C>::from_le_bytes_mod_order(&bytes)
}

/// Default-cycle convenience wrapper around [`fr_inner_to_outer_for`].
pub fn fr_inner_to_outer(x: &InnerFr) -> OuterFr {
    fr_inner_to_outer_for::<DefaultCycle>(x)
}
#[inline]
fn inner_modulus_bits<C: RecursionCycle>() -> usize {
    InnerScalar::<C>::MODULUS_BIT_SIZE as usize
}

pub fn normalized_inner_bits_le<C: RecursionCycle>(scalar: &InnerScalar<C>) -> Vec<bool> {
    let bit_len = inner_modulus_bits::<C>();
    let mut bits = scalar.into_bigint().to_bits_le();
    bits.truncate(bit_len);
    if bits.len() < bit_len {
        bits.resize(bit_len, false);
    }
    bits
}
/// Outer circuit proving "Groth16::verify(vk_inner, x_inner, proof_inner) == true" for a cycle.
#[derive(Clone)]
pub struct OuterCircuit<C: RecursionCycle> {
    pub vk_inner: InnerVk<C>,
    pub x_inner: Vec<InnerScalar<C>>,
    pub proof_inner: InnerProof<C>,
    _cycle: PhantomData<C>,
}

impl<C: RecursionCycle> OuterCircuit<C> {
    pub fn new(
        vk_inner: InnerVk<C>,
        x_inner: Vec<InnerScalar<C>>,
        proof_inner: InnerProof<C>,
    ) -> Self {
        Self {
            vk_inner,
            x_inner,
            proof_inner,
            _cycle: PhantomData,
        }
    }
}

impl<C: RecursionCycle> ConstraintSynthesizer<OuterScalar<C>> for OuterCircuit<C> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<OuterScalar<C>>,
    ) -> Result<(), SynthesisError> {
        let vk_var = VerifyingKeyVar::<C::InnerE, C::InnerPairingVar>::new_constant(
            cs.clone(),
            &self.vk_inner,
        )?;

        let proof_var = ProofVar::<C::InnerE, C::InnerPairingVar>::new_witness(cs.clone(), || {
            Ok(self.proof_inner)
        })?;
        // BooleanInputVar handles field element conversion for recursion
        // It converts inner field elements to the outer constraint field
        let input_var =
            BooleanInputVar::<InnerScalar<C>, OuterScalar<C>>::new_input(cs.clone(), || {
                Ok(self.x_inner.clone())
            })?;

        let ok = Groth16VerifierGadget::<C::InnerE, C::InnerPairingVar>::verify(
            &vk_var, &input_var, &proof_var,
        )?;
        ok.enforce_equal(&Boolean::TRUE)?;

        Ok(())
    }
}
/// Setup outer Groth16 parameters for a given inner VK and public input count.
pub fn setup_outer_params_for<C: RecursionCycle>(
    vk_inner: &InnerVk<C>,
    n_inputs: usize,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(OuterPk<C>, OuterVk<C>), SynthesisError> {
    let dummy_x = vec![InnerScalar::<C>::from(0u64); n_inputs];
    let dummy_proof = InnerProof::<C> {
        a: Default::default(),
        b: Default::default(),
        c: Default::default(),
    };

    let circuit = OuterCircuit::<C>::new(vk_inner.clone(), dummy_x, dummy_proof);

    let (pk, vk) = Groth16::<C::OuterE>::circuit_specific_setup(circuit, rng)?;

    Ok((pk, vk))
}

/// Default-cycle convenience wrapper around [`setup_outer_params_for`].
pub fn setup_outer_params(
    vk_inner: &InnerVkDefault,
    n_inputs: usize,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(OuterPkDefault, OuterVkDefault), SynthesisError> {
    setup_outer_params_for::<DefaultCycle>(vk_inner, n_inputs, rng)
}

/// Prove outer circuit (generate proof-of-proof) for the provided cycle.
///
/// Note: BooleanInputVar compresses inner field elements for recursion efficiency.
/// This function extracts the actual compressed public inputs from the circuit.
pub fn prove_outer_for<C: RecursionCycle>(
    pk_outer: &OuterPk<C>,
    vk_inner: &InnerVk<C>,
    x_inner: &[InnerScalar<C>],
    proof_inner: &InnerProof<C>,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(OuterProof<C>, OuterVk<C>, Vec<OuterScalar<C>>), SynthesisError> {
    use ark_relations::r1cs::ConstraintSystem;

    // First, synthesize the circuit to extract the actual public inputs that BooleanInputVar creates
    // (BooleanInputVar compresses the inputs for efficiency)
    let circuit_for_extraction =
        OuterCircuit::<C>::new(vk_inner.clone(), x_inner.to_vec(), proof_inner.clone());
    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    circuit_for_extraction.generate_constraints(cs.clone())?;
    let actual_public_inputs = cs.borrow().unwrap().instance_assignment.clone();
    // Remove the constant "1" at index 0
    let actual_public_inputs: Vec<_> = actual_public_inputs.into_iter().skip(1).collect();

    // Now prove with a fresh circuit instance
    let circuit_for_proving =
        OuterCircuit::<C>::new(vk_inner.clone(), x_inner.to_vec(), proof_inner.clone());
    let proof_outer = Groth16::<C::OuterE>::prove(pk_outer, circuit_for_proving, rng)?;
    let vk_outer = pk_outer.vk.clone();

    Ok((proof_outer, vk_outer, actual_public_inputs))
}

/// Default-cycle convenience wrapper around [`prove_outer_for`].
pub fn prove_outer(
    pk_outer: &OuterPkDefault,
    vk_inner: &InnerVkDefault,
    x_inner: &[InnerFr],
    proof_inner: &InnerProofDefault,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(OuterProofDefault, OuterVkDefault, Vec<OuterFr>), SynthesisError> {
    prove_outer_for::<DefaultCycle>(pk_outer, vk_inner, x_inner, proof_inner, rng)
}

/// Verify outer Groth16 proof for the provided cycle.
///
/// Note: The public inputs must be the compressed inputs returned by `prove_outer`,
/// not the original x_inner. BooleanInputVar compresses the inner public inputs.
pub fn verify_outer_for<C: RecursionCycle>(
    vk_outer: &OuterVk<C>,
    compressed_public_inputs: &[OuterScalar<C>],
    proof_outer: &OuterProof<C>,
    pvugc_vk: Option<&PvugcVk<C::OuterE>>,
) -> Result<bool, SynthesisError> {
    let pvk = Groth16::<C::OuterE>::process_vk(vk_outer)?;
    let proof_to_check = if let Some(pvugc_vk) = pvugc_vk {    
        let mut t_acc = pvugc_vk.t_const_points_gt[0];
        for (i, x_i) in compressed_public_inputs.iter().enumerate() {
             let term = pvugc_vk.t_const_points_gt[i + 1].0.pow(&x_i.into_bigint());
             t_acc = PairingOutput(t_acc.0 * term);
        }
        
        let mut pvk_modified = pvk.clone();
        // In ark-groth16 PreparedVerifyingKey, alpha_g1_beta_g2 is E::TargetField, not PairingOutput wrapper.
        // t_acc is PairingOutput(E::TargetField).
        pvk_modified.alpha_g1_beta_g2 = pvk_modified.alpha_g1_beta_g2 * t_acc.0;
        
        return Groth16::<C::OuterE>::verify_with_processed_vk(&pvk_modified, compressed_public_inputs, proof_outer);
    } else {
        proof_outer.clone()
    };
    Groth16::<C::OuterE>::verify_with_processed_vk(&pvk, compressed_public_inputs, &proof_to_check)
}

/// Default-cycle convenience wrapper around [`verify_outer_for`].
///
/// Note: The public inputs must be the compressed inputs returned by `prove_outer`,
/// not the original x_inner. BooleanInputVar compresses the inner public inputs.
pub fn verify_outer(
    vk_outer: &OuterVkDefault,
    compressed_public_inputs: &[OuterFr],
    proof_outer: &OuterProofDefault,
    pvugc_vk: Option<&PvugcVk<OuterE>>,
) -> Result<bool, SynthesisError> {
    verify_outer_for::<DefaultCycle>(vk_outer, compressed_public_inputs, proof_outer, pvugc_vk)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_groth16::Groth16;
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;
    use ark_std::Zero;

    use crate::test_circuits::AddCircuit;
    use crate::test_fixtures::{get_fixture_bls, get_fixture_mnt};
    use std::sync::Arc;

    fn smoke_test_for_cycle<C: ProvidesFixture>() {
        let mut rng = StdRng::seed_from_u64(12345);
        let fixture = C::load_fixture();

        let (pk_outer, vk_outer) =
            setup_outer_params_for::<C>(&fixture.vk_inner, 1, &mut rng).unwrap();

        let x = InnerScalar::<C>::from(11u64);
        let public_x = vec![x];
        let circuit_inner = AddCircuit::with_public_input(x);

        let proof_inner =
            Groth16::<C::InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).unwrap();
        let pvk_inner = Groth16::<C::InnerE>::process_vk(&fixture.vk_inner).unwrap();
        assert!(Groth16::<C::InnerE>::verify_with_processed_vk(
            &pvk_inner,
            &public_x,
            &proof_inner
        )
        .unwrap());

        let (proof_outer, _, actual_public_inputs) = prove_outer_for::<C>(
            &pk_outer,
            &fixture.vk_inner,
            &public_x,
            &proof_inner,
            &mut rng,
        )
        .unwrap();

        let pvk = Groth16::<C::OuterE>::process_vk(&vk_outer).unwrap();
        let verification_result = Groth16::<C::OuterE>::verify_with_processed_vk(
            &pvk,
            &actual_public_inputs,
            &proof_outer,
        );

        assert!(
            verification_result.unwrap(),
            "Outer proof verification failed for {}",
            C::name()
        );
    }

    #[test]
    fn test_outer_circuit_setup_and_verify_default_cycle() {
        smoke_test_for_cycle::<DefaultCycle>();
    }

    #[test]
    fn test_outer_circuit_setup_and_verify_mnt_cycle() {
        smoke_test_for_cycle::<Mnt4Mnt6Cycle>();
    }

    #[test]
    #[ignore]
    fn test_pvugc_on_outer_proof_e2e() {
        use crate::coeff_recorder::SimpleCoeffRecorder;
        use crate::prover_lean::prove_lean_with_randomizers;
        use crate::stark::test_utils::{build_vdf_stark_instance, get_or_init_inner_crs_keys};
        use ark_snark::SNARK;
        use ark_std::rand::rngs::StdRng;
        use ark_std::rand::SeedableRng;
        use ark_std::UniformRand;
        use std::sync::Arc;
        use std::time::Instant;

        type Cycle = Bls12Bw6Cycle;

        let mut rng = StdRng::seed_from_u64(99999);
        let sample_instances = vec![
            build_vdf_stark_instance(3, 8),
            build_vdf_stark_instance(5, 8),
        ];
        let runtime_instance = build_vdf_stark_instance(7, 8);

        let (pk_inner, vk_inner) = get_or_init_inner_crs_keys();

        let mut sample_proofs: Vec<(InnerScalar<Cycle>, InnerProof<Cycle>)> = Vec::new();
        for inst in &sample_instances {
            let proof = Groth16::<<Cycle as RecursionCycle>::InnerE>::prove(
                &pk_inner,
                inst.circuit.clone(),
                &mut rng,
            )
            .unwrap();
            sample_proofs.push((inst.statement_hash, proof));
        }
        let runtime_inner_proof = Groth16::<<Cycle as RecursionCycle>::InnerE>::prove(
            &pk_inner,
            runtime_instance.circuit.clone(),
            &mut rng,
        )
        .unwrap();

        let (pk_outer_raw, vk_outer_raw) =
            setup_outer_params_for::<Cycle>(&vk_inner, 1, &mut rng).unwrap();
        let pk_outer = Arc::new(pk_outer_raw);
        let vk_outer = Arc::new(vk_outer_raw);

        let sample_statements: Vec<Vec<InnerScalar<Cycle>>> =
            sample_proofs.iter().map(|(stmt, _)| vec![*stmt]).collect();
        let proof_lookup = sample_proofs.clone();
        let inner_proof_generator = move |statements: &[InnerScalar<Cycle>]| {
            let target = statements
                .get(0)
                .copied()
                .unwrap_or_else(|| InnerScalar::<Cycle>::zero());
            proof_lookup
                .iter()
                .find(|(stmt, _)| *stmt == target)
                .map(|(_, proof)| proof.clone())
                .expect("missing STARK SNARK for sample statement")
        };

        let (pvugc_vk, lean_pk) =
            crate::pvugc_outer::build_pvugc_setup_from_pk_for_with_samples::<Cycle, _>(
                &pk_outer,
                &vk_inner,
                inner_proof_generator,
                sample_statements,
            );

        let public_x = vec![runtime_instance.statement_hash];
        let rho = OuterScalar::<Cycle>::rand(&mut rng);

        let outer_circuit = OuterCircuit::<Cycle>::new(
            (*vk_inner).clone(),
            public_x.clone(),
            runtime_inner_proof.clone(),
        );

        let mut recorder = SimpleCoeffRecorder::<<Cycle as RecursionCycle>::OuterE>::new();
        recorder.set_num_instance_variables(vk_outer.gamma_abc_g1.len());
        let outer_start = Instant::now();
        let r_rand = OuterScalar::<Cycle>::rand(&mut rng);
        let s_rand = OuterScalar::<Cycle>::rand(&mut rng);
        let (proof_outer, full_assignment) =
            prove_lean_with_randomizers(&lean_pk, outer_circuit, r_rand, s_rand)
                .expect("lean prover failed");
        recorder.record_from_assignment(&full_assignment, &proof_outer.a, &proof_outer.c, s_rand);
        eprintln!(
            "[timing:{}] outer Lean proof {:?}",
            Cycle::name(),
            outer_start.elapsed()
        );

        let circuit_for_extraction = OuterCircuit::<Cycle>::new(
            (*vk_inner).clone(),
            public_x.clone(),
            runtime_inner_proof.clone(),
        );
        let cs = ark_relations::r1cs::ConstraintSystem::<OuterScalar<Cycle>>::new_ref();
        circuit_for_extraction
            .generate_constraints(cs.clone())
            .expect("constraint synthesis failed");
        cs.finalize();
        let mut instance = cs.borrow().unwrap().instance_assignment.clone();
        let actual_public_inputs = instance.split_off(1);

        assert!(
            verify_outer_for::<Cycle>(
                &*vk_outer,
                &actual_public_inputs,
                &proof_outer,
                Some(&pvugc_vk)
            )
            .unwrap(),
            "Outer proof verification failed for {}",
            Cycle::name()
        );

        let run_decap = std::env::var("PVUGC_RUN_DECAP")
            .map(|flag| flag == "1" || flag.eq_ignore_ascii_case("true"))
            .unwrap_or(false);

        let bases = crate::pvugc_outer::build_column_bases_outer_for::<Cycle>(
            &pvugc_vk,
            &vk_outer,
            &actual_public_inputs,
        );
        let col_arms = crate::pvugc_outer::arm_columns_outer_for::<Cycle>(&bases, &rho);

        if run_decap {
            let decap_start = Instant::now();
            let gs_commitments = recorder.build_commitments();
            let k_decapped = crate::decap::decap(&gs_commitments, &col_arms).expect("decap failed");
            eprintln!(
                "[timing:{}] decap {:?}",
                Cycle::name(),
                decap_start.elapsed()
            );

            let r = crate::pvugc_outer::compute_target_outer_for::<Cycle>(
                &*vk_outer, &pvugc_vk, &public_x,
            );
            let k_expected = crate::pvugc_outer::compute_r_to_rho_outer_for::<Cycle>(&r, &rho);

            assert!(
                crate::ct::gt_eq_ct::<<Cycle as RecursionCycle>::OuterE>(&k_decapped, &k_expected),
                "Decapsulated K doesn't match R^ρ!"
            );
        } else {
            eprintln!(
                "[timing:{}] decap skipped (set PVUGC_RUN_DECAP=1 to enable)",
                Cycle::name(),
            );
        }
    }

    struct GlobalFixtureAdapter<C: RecursionCycle> {
        pk_inner: Arc<ark_groth16::ProvingKey<C::InnerE>>,
        vk_inner: Arc<ark_groth16::VerifyingKey<C::InnerE>>,
    }

    trait ProvidesFixture: RecursionCycle + Sized {
        fn load_fixture() -> GlobalFixtureAdapter<Self>;
    }

    impl ProvidesFixture for Bls12Bw6Cycle {
        fn load_fixture() -> GlobalFixtureAdapter<Self> {
            let fx = get_fixture_bls();
            GlobalFixtureAdapter {
                pk_inner: fx.pk_inner,
                vk_inner: fx.vk_inner,
            }
        }
    }

    impl ProvidesFixture for Mnt4Mnt6Cycle {
        fn load_fixture() -> GlobalFixtureAdapter<Self> {
            let fx = get_fixture_mnt();
            GlobalFixtureAdapter {
                pk_inner: fx.pk_inner,
                vk_inner: fx.vk_inner,
            }
        }
    }
}
