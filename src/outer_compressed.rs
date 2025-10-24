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

use core::marker::PhantomData;

use ark_crypto_primitives::snark::constraints::{BooleanInputVar, SNARKGadget};
use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{
    constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar},
    Groth16, Proof, VerifyingKey,
};
use ark_r1cs_std::{
    alloc::AllocVar, boolean::Boolean, eq::EqGadget, pairing::PairingVar as PairingVarTrait,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;

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
pub type DefaultCycle = Bls12Bw6Cycle;

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

        // BooleanInputVar performs a bit-decomposition and reconstruction over the constraint field,
        // giving the verifier gadget the same public inputs that Groth16 expects.  No hashing occurs.
        let input_var =
            BooleanInputVar::<InnerScalar<C>, OuterScalar<C>>::new_input(cs.clone(), || {
                Ok(self.x_inner.clone())
            })?;

        #[cfg(test)]
        {
            let instance = cs.borrow().unwrap().instance_assignment.clone();
            eprintln!(
                "         OuterCircuit[{}]: instance_assignment.len() = {}",
                C::name(),
                instance.len()
            );
            if instance.len() > 1 {
                eprintln!(
                    "         OuterCircuit[{}]: instance[1] = {:?}",
                    C::name(),
                    instance[1]
                );
            }
        }

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
pub fn prove_outer_for<C: RecursionCycle>(
    pk_outer: &OuterPk<C>,
    vk_inner: &InnerVk<C>,
    x_inner: &[InnerScalar<C>],
    proof_inner: &InnerProof<C>,
    rng: &mut (impl ark_std::rand::RngCore + ark_std::rand::CryptoRng),
) -> Result<(OuterProof<C>, OuterVk<C>, Vec<OuterScalar<C>>), SynthesisError> {
    let circuit = OuterCircuit::<C>::new(vk_inner.clone(), x_inner.to_vec(), proof_inner.clone());

    let public_inputs = x_inner
        .iter()
        .map(fr_inner_to_outer_for::<C>)
        .collect::<Vec<_>>();

    let proof_outer = Groth16::<C::OuterE>::prove(pk_outer, circuit, rng)?;
    let vk_outer = pk_outer.vk.clone();

    Ok((proof_outer, vk_outer, public_inputs))
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
pub fn verify_outer_for<C: RecursionCycle>(
    vk_outer: &OuterVk<C>,
    x_inner: &[InnerScalar<C>],
    proof_outer: &OuterProof<C>,
) -> Result<bool, SynthesisError> {
    let x_outer: Vec<_> = x_inner.iter().map(fr_inner_to_outer_for::<C>).collect();

    let pvk = Groth16::<C::OuterE>::process_vk(vk_outer)?;
    Groth16::<C::OuterE>::verify_with_processed_vk(&pvk, &x_outer, proof_outer)
}

/// Default-cycle convenience wrapper around [`verify_outer_for`].
pub fn verify_outer(
    vk_outer: &OuterVkDefault,
    x_inner: &[InnerFr],
    proof_outer: &OuterProofDefault,
) -> Result<bool, SynthesisError> {
    verify_outer_for::<DefaultCycle>(vk_outer, x_inner, proof_outer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_groth16::Groth16;
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;

    use crate::test_circuits::AddCircuit;
    use crate::test_fixtures::{get_fixture, get_fixture_mnt, GlobalFixture};

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
        e2e_outer_proof_for::<DefaultCycle>(get_fixture(), 99999);
        //e2e_outer_proof_for::<Mnt4Mnt6Cycle>(get_fixture_mnt(), 99999);
    }

    fn e2e_outer_proof_for<C: RecursionCycle>(fixture: GlobalFixture<C>, rng_seed: u64) {
        use crate::coeff_recorder::SimpleCoeffRecorder;
        use ark_snark::SNARK;
        use ark_std::rand::rngs::StdRng;
        use ark_std::rand::SeedableRng;
        use ark_std::UniformRand;
        use std::sync::Arc;
        use std::time::Instant;

        let mut rng = StdRng::seed_from_u64(rng_seed);
        eprintln!(
            "[timing:{}] outer setup cached in {:?}",
            C::name(),
            fixture.outer_setup_time
        );

        let pk_outer = Arc::clone(&fixture.pk_outer_recursive);
        let vk_outer = Arc::clone(&fixture.vk_outer_recursive);

        let x = InnerScalar::<C>::from(42u64);
        let public_x = vec![x];
        let circuit_inner = AddCircuit::with_public_input(x);
        let inner_start = Instant::now();
        let proof_inner =
            Groth16::<C::InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).unwrap();
        eprintln!(
            "[timing:{}] inner Groth16 proof {:?}",
            C::name(),
            inner_start.elapsed()
        );

        let rho = OuterScalar::<C>::rand(&mut rng);
        let pvugc_vk = fixture.pvugc_vk_outer_recursive.clone();
        let bases = crate::pvugc_outer::build_column_bases_outer_for::<C>(&pvugc_vk);
        let col_arms = crate::pvugc_outer::arm_columns_outer_for::<C>(&bases, &rho);

        let outer_circuit = OuterCircuit::<C>::new(
            fixture.vk_inner.as_ref().clone(),
            public_x.clone(),
            proof_inner.clone(),
        );

        let mut recorder = SimpleCoeffRecorder::<C::OuterE>::new();
        let outer_start = Instant::now();
        let proof_outer = ark_groth16::Groth16::<C::OuterE>::create_random_proof_with_hook(
            outer_circuit,
            &*pk_outer,
            &mut rng,
            &mut recorder,
        )
        .unwrap();
        eprintln!(
            "[timing:{}] outer Groth16 proof {:?}",
            C::name(),
            outer_start.elapsed()
        );

        assert!(verify_outer_for::<C>(&*vk_outer, &public_x, &proof_outer).unwrap());

        let run_decap = std::env::var("PVUGC_RUN_DECAP")
            .map(|flag| flag == "1" || flag.eq_ignore_ascii_case("true"))
            .unwrap_or(false);

        if run_decap {
            let decap_start = Instant::now();
            let gs_commitments = recorder.build_commitments();
            let k_decapped = crate::decap::decap(&gs_commitments, &col_arms).expect("decap failed");
            eprintln!("[timing:{}] decap {:?}", C::name(), decap_start.elapsed());

            let r = crate::pvugc_outer::compute_target_outer_for::<C>(&*vk_outer, &public_x);
            let k_expected = crate::pvugc_outer::compute_r_to_rho_outer_for::<C>(&r, &rho);

            assert!(crate::ct::gt_eq_ct::<C::OuterE>(&k_decapped, &k_expected), "Decapsulated K doesn't match R^ρ!");
        } else {
            eprintln!(
                "[timing:{}] decap skipped (set PVUGC_RUN_DECAP=1 to enable)",
                C::name(),
            );
        }
    }

    /// Adapter that materialises fixtures for either cycle without duplicating the cached setup.
    struct GlobalFixtureAdapter<C: RecursionCycle> {
        pk_inner: std::sync::Arc<ark_groth16::ProvingKey<C::InnerE>>,
        vk_inner: std::sync::Arc<ark_groth16::VerifyingKey<C::InnerE>>,
    }

    trait ProvidesFixture: RecursionCycle + Sized {
        fn load_fixture() -> GlobalFixtureAdapter<Self>;
    }

    impl ProvidesFixture for DefaultCycle {
        fn load_fixture() -> GlobalFixtureAdapter<Self> {
            let fx = get_fixture();
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
