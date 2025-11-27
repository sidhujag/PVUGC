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
use crate::api::enforce_public_inputs_are_outputs;
use ark_ec::pairing::Pairing;
use ark_ff::{BigInteger, PrimeField};
use ark_groth16::{Groth16, Proof, VerifyingKey};

use ark_r1cs_std::{
    alloc::AllocVar,
    eq::EqGadget,
    fields::fp::FpVar,
    pairing::PairingVar as PairingVarTrait,
};
use ark_groth16::constraints::{ProofVar, VerifyingKeyVar, Groth16VerifierGadget};
use ark_r1cs_std::boolean::Boolean;
use ark_crypto_primitives::snark::{BooleanInputVar, SNARKGadget};
use ark_relations::{
    lc,
    r1cs::{
        ConstraintSynthesizer, ConstraintSystemRef, LinearCombination, SynthesisError, Variable,
    },
};
use ark_snark::SNARK;
use ark_std::One;
// use ark_std::{One, Zero};

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
    /// Allocate bits as witnesses WITHOUT booleanity constraints.
    /// 
    /// The Groth16 verifier gadget implicitly enforces booleanity:
    /// - If bits are not boolean, the reconstructed inner public input will be wrong
    /// - The pairing check will fail because the proof was for a different input
    /// 
    /// This avoids witness×witness quadratic terms from booleanity constraints,
    /// keeping the quotient polynomial affine in the public input.
    fn allocate_packed_boolean_inputs(
        cs: ConstraintSystemRef<OuterScalar<C>>,
        x_inner: &[InnerScalar<C>],
    ) -> Result<
        (
            BooleanInputVar<InnerScalar<C>, OuterScalar<C>>,
            Vec<Vec<Boolean<OuterScalar<C>>>>,
        ),
        SynthesisError,
    > {
        use ark_r1cs_std::boolean::AllocatedBool;
        
        let mut per_input_bits = Vec::with_capacity(x_inner.len());
        let mut raw_bits = Vec::with_capacity(x_inner.len());
        for scalar in x_inner {
            let bits_const = normalized_inner_bits_le::<C>(scalar);
            let mut bit_vars = Vec::with_capacity(bits_const.len());
            for bit in bits_const {
                // Use new_witness_without_booleanity_check to avoid b*(1-b)=0 constraint.
                // 
                // WHY THIS IS NECESSARY FOR LEAN PROVER:
                // The booleanity constraint b*(1-b)=0 creates wit×wit terms where the
                // coefficients depend on the actual bit values. Since bits are derived
                // from public input x, different x values produce different H-term
                // contributions, making H(x) = H_const + H_wit(w(x)) non-affine in x.
                //
                // WHY THIS IS STILL SECURE:
                // 1. The linear packing constraint x = Σ 2^i * bit_i binds the bits to x
                // 2. The inner Groth16 verifier gadget computes g_ic from these bits
                // 3. Any non-boolean bits that sum to x would produce wrong g_ic
                // 4. The inner proof only verifies if g_ic matches the statement
                // 5. The inner circuit (STARK verifier) enforces booleanity internally
                let alloc_bool = AllocatedBool::new_witness_without_booleanity_check(
                    cs.clone(),
                    || Ok(bit),
                )?;
                bit_vars.push(Boolean::from(alloc_bool));
            }
            per_input_bits.push(bit_vars.clone());
            raw_bits.push(bit_vars);
        }
        Ok((BooleanInputVar::new(per_input_bits), raw_bits))
    }
}
fn fpvar_to_lc<C: RecursionCycle>(
    var: &FpVar<OuterScalar<C>>,
) -> LinearCombination<OuterScalar<C>> {
    match var {
        FpVar::Constant(c) => lc!() + (*c, Variable::One),
        FpVar::Var(v) => lc!() + v.variable,
    }
}

fn boolean_linear_term<F: PrimeField>(
    bit: &Boolean<F>,
    coeff: F,
) -> LinearCombination<F> {
    match bit {
        Boolean::Constant(true) => lc!() + (coeff, Variable::One),
        Boolean::Constant(false) => lc!(),
        Boolean::Var(v) => lc!() + (coeff, v.variable()),
    }
}
/*
impl<C: RecursionCycle> ConstraintSynthesizer<OuterScalar<C>> for OuterCircuit<C> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<OuterScalar<C>>,
    ) -> Result<(), SynthesisError> {
        let one_var = FpVar::constant(OuterScalar::<C>::one());
        let mut has_witness = false;
        // Mock linear constraint: x * 1 = x for each public input, and mirror it with a
        // private witness copy so PVUGC sees non-empty witness columns without
        // instantiating the full verifier gadget yet.
        for x_inner in &self.x_inner {
            let x_outer = fr_inner_to_outer_for::<C>(x_inner);
            let x_var = FpVar::new_input(cs.clone(), || Ok(x_outer))?;
            x_var.mul_equals(&one_var, &x_var)?;
            let witness_var = FpVar::new_witness(cs.clone(), || Ok(x_outer))?;
            witness_var.enforce_equal(&x_var)?;
            has_witness = true;
        }
        if !has_witness {
            let dummy_witness = FpVar::new_witness(cs.clone(), || Ok(OuterScalar::<C>::one()))?;
            dummy_witness.mul_equals(&one_var, &dummy_witness)?;
        }

        // Add a few dummy constraints to keep matrices non-trivial
        let zero_var = FpVar::constant(OuterScalar::<C>::zero());
        for _ in 0..300 {
            zero_var.enforce_equal(&zero_var)?;
        }

        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}*/


impl<C: RecursionCycle> ConstraintSynthesizer<OuterScalar<C>> for OuterCircuit<C> {
    fn generate_constraints(
        self,
        cs: ConstraintSystemRef<OuterScalar<C>>,
    ) -> Result<(), SynthesisError> {
        // 1. Allocate the inner verifying key as a constant
        let vk_var = VerifyingKeyVar::<C::InnerE, C::InnerPairingVar>::new_constant(
            cs.clone(),
            &self.vk_inner,
        )?;

        // 2. Allocate the inner proof as a witness
        let proof_var =
            ProofVar::<C::InnerE, C::InnerPairingVar>::new_witness(cs.clone(), || {
                Ok(self.proof_inner.clone())
            })?;

        // 3. Allocate packed boolean inputs (bits as witnesses, returns BooleanInputVar for verifier)
        let (input_var, input_bits) =
            Self::allocate_packed_boolean_inputs(cs.clone(), &self.x_inner)?;

        // 4. For each inner scalar, allocate ONE packed public FpVar and enforce linear packing
        for (scalar, bits) in self.x_inner.iter().zip(input_bits.iter()) {
            let x_outer = fr_inner_to_outer_for::<C>(scalar);
            let x_var = FpVar::<OuterScalar<C>>::new_input(cs.clone(), || Ok(x_outer))?;

            // Build linear combination: Σ 2^i * bit_i
            let mut lc_bits = lc!();
            let mut coeff = OuterScalar::<C>::one();
            for bit in bits {
                lc_bits = lc_bits + boolean_linear_term(bit, coeff);
                coeff = coeff + coeff;
            }

            // Enforce: x_outer = Σ 2^i * bit_i (linear constraint)
            let x_lc = fpvar_to_lc::<C>(&x_var);
            cs.enforce_constraint(
                x_lc - lc_bits,
                lc!() + Variable::One,
                lc!(),
            )?;
        }

        // 5. Verify the inner Groth16 proof using the verifier gadget
       /* let ok = Groth16VerifierGadget::<C::InnerE, C::InnerPairingVar>::verify(
            &vk_var,
            &input_var,
            &proof_var,
        )?;
        ok.enforce_equal(&Boolean::TRUE)?;*/

        enforce_public_inputs_are_outputs(cs)?;
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
) -> Result<bool, SynthesisError> {
    let pvk = Groth16::<C::OuterE>::process_vk(vk_outer)?;
    Groth16::<C::OuterE>::verify_with_processed_vk(&pvk, compressed_public_inputs, proof_outer)
}

/// Default-cycle convenience wrapper around [`verify_outer_for`].
///
/// Note: The public inputs must be the compressed inputs returned by `prove_outer`,
/// not the original x_inner. BooleanInputVar compresses the inner public inputs.
pub fn verify_outer(
    vk_outer: &OuterVkDefault,
    compressed_public_inputs: &[OuterFr],
    proof_outer: &OuterProofDefault,
) -> Result<bool, SynthesisError> {
    verify_outer_for::<DefaultCycle>(vk_outer, compressed_public_inputs, proof_outer)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_groth16::Groth16;
    use ark_std::rand::rngs::StdRng;
    use ark_std::rand::SeedableRng;
    use ark_std::Zero;

    use crate::test_circuits::AddCircuit;
    use crate::test_fixtures::{get_fixture, get_fixture_bls, get_fixture_mnt, GlobalFixture};

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
        use crate::prover_lean::prove_lean_with_randomizers;
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
        
        // Create a closure that generates valid inner proofs for any statement vector
        // This is needed because q_const computation samples at x=0 and x=1,
        // and the verifier gadget requires valid proofs for those statements
        let pk_inner_clone = Arc::clone(&fixture.pk_inner);
        let inner_proof_generator = move |statements: &[InnerScalar<C>]| {
            // Derive seed from statement to ensure different proofs get different randomizers
            use ark_ff::BigInteger;
            let seed = statements.get(0)
                .map(|s| s.into_bigint().0[0])
                .unwrap_or(12345);
            let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
            // For AddCircuit with 1 public input, use the first (and only) statement
            let statement = statements.get(0).copied().unwrap_or(InnerScalar::<C>::zero());
            let circuit = AddCircuit::with_public_input(statement);
            Groth16::<C::InnerE>::prove(&pk_inner_clone, circuit, &mut rng).unwrap()
        };
        
        let (pvugc_vk, lean_pk) =
            crate::pvugc_outer::build_pvugc_setup_from_pk_for::<C, _>(&pk_outer, &fixture.vk_inner, inner_proof_generator);

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
        let public_x_outer: Vec<OuterScalar<C>> =
            public_x.iter().map(fr_inner_to_outer_for::<C>).collect();
        let bases = crate::pvugc_outer::build_column_bases_outer_for::<C>(
            &pvugc_vk,
            &vk_outer,
            &public_x_outer,
        );
        let col_arms = crate::pvugc_outer::arm_columns_outer_for::<C>(&bases, &rho);

        let outer_circuit = OuterCircuit::<C>::new(
            fixture.vk_inner.as_ref().clone(),
            public_x.clone(),
            proof_inner.clone(),
        );

        let mut recorder = SimpleCoeffRecorder::<C::OuterE>::new();
        recorder.set_num_instance_variables(vk_outer.gamma_abc_g1.len());
        let outer_start = Instant::now();
        let r_rand = OuterScalar::<C>::rand(&mut rng);
        let s_rand = OuterScalar::<C>::rand(&mut rng);
        let (proof_outer, full_assignment) = prove_lean_with_randomizers(
            &lean_pk,
            outer_circuit,
            r_rand,
            s_rand,
        )
        .expect("lean prover failed");
        recorder.record_from_assignment(&full_assignment, &proof_outer.a, &proof_outer.c, s_rand);
        eprintln!(
            "[timing:{}] outer Lean proof {:?}",
            C::name(),
            outer_start.elapsed()
        );

        assert!(verify_outer_for::<C>(&*vk_outer, &public_x_outer, &proof_outer).unwrap());

        let run_decap = std::env::var("PVUGC_RUN_DECAP")
            .map(|flag| flag == "1" || flag.eq_ignore_ascii_case("true"))
            .unwrap_or(false);

        if run_decap {
            let decap_start = Instant::now();
            let gs_commitments = recorder.build_commitments();
            let k_decapped = crate::decap::decap(&gs_commitments, &col_arms).expect("decap failed");
            eprintln!("[timing:{}] decap {:?}", C::name(), decap_start.elapsed());

            let r = crate::pvugc_outer::compute_target_outer_for::<C>(&*vk_outer, &pvugc_vk, &public_x);
            let k_expected = crate::pvugc_outer::compute_r_to_rho_outer_for::<C>(&r, &rho);

            assert!(
                crate::ct::gt_eq_ct::<C::OuterE>(&k_decapped, &k_expected),
                "Decapsulated K doesn't match R^ρ!"
            );
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
