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

use crate::ppe::PvugcVk;
use ark_crypto_primitives::snark::{BooleanInputVar, SNARKGadget};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ff::{BigInteger, Field, PrimeField};
use ark_groth16::constraints::{Groth16VerifierGadget, ProofVar, VerifyingKeyVar};
use ark_r1cs_std::boolean::Boolean;
use ark_groth16::{Groth16, Proof, VerifyingKey};
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
        use ark_relations::r1cs::{LinearCombination, Variable};
        use ark_ff::One;

        // SECURE SPAN-SEPARATED PUBLIC INPUT BINDING
        //
        // Goal:
        // - Keep true public inputs out of A and B (u_pub = v_pub = 0),
        // - Bind the verifier's witness bit-decomposition to the public input,
        // - Avoid placing many bit-witness variables on the *single* public-C row.
        //
        // Construction (per public input element):
        // 1) Allocate x_pub as an input variable (public, appears only in C)
        // 2) Allocate x_wit as a witness scalar
        // 3) Constrain: 1 * reconstruct(bits) = x_wit        (witness-only row)
        // 4) Constrain: 1 * x_wit            = x_pub         (single public-C row)
        //
        // This ensures only ONE witness column (x_wit) touches the public-C row,
        // and we can omit the corresponding (0, x_wit) quotient basis from the
        // published Lean CRS and bake it via the standard–lean C-gap machinery.
        
        let one_lc = LinearCombination::from((OuterScalar::<C>::one(), Variable::One));
        
        // Step 1: Allocate public inputs x_pub and corresponding witness scalars x_wit.
        // We keep the outer-field value around so both allocations are consistent.
        let mut x_pub_vars = Vec::new();
        let mut x_wit_vars = Vec::new();
        for x_val in &self.x_inner {
            let x_outer: OuterScalar<C> = convert_inner_to_outer::<C>(*x_val);
            let x_pub = cs.new_input_variable(|| Ok(x_outer))?;
            let x_wit = cs.new_witness_variable(|| Ok(x_outer))?;
            x_pub_vars.push(x_pub);
            x_wit_vars.push(x_wit);
        }
        
        // Step 2: BooleanInputVar as WITNESS (for verifier's scalar multiplication).
        let input_var =
            BooleanInputVar::<InnerScalar<C>, OuterScalar<C>>::new_witness(cs.clone(), || {
                Ok(self.x_inner.clone())
            })?;

        // Step 3: Link public scalars to input_var bits via binding constraints.
        // For each input element, reconstruct the scalar from bits and bind it to x_wit,
        // then bind x_wit to x_pub in a single public-C row.
        for ((x_pub, x_wit), bits) in x_pub_vars
            .iter()
            .zip(x_wit_vars.iter())
            .zip(input_var.clone().into_iter())
        {
            // bits is Vec<Boolean<OuterScalar<C>>> for this input
            // Build linear combination: sum of bit_i * 2^i
            let mut reconstructed_lc = LinearCombination::<OuterScalar<C>>::zero();
            let mut power_of_two = OuterScalar::<C>::one();
            
            for bit in &bits {
                // bit.lc() gives the linear combination for this boolean
                let bit_lc = bit.lc();
                // Add power_of_two * bit to the reconstruction
                for (coeff, var) in bit_lc.iter() {
                    reconstructed_lc += (power_of_two * coeff, *var);
                }
                power_of_two = power_of_two + power_of_two;
            }
            
            // 3a) Enforce: 1 * reconstructed(bits) = x_wit  (witness-only row)
            let mut lc_c_wit = LinearCombination::<OuterScalar<C>>::zero();
            lc_c_wit += (OuterScalar::<C>::one(), *x_wit);
            cs.enforce_constraint(one_lc.clone(), reconstructed_lc, lc_c_wit)?;

            // 3b) Enforce: 1 * x_wit = x_pub  (single public-C row; public input appears only in C)
            let mut lc_b = LinearCombination::<OuterScalar<C>>::zero();
            lc_b += (OuterScalar::<C>::one(), *x_wit);
            let mut lc_c_pub = LinearCombination::<OuterScalar<C>>::zero();
            lc_c_pub += (OuterScalar::<C>::one(), *x_pub);
            cs.enforce_constraint(one_lc.clone(), lc_b, lc_c_pub)?;
        }
        
        // Step 4: Use witness input_var in verifier (now bound to x_pub!)
        let proof_var = ProofVar::<C::InnerE, C::InnerPairingVar>::new_witness(cs.clone(), || {
            Ok(self.proof_inner)
        })?;

        let ok = Groth16VerifierGadget::<C::InnerE, C::InnerPairingVar>::verify(
            &vk_var, &input_var, &proof_var,
        )?;
        ok.enforce_equal(&Boolean::TRUE)?;
        Ok(())
    }
}
/// Convert inner scalar field element to outer scalar field element.
/// For recursion-friendly cycles (BLS12-377/BW6-761), this embeds the smaller
/// inner field into the larger outer field.
fn convert_inner_to_outer<C: RecursionCycle>(x: InnerScalar<C>) -> OuterScalar<C> {
    use ark_ff::PrimeField;
    // Convert via BigInt representation
 // Convert via byte representation - works for any field pair
    let bytes = x.into_bigint().to_bytes_le();
    OuterScalar::<C>::from_le_bytes_mod_order(&bytes)
}
use ark_groth16::r1cs_to_qap::PvugcReduction;

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

    let (pk, vk) = Groth16::<C::OuterE, PvugcReduction>::circuit_specific_setup(circuit, rng)?;

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
    let proof_outer = Groth16::<C::OuterE, PvugcReduction>::prove(pk_outer, circuit_for_proving, rng)?;
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

    /// Test that our bit reconstruction matches convert_inner_to_outer.
    /// This verifies the binding constraint correctly links public inputs to verifier bits.
    #[test]
    fn test_bit_encoding_matches_convert() {
        use ark_ff::{BigInteger, PrimeField, One, Zero};
        
        // Test with several values
        let test_values = [0u64, 1, 42, 12345, u64::MAX / 2];
        
        for &val in &test_values {
            let x_inner = InnerScalar::<DefaultCycle>::from(val);
            
            // Method 1: convert_inner_to_outer (what x_pub uses)
            let x_outer_direct = convert_inner_to_outer::<DefaultCycle>(x_inner);
            
            // Method 2: reconstruct from LE bits (what binding constraint does)
            let bits = x_inner.into_bigint().to_bits_le();
            let mut x_outer_reconstructed = OuterScalar::<DefaultCycle>::zero();
            let mut power_of_two = OuterScalar::<DefaultCycle>::one();
            for bit in bits {
                if bit {
                    x_outer_reconstructed += power_of_two;
                }
                power_of_two = power_of_two + power_of_two;
            }
            
            assert_eq!(
                x_outer_direct, x_outer_reconstructed,
                "Encoding mismatch for value {}! direct={:?}, reconstructed={:?}",
                val, x_outer_direct, x_outer_reconstructed
            );
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
