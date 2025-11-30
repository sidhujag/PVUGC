
use ark_ec::{pairing::{Pairing, PairingOutput}, AffineRepr, CurveGroup};
use ark_groth16::Groth16;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar; // Import FieldVar trait
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_snark::SNARK;
use ark_std::{rand::rngs::StdRng, rand::SeedableRng, UniformRand};
use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::{OneSidedPvugc, LeanProvingKey};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerScalar, InnerProof, InnerVk, RecursionCycle,
};
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for_with_samples;

type Cycle = DefaultCycle;
type E = <Cycle as RecursionCycle>::OuterE;
type Fr = <E as Pairing>::ScalarField;

// Use explicit types for the inner curve to avoid ambiguity
type InnerE = <Cycle as RecursionCycle>::InnerE;
type InnerG1Affine = <InnerE as Pairing>::G1Affine;
type InnerG2Affine = <InnerE as Pairing>::G2Affine;

/// A Secure Circuit that puts Public Input in C, not A.
/// Constraint: witness_w * 1 = public_x
/// A = witness_w, B = 1, C = public_x
#[derive(Clone)]
struct SecureCircuit {
    pub public_x: Option<Fr>,
    pub witness_w: Option<Fr>,
}

impl ConstraintSynthesizer<Fr> for SecureCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        // Allocate public input (ensure it's not put in A by default logic)
        // We enforce it via a specific constraint structure.
        let pub_x = FpVar::new_input(cs.clone(), || {
            self.public_x.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let wit_w = FpVar::new_witness(cs.clone(), || {
            self.witness_w.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        // Enforce: wit_w * 1 = pub_x
        // This puts wit_w in A, 1 in B, pub_x in C.
        // Public input x ends up ONLY in C (and B for '1' term maybe), but NOT A.
        let one = FpVar::constant(Fr::from(1));
        
        // This enforces a * b = c
        // We want a = wit_w, b = 1, c = pub_x
        wit_w.mul_equals(&one, &pub_x)?;
        
        // Standard PVUGC constraint
        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

// Mock inner proof generator
fn mock_inner_proof_generator(_: &[InnerScalar<Cycle>]) -> InnerProof<Cycle> {
    use ark_groth16::Proof;
    Proof {
        a: InnerG1Affine::zero(),
        b: InnerG2Affine::zero(),
        c: InnerG1Affine::zero(),
    }
}

#[test]
fn confirm_attack_fails_on_secure_circuit() {
    let mut rng = StdRng::seed_from_u64(0);

    // 1. Setup Secure Circuit
    // w * 1 = x -> 10 * 1 = 10
    let circuit = SecureCircuit {
        public_x: Some(Fr::from(10u64)),
        witness_w: Some(Fr::from(10u64)),
    };
    
    // Standard Groth16 Setup
    let (pk_groth, vk_groth) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let public_inputs = vec![Fr::from(10u64)];

    // 2. Generate PVUGC Artifacts
    let vk_inner = InnerVk::<Cycle> {
        alpha_g1: Default::default(),
        beta_g2: Default::default(),
        gamma_g2: Default::default(),
        delta_g2: Default::default(),
        gamma_abc_g1: vec![Default::default(); 2],
    };
    
    let n_inputs = 1; // 1 public input
    let mut samples = Vec::new();
    for _ in 0..=n_inputs {
        samples.push(vec![InnerScalar::<Cycle>::from(0); 1]);
    }

    let (pvugc_vk, lean_pk) = build_pvugc_setup_from_pk_for_with_samples::<Cycle, _>(
        &pk_groth,
        &vk_inner,
        mock_inner_proof_generator,
        samples
    );

    // 3. Deposit/Arming Phase
    let rho = Fr::rand(&mut rng);
    let (_, col_arms, _, k_expected) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk_groth, &public_inputs, &rho).expect("setup_and_arm");

    // -------------------------------------------------------------------------
    // ADVERSARY ATTACK ATTEMPT
    // -------------------------------------------------------------------------
    
    println!("Adversary performing attack on SecureCircuit...");

    // Attack Step 1: Attempt to reconstruct A_pub using `lean_pk.a_query`
    // Since the circuit puts public inputs in C, the A-basis for the public input should be ZERO.
    // A_pub = alpha + A_0 + x * A_x
    // If A_x is zero, then A_pub = alpha + A_0.
    
    let mut a_pub_acc = lean_pk.vk.alpha_g1.into_group();
    a_pub_acc += lean_pk.a_query[0].into_group(); // Constant term
    for (i, val) in public_inputs.iter().enumerate() {
        // We use the same formula as before, blindly trusting a_query
        a_pub_acc += lean_pk.a_query[1 + i].into_group() * val;
    }
    let a_pub = a_pub_acc.into_affine();

    // Attack Step 2: Get Armed B_pub from `col_arms`
    let d_pub = col_arms.y_cols_rho[0];

    // Attack Step 3: Pair them
    let k_forged = E::pairing(a_pub, d_pub);

    // -------------------------------------------------------------------------
    // VERIFICATION: Attack MUST Fail
    // -------------------------------------------------------------------------
    
    // The True Target K involves the witness term (A_wit * B_pub).
    // The adversary only computed (A_pub * B_pub)^rho.
    // If A_pub != A_full (which it isn't, because A_wit exists), these should differ.
    
    assert_ne!(k_forged, k_expected, "SAFE: Adversary FAILED to recover K (Attack thwarted by Secure Circuit!)");
    
    println!("SUCCESS: The 'No Public A' defense successfully blocked the attack.");
}
