
use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::{pairing::{Pairing, PairingOutput}, AffineRepr, CurveGroup};
use ark_groth16::Groth16;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, ConstraintSystem};
use ark_snark::SNARK;
use ark_std::{rand::rngs::StdRng, rand::SeedableRng, UniformRand};
use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::{OneSidedPvugc, LeanProvingKey};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerScalar, InnerProof, InnerVk, RecursionCycle,
};
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for_with_samples;
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};

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
        let one = FpVar::constant(Fr::from(1));
        wit_w.mul_equals(&one, &pub_x)?;
        
        // Standard PVUGC constraint (which we just fixed to put public inputs in B, not A)
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
    let circuit = SecureCircuit {
        public_x: Some(Fr::from(10u64)),
        witness_w: Some(Fr::from(10u64)),
    };
    
    // -------------------------------------------------------------------------
    // MATRIX AUDIT (In-Test)
    // -------------------------------------------------------------------------
    println!("\n=== Starting Matrix Audit for SecureCircuit ===");
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    
    let matrices = cs.to_matrices().expect("matrix extraction");
    let num_constraints = cs.num_constraints();
    let num_pub = cs.num_instance_variables(); // 0=One, 1=public_x
    let num_wit = cs.num_witness_variables();
    
    println!("Constraints: {}", num_constraints);
    println!("Public Vars: {} (0=One, 1..=Public)", num_pub);
    
    // Extract column counts
    let mut a_cols = vec![0; num_pub + num_wit];
    let mut b_cols = vec![0; num_pub + num_wit];
    let mut c_cols = vec![0; num_pub + num_wit];
    
    for row in matrices.a.iter() {
        for &(_, col) in row { a_cols[col] += 1; }
    }
    for row in matrices.b.iter() {
        for &(_, col) in row { b_cols[col] += 1; }
    }
    for row in matrices.c.iter() {
        for &(_, col) in row { c_cols[col] += 1; }
    }
    
    // Check Public Input (Variable 1)
    let pub_idx = 1;
    println!("\n[Column {} (Public Input)]", pub_idx);
    println!("  A-count: {}", a_cols[pub_idx]);
    println!("  B-count: {}", b_cols[pub_idx]);
    println!("  C-count: {}", c_cols[pub_idx]);
    
    // VERIFICATION 1: Public Input MUST NOT be in A
    assert_eq!(a_cols[pub_idx], 0, "SECURITY FAIL: Public Input found in A-matrix!");
    println!("[PASS] Public Input is NOT in A-matrix.");
    
    // VERIFICATION 2: Public Input MUST be in B (due to enforce_public_inputs_are_outputs fix) or C
    // Our fix puts it in B. SecureCircuit puts it in C. So it should be in both or one.
    assert!(b_cols[pub_idx] > 0 || c_cols[pub_idx] > 0, "Public Input must be used in B or C");
    println!("[PASS] Public Input is used in B/C.");

    println!("=== Matrix Audit Complete ===\n");

    // -------------------------------------------------------------------------
    // ATTACK SIMULATION
    // -------------------------------------------------------------------------
    
    // Standard Groth16 Setup
    let (pk_groth, vk_groth) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    let public_inputs = vec![Fr::from(10u64)];

    // Generate PVUGC Artifacts
    let vk_inner = InnerVk::<Cycle> {
        alpha_g1: Default::default(),
        beta_g2: Default::default(),
        gamma_g2: Default::default(),
        delta_g2: Default::default(),
        gamma_abc_g1: vec![Default::default(); 2],
    };
    
    let n_inputs = 1; 
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

    // Deposit/Arming Phase
    let rho = Fr::rand(&mut rng);
    let (_, col_arms, _, k_expected) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk_groth, &public_inputs, &rho).expect("setup_and_arm");

    // Attack Attempt: Pair constructed A_pub with armed B_pub
    // A_pub = alpha + A_0 + x*A_x. Since A_x is zero (verified above), A_pub = alpha + A_0.
    
    let mut a_pub_acc = lean_pk.vk.alpha_g1.into_group();
    a_pub_acc += lean_pk.a_query[0].into_group(); // Constant term
    for (i, val) in public_inputs.iter().enumerate() {
        a_pub_acc += lean_pk.a_query[1 + i].into_group() * val;
    }
    let a_pub = a_pub_acc.into_affine();

    let d_pub = col_arms.y_cols_rho[0];
    let k_forged = E::pairing(a_pub, d_pub);

    assert_ne!(k_forged, k_expected, "SAFE: Adversary FAILED to recover K");
    println!("SUCCESS: Attack failed as expected.");
}
