
use ark_bls12_381::{Bls12_381};
use ark_ec::{pairing::{Pairing, PairingOutput}, AffineRepr, CurveGroup};
use ark_groth16::Groth16;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError, ConstraintSystem};
use ark_snark::SNARK;
use ark_std::{rand::rngs::StdRng, rand::SeedableRng, UniformRand};
use arkworks_groth16::api::enforce_public_inputs_are_outputs;
use arkworks_groth16::{OneSidedPvugc, LeanProvingKey};
use arkworks_groth16::outer_compressed::{
    DefaultCycle, InnerScalar, InnerProof, InnerVk, RecursionCycle, OuterCircuit,
    fr_inner_to_outer_for
};
use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for_with_samples;
use ark_poly::{GeneralEvaluationDomain, EvaluationDomain};

type Cycle = DefaultCycle;
type E = <Cycle as RecursionCycle>::OuterE;
type OuterFr = <E as Pairing>::ScalarField;

// Use explicit types for the inner curve to avoid ambiguity
type InnerE = <Cycle as RecursionCycle>::InnerE;
type InnerG1Affine = <InnerE as Pairing>::G1Affine;
type InnerG2Affine = <InnerE as Pairing>::G2Affine;

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

    // 1. Setup REAL Outer Circuit
    let vk_inner = InnerVk::<Cycle> {
        alpha_g1: Default::default(),
        beta_g2: Default::default(),
        gamma_g2: Default::default(),
        delta_g2: Default::default(),
        gamma_abc_g1: vec![Default::default(); 2],
    };
    let inner_proof = mock_inner_proof_generator(&[]);
    let x_inner = vec![InnerScalar::<Cycle>::from(1u64)];
    
    // We use the actual OuterCircuit from outer_compressed.rs
    // This circuit uses Groth16VerifierGadget which handles public inputs correctly (in C, not A)
    let circuit = OuterCircuit::<Cycle>::new(
        vk_inner.clone(),
        x_inner.clone(),
        inner_proof
    );
    
    // -------------------------------------------------------------------------
    // MATRIX AUDIT (In-Test)
    // -------------------------------------------------------------------------
    println!("\n=== Starting Matrix Audit for REAL OuterCircuit ===");
    let cs = ConstraintSystem::<OuterFr>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).unwrap();
    cs.finalize();
    
    let matrices = cs.to_matrices().expect("matrix extraction");
    let num_constraints = cs.num_constraints();
    let num_pub = cs.num_instance_variables(); 
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
    // OuterCircuit public input is the hash of the inner statement (1 field element)
    let pub_idx = 1;
    println!("\n[Column {} (Public Input)]", pub_idx);
    println!("  A-count: {}", a_cols[pub_idx]);
    println!("  B-count: {}", b_cols[pub_idx]);
    println!("  C-count: {}", c_cols[pub_idx]);
    
    // VERIFICATION 1: Public Input MUST NOT be in A
    assert_eq!(a_cols[pub_idx], 0, "SECURITY FAIL: Public Input found in A-matrix!");
    println!("[PASS] Public Input is NOT in A-matrix.");
    
    // VERIFICATION 2: Public Input MUST be in B (and C)
    assert!(b_cols[pub_idx] > 0, "Public Input MUST be used in B-matrix for statement dependency!");
    println!("[PASS] Public Input is used in B/C.");

    println!("=== Matrix Audit Complete ===\n");

    // -------------------------------------------------------------------------
    // ATTACK SIMULATION
    // -------------------------------------------------------------------------
    
    // Standard Groth16 Setup
    let (pk_groth, vk_groth) = Groth16::<E>::circuit_specific_setup(circuit.clone(), &mut rng).unwrap();
    
    // Public input for OuterCircuit is the outer-field representation of x_inner
    let public_inputs = vec![fr_inner_to_outer_for::<Cycle>(&x_inner[0])];

    // Generate PVUGC Artifacts
    let mut samples = Vec::new();
    samples.push(vec![InnerScalar::<Cycle>::from(0); 1]);
    samples.push(vec![InnerScalar::<Cycle>::from(1); 1]);

    let (pvugc_vk, lean_pk) = build_pvugc_setup_from_pk_for_with_samples::<Cycle, _>(
        &pk_groth,
        &vk_inner,
        mock_inner_proof_generator,
        samples
    );

    // Deposit/Arming Phase
    let rho = OuterFr::rand(&mut rng);
    let (_, col_arms, _, k_expected) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk_groth, &public_inputs, &rho).expect("setup_and_arm");

    // Attack Attempt: Pair constructed A_pub with armed B_pub
    
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
