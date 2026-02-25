//! Temporary investigation scratchpad.
//!
//! This file is intended for local measurement experiments and can be deleted later.

use crate::outer_compressed::{
    cycles::Mnt4Mnt6Cycle,
    InnerProof, InnerScalar, InnerVk, OuterCircuit, OuterScalar, RecursionCycle,
};
use crate::find_relation_with_nonzero_sum;
use crate::outer_compressed::{prove_outer_for, setup_outer_params_for};
use crate::pvugc_outer::build_pvugc_setup_from_pk_for;
use crate::test_circuits::AddCircuit;
use crate::{prover_lean, ColumnArms, LeanProvingKey, OneSidedPvugc, PvugcVk};
use crate::decap::{build_commitments, decap};
use ark_ec::{pairing::{Pairing, PairingOutput}, AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{FftField, Field, PrimeField};
use ark_groth16::{Groth16, VerifyingKey as Groth16VK};
use ark_groth16::r1cs_to_qap::{evaluate_constraint, PvugcReduction};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, SynthesisError,
};
use ark_snark::SNARK;
use ark_std::rand::{rngs::StdRng, CryptoRng, Rng, RngCore, SeedableRng};
use ark_std::{One, UniformRand, Zero};
use rayon::prelude::*;

pub struct SynthesizedOuterWitness<C: RecursionCycle> {
    pub num_constraints: usize,
    pub num_instance_variables: usize,
    pub num_witness_variables: usize,
    pub instance_assignment: Vec<OuterScalar<C>>,
    pub witness_assignment: Vec<OuterScalar<C>>,
}

pub struct OneRowAttackSamples<C: RecursionCycle> {
    pub touched_rows: Vec<usize>,
    pub coeffs: Vec<OuterScalar<C>>,
    pub proofs: Vec<InnerProof<C>>,
    pub errors: Vec<Vec<OuterScalar<C>>>,
    pub assignments: Vec<Vec<OuterScalar<C>>>,
}

#[derive(Clone)]
pub struct AttackerView<E: Pairing> {
    pub vk: Groth16VK<E>,
    pub public_inputs: Vec<E::ScalarField>,
    pub pvugc_vk: PvugcVk<E>,
    pub lean_pk: LeanProvingKey<E>,
    pub col_arms: ColumnArms<E>,
    pub pk_inner: Option<ark_groth16::ProvingKey<<Mnt4Mnt6Cycle as RecursionCycle>::InnerE>>,
    pub vk_inner: InnerVk<Mnt4Mnt6Cycle>,
    pub x_inner: Vec<InnerScalar<Mnt4Mnt6Cycle>>,
}

fn random_invalid_inner_proof<C: RecursionCycle, R: Rng + ?Sized>(rng: &mut R) -> InnerProof<C> {
    InnerProof::<C> {
        a: <<C as RecursionCycle>::InnerE as Pairing>::G1::rand(rng).into_affine(),
        b: <<C as RecursionCycle>::InnerE as Pairing>::G2::rand(rng).into_affine(),
        c: <<C as RecursionCycle>::InnerE as Pairing>::G1::rand(rng).into_affine(),
    }
}

fn uniform_random_inner_vk<C: RecursionCycle, R: Rng + ?Sized>(
    n_public_inputs: usize,
    rng: &mut R,
) -> InnerVk<C> {
    InnerVk::<C> {
        alpha_g1: <<C as RecursionCycle>::InnerE as Pairing>::G1::rand(rng).into_affine(),
        beta_g2: <<C as RecursionCycle>::InnerE as Pairing>::G2::rand(rng).into_affine(),
        gamma_g2: <<C as RecursionCycle>::InnerE as Pairing>::G2::rand(rng).into_affine(),
        delta_g2: <<C as RecursionCycle>::InnerE as Pairing>::G2::rand(rng).into_affine(),
        gamma_abc_g1: (0..=n_public_inputs)
            .map(|_| <<C as RecursionCycle>::InnerE as Pairing>::G1::rand(rng).into_affine())
            .collect(),
    }
}

fn synthesize_outer_with_matrices<C: RecursionCycle>(
    vk_inner: InnerVk<C>,
    x_inner: Vec<InnerScalar<C>>,
    proof_inner: InnerProof<C>,
) -> Result<
    (
        ConstraintMatrices<OuterScalar<C>>,
        Vec<OuterScalar<C>>,
        usize,
        usize,
        usize,
    ),
    SynthesisError,
> {
    let outer_circuit = OuterCircuit::<C>::new(vk_inner, x_inner, proof_inner);
    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    outer_circuit.generate_constraints(cs.clone())?;
    cs.finalize();

    let matrices = cs.to_matrices().ok_or(SynthesisError::Unsatisfiable)?;
    let cs_borrow = cs.borrow().expect("constraint system borrow");
    let mut full_assignment = cs_borrow.instance_assignment.clone();
    full_assignment.extend(cs_borrow.witness_assignment.clone());

    Ok((
        matrices,
        full_assignment,
        cs.num_constraints(),
        cs.num_instance_variables(),
        cs.num_witness_variables(),
    ))
}

fn synthesize_outer_from_explicit_inner<C: RecursionCycle>(
    vk_inner: InnerVk<C>,
    x_inner: Vec<InnerScalar<C>>,
    proof_inner: InnerProof<C>,
) -> Result<SynthesizedOuterWitness<C>, SynthesisError> {
    let outer_circuit = OuterCircuit::<C>::new(vk_inner, x_inner, proof_inner);
    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    outer_circuit.generate_constraints(cs.clone())?;
    cs.finalize();

    let cs_borrow = cs.borrow().expect("constraint system borrow");
    Ok(SynthesizedOuterWitness::<C> {
        num_constraints: cs.num_constraints(),
        num_instance_variables: cs.num_instance_variables(),
        num_witness_variables: cs.num_witness_variables(),
        instance_assignment: cs_borrow.instance_assignment.clone(),
        witness_assignment: cs_borrow.witness_assignment.clone(),
    })
}

fn row_error_vector<F: ark_ff::PrimeField>(
    matrices: &ConstraintMatrices<F>,
    full_assignment: &[F],
    num_constraints: usize,
) -> Vec<F> {
    let mut out = vec![F::zero(); num_constraints];
    for i in 0..num_constraints {
        let a: F = evaluate_constraint(&matrices.a[i], full_assignment);
        let b: F = evaluate_constraint(&matrices.b[i], full_assignment);
        let c: F = evaluate_constraint(&matrices.c[i], full_assignment);
        out[i] = a * b - c;
    }
    out
}

/// Compute full (uncut) QAP-domain error evaluations:
/// e = A_eval * B_eval - C_eval, where A/B/C are laid out over
/// domain size `num_constraints + num_instance_variables` and include
/// the public-input copy segment in A.
fn full_qap_error_vector<F: FftField>(
    matrices: &ConstraintMatrices<F>,
    full_assignment: &[F],
    num_instance_variables: usize,
    num_constraints: usize,
) -> Result<Vec<F>, SynthesisError> {
    let domain = GeneralEvaluationDomain::<F>::new(num_constraints + num_instance_variables)
        .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
    let domain_size = domain.size();

    if full_assignment.len() < num_instance_variables {
        return Err(SynthesisError::Unsatisfiable);
    }

    let mut a_eval = vec![F::zero(); domain_size];
    let mut b_eval = vec![F::zero(); domain_size];
    let mut c_eval = vec![F::zero(); domain_size];

    for i in 0..num_constraints {
        a_eval[i] = evaluate_constraint(&matrices.a[i], full_assignment);
        b_eval[i] = evaluate_constraint(&matrices.b[i], full_assignment);
        c_eval[i] = evaluate_constraint(&matrices.c[i], full_assignment);
    }

    let copy_start = num_constraints;
    let copy_end = core::cmp::min(copy_start + num_instance_variables, domain_size);
    let copy_len = copy_end.saturating_sub(copy_start);
    if copy_len > 0 {
        a_eval[copy_start..copy_end].copy_from_slice(&full_assignment[..copy_len]);
    }

    let mut out = vec![F::zero(); domain_size];
    for i in 0..domain_size {
        out[i] = a_eval[i] * b_eval[i] - c_eval[i];
    }
    Ok(out)
}

/// Compute H in evaluation form by:
/// 1) building A,B,C in coefficient form for this assignment,
/// 2) computing AB-C,
/// 3) dividing by vanishing polynomial Z with remainder,
/// 4) casting quotient back to evaluation form.
fn find_h_through_div_rem<F: FftField>(
    matrices: &ConstraintMatrices<F>,
    full_assignment: &[F],
    num_instance_variables: usize,
    num_constraints: usize,
) -> Result<Vec<F>, SynthesisError> {
    let domain = GeneralEvaluationDomain::<F>::new(num_constraints + num_instance_variables)
        .ok_or(SynthesisError::PolynomialDegreeTooLarge)?;
    let domain_size = domain.size();

    if full_assignment.len() < num_instance_variables {
        return Err(SynthesisError::Unsatisfiable);
    }

    // Build A,B,C evaluations over the full QAP domain shape.
    let mut a_eval = vec![F::zero(); domain_size];
    let mut b_eval = vec![F::zero(); domain_size];
    let mut c_eval = vec![F::zero(); domain_size];

    for i in 0..num_constraints {
        a_eval[i] = evaluate_constraint(&matrices.a[i], full_assignment);
        b_eval[i] = evaluate_constraint(&matrices.b[i], full_assignment);
        c_eval[i] = evaluate_constraint(&matrices.c[i], full_assignment);
    }
    let copy_start = num_constraints;
    let copy_end = core::cmp::min(copy_start + num_instance_variables, domain_size);
    let copy_len = copy_end.saturating_sub(copy_start);
    if copy_len > 0 {
        a_eval[copy_start..copy_end].copy_from_slice(&full_assignment[..copy_len]);
    }

    // Cast evaluations to coefficient form.
    let a_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&a_eval));
    let b_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&b_eval));
    let c_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&c_eval));

    // AB - C in coefficient form.
    let ab_minus_c_poly = &(&a_poly * &b_poly) - &c_poly;

    // Divide by vanishing polynomial Z (with remainder).
    let (h_poly, _remainder_poly) = ab_minus_c_poly.divide_by_vanishing_poly(domain);

    // Cast quotient back to evaluation form on the same domain.
    let mut h_coeff = vec![F::zero(); domain_size];
    let take = core::cmp::min(h_poly.coeffs.len(), domain_size);
    if take > 0 {
        h_coeff[..take].copy_from_slice(&h_poly.coeffs[..take]);
    }
    domain.fft_in_place(&mut h_coeff);
    Ok(h_coeff)
}

fn single_nonzero_row<F: ark_ff::PrimeField>(e: &[F]) -> Option<usize> {
    let mut idx = None;
    for (i, v) in e.iter().enumerate() {
        if v.is_zero() {
            continue;
        }
        if idx.is_some() {
            return None;
        }
        idx = Some(i);
    }
    idx
}

fn nonzero_rows<F: ark_ff::PrimeField>(e: &[F]) -> Vec<(usize, F)> {
    let mut out = Vec::new();
    for (i, v) in e.iter().enumerate() {
        if !v.is_zero() {
            out.push((i, *v));
        }
    }
    out
}

fn randomize_last_witness_variables<F: ark_ff::PrimeField, R: Rng + ?Sized>(
    full_assignment: &mut [F],
    num_instances: usize,
    num_witnesses: usize,
    how_many: usize,
    rng: &mut R,
) {
    let count = core::cmp::min(how_many, num_witnesses);
    if count == 0 {
        return;
    }
    let start = num_instances + num_witnesses - count;
    let end = num_instances + num_witnesses;
    for idx in start..end {
        let prev = full_assignment[idx];
        let mut next = F::rand(rng);
        if next == prev {
            next += F::one();
        }
        full_assignment[idx] = next;
    }
}

/// Sample three random invalid inner proofs for the same (vk, x), randomize
/// the last outer witness variable independently for each sample, then solve:
///   s1 * e1 + s2 * e2 + s3 * e3 = 0   and   s1 + s2 + s3 = 1
pub fn sample_combination<C: RecursionCycle, R: Rng + ?Sized>(
    vk_inner: InnerVk<C>,
    x_inner: Vec<InnerScalar<C>>,
    rng: &mut R,
) -> Result<OneRowAttackSamples<C>, SynthesisError> {
    const RANDOMIZED_TAIL_WITNESS_VARS: usize = 7;

    let proof0 = random_invalid_inner_proof::<C, R>(rng);
    let (matrices, mut full0, num_constraints, n_instances, n_witnesses) =
        synthesize_outer_with_matrices::<C>(vk_inner.clone(), x_inner.clone(), proof0.clone())?;
    randomize_last_witness_variables(
        &mut full0,
        n_instances,
        n_witnesses,
        RANDOMIZED_TAIL_WITNESS_VARS,
        rng,
    );
    let error0 = row_error_vector(&matrices, &full0, num_constraints);
    let touched_rows: Vec<usize> = nonzero_rows(&error0).into_iter().map(|(i, _)| i).collect();
    let d = touched_rows.len();
    if d == 0 {
        return Err(SynthesisError::Unsatisfiable);
    }
    let sample_count = d + 1;

    let mut proofs = Vec::with_capacity(sample_count);
    let mut errors = Vec::with_capacity(sample_count);
    let mut assignments = Vec::with_capacity(sample_count);
    proofs.push(proof0);
    errors.push(error0);
    assignments.push(full0);

    for _ in 1..sample_count {
        let proof = random_invalid_inner_proof::<C, R>(rng);
        let (_m, mut full, _, _, _) =
            synthesize_outer_with_matrices::<C>(vk_inner.clone(), x_inner.clone(), proof.clone())?;
        randomize_last_witness_variables(
            &mut full,
            n_instances,
            n_witnesses,
            RANDOMIZED_TAIL_WITNESS_VARS,
            rng,
        );
        let err = row_error_vector(&matrices, &full, num_constraints);
        proofs.push(proof);
        errors.push(err);
        assignments.push(full);
    }

    let errors_comp: Vec<Vec<OuterScalar<C>>> = errors
        .iter()
        .map(|err| touched_rows.iter().map(|&i| err[i]).collect())
        .collect();
    let relation = find_relation_with_nonzero_sum(&errors_comp)
        .ok_or(SynthesisError::Unsatisfiable)?;
    if relation.len() != sample_count {
        return Err(SynthesisError::Unsatisfiable);
    }
    let sum = relation.iter().fold(OuterScalar::<C>::zero(), |acc, x| acc + *x);
    let sum_inv = sum.inverse().ok_or(SynthesisError::Unsatisfiable)?;
    let coeffs: Vec<_> = relation.into_iter().map(|x| x * sum_inv).collect();

    println!("Found affine combination of size {}", coeffs.len());

    Ok(OneRowAttackSamples::<C> {
        touched_rows,
        coeffs,
        proofs,
        errors,
        assignments,
    })
}

fn measure_outer_circuit_size_for<C: RecursionCycle>() -> (usize, usize, usize) {
    let mut rng = StdRng::seed_from_u64(2026);

    // Inner circuit with exactly 1 public input.
    let x0 = InnerScalar::<C>::from(7u64);
    let inner_circuit = AddCircuit::<InnerScalar<C>>::with_public_input(x0);
    let (pk_inner, vk_inner) = Groth16::<C::InnerE>::circuit_specific_setup(inner_circuit, &mut rng)
        .expect("inner setup failed");

    let x_inner = vec![x0];
    let inner_proof = Groth16::<C::InnerE>::prove(
        &pk_inner,
        AddCircuit::<InnerScalar<C>>::with_public_input(x0),
        &mut rng,
    )
    .expect("inner prove failed");

    let synthesized =
        synthesize_outer_from_explicit_inner::<C>(vk_inner, x_inner, inner_proof)
            .expect("outer synthesis failed");

    (
        synthesized.num_constraints,
        synthesized.num_instance_variables,
        synthesized.num_witness_variables,
    )
}

pub fn solvable_setup<Rng: RngCore + CryptoRng>(
    rng: &mut Rng,
) -> (
    AttackerView<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
    PairingOutput<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
) {
    let x = InnerScalar::<Mnt4Mnt6Cycle>::rand(rng);
    setup_with_input_e2e(rng, x)
}

pub fn setup_with_input_e2e<Rng: RngCore + CryptoRng>(
    rng: &mut Rng,
    x: InnerScalar<Mnt4Mnt6Cycle>,
) -> (
    AttackerView<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
    PairingOutput<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
) {
    type C = Mnt4Mnt6Cycle;

    let inner_circuit = AddCircuit::<InnerScalar<C>>::with_public_input(x);
    let (pk_inner, vk_inner) =
        Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::circuit_specific_setup(
            inner_circuit,
            rng,
        )
        .expect("inner setup failed");
    let proof_inner = Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::prove(
        &pk_inner,
        AddCircuit::<InnerScalar<C>>::with_public_input(x),
        rng,
    )
    .expect("inner prove failed");

    // Keep RNG call-order parity with `unsolvable_setup` before outer CRS generation.
    // This burns exactly the same random draws as `uniform_random_inner_vk::<C, _>(1, rng)`.
    let _ = uniform_random_inner_vk::<C, _>(1, rng);

    let (pk_outer, vk_outer) =
        setup_outer_params_for::<C>(&vk_inner, 1, rng).expect("outer setup failed");
    let (_proof_outer, _vk_outer_check, public_inputs) =
        prove_outer_for::<C>(&pk_outer, &vk_inner, &[x], &proof_inner, rng)
            .expect("outer prove failed");

    let pk_inner_for_setup = pk_inner.clone();
    let inner_proof_generator = move |statement: &[InnerScalar<C>]| -> InnerProof<C> {
        assert_eq!(statement.len(), 1, "expected exactly one public input");
        let mut local_rng = StdRng::seed_from_u64(0xA11CE);
        Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::prove(
            &pk_inner_for_setup,
            AddCircuit::<InnerScalar<C>>::with_public_input(statement[0]),
            &mut local_rng,
        )
        .expect("inner sample proof generation failed")
    };
    let (pvugc_vk, lean_pk) =
        build_pvugc_setup_from_pk_for::<C, _>(&pk_outer, &vk_inner, inner_proof_generator);

    let rho = OuterScalar::<C>::rand(rng);
    let (_bases, col_arms, _r_baked, k) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk_outer, &public_inputs, &rho)
            .expect("setup_and_arm failed");

    (
        AttackerView {
            vk: vk_outer,
            public_inputs,
            pvugc_vk,
            lean_pk,
            col_arms,
            pk_inner: Some(pk_inner),
            vk_inner,
            x_inner: vec![x],
        },
        k,
    )
}

pub fn unsolvable_setup<Rng: RngCore + CryptoRng>(
    rng: &mut Rng,
) -> (
    AttackerView<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
    PairingOutput<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
) {
    type C = Mnt4Mnt6Cycle;
    let x = InnerScalar::<C>::rand(rng);

    // Keep a small inner PK available for proving helper parity (not linked to vk_inner below).
    let (pk_inner, _vk_inner_valid) =
        Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::circuit_specific_setup(
            AddCircuit::<InnerScalar<C>>::with_public_input(x),
            rng,
        )
        .expect("inner setup failed");
    let proof_inner = Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::prove(
        &pk_inner,
        AddCircuit::<InnerScalar<C>>::with_public_input(x),
        rng,
    )
    .expect("inner prove failed");

    // Required by request: uniformly random VK.
    let vk_inner = uniform_random_inner_vk::<C, _>(1, rng);
    let (pk_outer, vk_outer) =
        setup_outer_params_for::<C>(&vk_inner, 1, rng).expect("outer setup failed");

    // Extract compressed public inputs directly by synthesis (no outer proving needed here).
    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    let oc = OuterCircuit::<C>::new(vk_inner.clone(), vec![x], proof_inner);
    oc.generate_constraints(cs.clone()).expect("outer synthesis failed");
    cs.finalize();
    let mut public_inputs = cs.borrow().unwrap().instance_assignment.clone();
    public_inputs.remove(0); // drop constant ONE

    let pk_inner_for_setup = pk_inner.clone();
    let inner_proof_generator = move |statement: &[InnerScalar<C>]| -> InnerProof<C> {
        assert_eq!(statement.len(), 1, "expected exactly one public input");
        let mut local_rng = StdRng::seed_from_u64(0xA11CE);
        Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::prove(
            &pk_inner_for_setup,
            AddCircuit::<InnerScalar<C>>::with_public_input(statement[0]),
            &mut local_rng,
        )
        .expect("inner sample proof generation failed")
    };
    let (pvugc_vk, lean_pk) =
        build_pvugc_setup_from_pk_for::<C, _>(&pk_outer, &vk_inner, inner_proof_generator);

    let rho = OuterScalar::<C>::rand(rng);
    let (_bases, col_arms, _r_baked, k) =
        OneSidedPvugc::setup_and_arm(&pvugc_vk, &vk_outer, &public_inputs, &rho)
            .expect("setup_and_arm failed");

    (
        AttackerView {
            vk: vk_outer,
            public_inputs,
            pvugc_vk,
            lean_pk,
            col_arms,
            pk_inner: None,
            vk_inner,
            x_inner: vec![x],
        },
        k,
    )
}

pub fn decap_e2e(
    view: &AttackerView<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
) -> PairingOutput<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE> {
    type C = Mnt4Mnt6Cycle;
    let zero = OuterScalar::<C>::zero();
    let x = view.x_inner[0];
    let pk_inner = view
        .pk_inner
        .as_ref()
        .expect("decap_e2e requires AttackerView with pk_inner=Some(..)");
    let inner_proof = Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::prove(
        pk_inner,
        AddCircuit::<InnerScalar<C>>::with_public_input(x),
        &mut StdRng::seed_from_u64(0xDECAF_u64),
    )
    .expect("inner prove failed");

    let outer_circuit =
        OuterCircuit::<C>::new(view.vk_inner.clone(), view.x_inner.clone(), inner_proof);
    let (proof_lean, full_assignment) = prover_lean::prove_lean_with_randomizers(
        &view.lean_pk,
        outer_circuit,
        zero,
        zero,
    )
    .expect("lean proving failed");

    let commitments = build_commitments::<<C as RecursionCycle>::OuterE>(
        &proof_lean.a,
        &proof_lean.c,
        &zero,
        &full_assignment,
        view.vk.gamma_abc_g1.len(),
    );

    decap(&commitments, &view.col_arms).expect("decap failed")
}

fn decap_for_inner_proof(
    view: &AttackerView<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
    proof_inner: InnerProof<Mnt4Mnt6Cycle>,
) -> PairingOutput<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE> {
    type C = Mnt4Mnt6Cycle;
    let zero = OuterScalar::<C>::zero();
    let outer_circuit = OuterCircuit::<C>::new(view.vk_inner.clone(), view.x_inner.clone(), proof_inner);
    let (proof_lean, full_assignment) = prover_lean::prove_lean_with_randomizers(
        &view.lean_pk,
        outer_circuit,
        zero,
        zero,
    )
    .expect("lean proving failed");
    let commitments = build_commitments::<<C as RecursionCycle>::OuterE>(
        &proof_lean.a,
        &proof_lean.c,
        &zero,
        &full_assignment,
        view.vk.gamma_abc_g1.len(),
    );
    decap(&commitments, &view.col_arms).expect("decap failed")
}

fn fake_decap_from_full_assignment(
    view: &AttackerView<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE>,
    full_assignment: &[OuterScalar<Mnt4Mnt6Cycle>],
) -> PairingOutput<<Mnt4Mnt6Cycle as RecursionCycle>::OuterE> {
    type C = Mnt4Mnt6Cycle;
    let zero = OuterScalar::<C>::zero();
    let num_inputs = view.vk.gamma_abc_g1.len();

    assert_eq!(
        full_assignment.len(),
        view.lean_pk.a_query_wit.len(),
        "full assignment length must match a_query_wit"
    );
    assert_eq!(
        full_assignment.len(),
        view.lean_pk.b_g2_query.len(),
        "full assignment length must match b_g2_query"
    );

    let scalars_bigint: Vec<_> = full_assignment.iter().map(|s| s.into_bigint()).collect();

    // A = alpha + <a_query_wit, assignment>  (r = 0)
    let mut a_acc = view.lean_pk.vk.alpha_g1.into_group();
    a_acc += <<<C as RecursionCycle>::OuterE as Pairing>::G1 as VariableBaseMSM>::msm_bigint(
        &view.lean_pk.a_query_wit,
        &scalars_bigint,
    );

    // B = beta + <b_g2_query, assignment>  (s = 0)
    let mut b_g2_acc = view.lean_pk.vk.beta_g2.into_group();
    b_g2_acc += <<<C as RecursionCycle>::OuterE as Pairing>::G2 as VariableBaseMSM>::msm_bigint(
        &view.lean_pk.b_g2_query,
        &scalars_bigint,
    );

    // C = <l_query, witness> + sum_{(i,j)} assignment[i]*assignment[j]*h_ij  (r=s=0)
    let mut c_acc = <<C as RecursionCycle>::OuterE as Pairing>::G1::zero();
    let witness_scalars_bigint = &scalars_bigint[num_inputs..];
    assert_eq!(
        witness_scalars_bigint.len(),
        view.lean_pk.l_query.len(),
        "witness assignment length must match l_query"
    );
    c_acc += <<<C as RecursionCycle>::OuterE as Pairing>::G1 as VariableBaseMSM>::msm_bigint(
        &view.lean_pk.l_query,
        witness_scalars_bigint,
    );

    // H-term via chunked MSM (parity with lean prover performance pattern).
    const MSM_CHUNK_SIZE: usize = 1 << 20;
    let h_bases_scalars: Vec<_> = view
        .lean_pk
        .h_query_wit
        .par_iter()
        .filter_map(|(i, j, base)| {
            let ii = *i as usize;
            let jj = *j as usize;
            assert!(
                ii < full_assignment.len() && jj < full_assignment.len(),
                "h_query_wit index out of bounds: ({ii}, {jj}) for assignment len {}",
                full_assignment.len()
            );
            let coeff = full_assignment[ii] * full_assignment[jj];
            if coeff.is_zero() {
                None
            } else {
                Some((*base, coeff))
            }
        })
        .collect();

    let chunk_results: Vec<_> = h_bases_scalars
        .par_chunks(MSM_CHUNK_SIZE)
        .map(|chunk| {
            let (h_bases, h_scalars): (Vec<_>, Vec<_>) = chunk.iter().cloned().unzip();
            let h_scalars_bigint: Vec<_> = h_scalars.iter().map(|s| s.into_bigint()).collect();
            <<<C as RecursionCycle>::OuterE as Pairing>::G1 as VariableBaseMSM>::msm_bigint(
                &h_bases,
                &h_scalars_bigint,
            )
        })
        .collect();
    for partial in chunk_results {
        c_acc += partial;
    }

    let proof_lean = ark_groth16::Proof::<<C as RecursionCycle>::OuterE> {
        a: a_acc.into_affine(),
        b: b_g2_acc.into_affine(),
        c: c_acc.into_affine(),
    };

    let commitments = build_commitments::<<C as RecursionCycle>::OuterE>(
        &proof_lean.a,
        &proof_lean.c,
        &zero,
        full_assignment,
        num_inputs,
    );
    decap(&commitments, &view.col_arms).expect("decap failed")
}

fn combine_k_with_scalars<E: Pairing>(
    coeffs: &[E::ScalarField],
    ks: &[PairingOutput<E>],
) -> PairingOutput<E> {
    assert_eq!(coeffs.len(), ks.len(), "coeff and k length mismatch");
    let mut acc = PairingOutput::<E>(<<E as Pairing>::TargetField as ark_ff::Field>::ONE);
    for (s, k) in coeffs.iter().zip(ks.iter()) {
        if s.is_zero() {
            continue;
        }
        let term = k.0.pow(s.into_bigint());
        acc = PairingOutput(acc.0 * term);
    }
    acc
}


#[test]
fn scratchpad_sample_combination_checks() {
    type C = Mnt4Mnt6Cycle;
    let mut rng = StdRng::seed_from_u64(2028);

    let x0 = InnerScalar::<C>::rand(&mut rng);
    let vk_inner = uniform_random_inner_vk::<C, _>(1, &mut rng);

    let x_inner = vec![x0];
    let combo =
        sample_combination::<C, _>(vk_inner.clone(), x_inner, &mut rng).expect("sample_combination failed");

    assert_eq!(
        combo.proofs.len(),
        combo.touched_rows.len() + 1,
        "must sample d+1 proofs for d touched rows"
    );
    assert_eq!(
        combo.coeffs.len(),
        combo.proofs.len(),
        "coeff/proof count mismatch"
    );
    assert_eq!(
        combo.errors.len(),
        combo.proofs.len(),
        "error/proof count mismatch"
    );
    assert_eq!(
        combo.assignments.len(),
        combo.proofs.len(),
        "assignment/proof count mismatch"
    );
    let coeff_sum = combo
        .coeffs
        .iter()
        .fold(OuterScalar::<C>::zero(), |acc, x| acc + *x);
    assert_eq!(
        coeff_sum,
        OuterScalar::<C>::one(),
        "coefficients must sum to 1"
    );

    let n = combo.errors[0].len();
    for err in &combo.errors {
        assert_eq!(err.len(), n, "error vectors must have equal length");
    }
    for i in 0..n {
        let mut sum_i = OuterScalar::<C>::zero();
        for (s, err) in combo.coeffs.iter().zip(combo.errors.iter()) {
            sum_i += *s * err[i];
        }
        assert!(
            sum_i.is_zero(),
            "combined error must be zero at row {i}, got {:?}",
            sum_i
        );
    }

    // Validate cancellation also in full (uncut) QAP-domain error space.
    let x_inner = vec![x0];
    let (matrices, _full0_uncut, num_constraints, n_instances, _n_witnesses) =
        synthesize_outer_with_matrices::<C>(vk_inner.clone(), x_inner, combo.proofs[0].clone())
            .expect("synthesis for uncut-error check failed");
    let mut full_errors = Vec::with_capacity(combo.assignments.len());
    for assignment in &combo.assignments {
        full_errors.push(
            full_qap_error_vector::<OuterScalar<C>>(
                &matrices,
                assignment,
                n_instances,
                num_constraints,
            )
            .expect("full_qap_error_vector failed"),
        );
    }
    let full_n = full_errors[0].len();
    for err in &full_errors {
        assert_eq!(err.len(), full_n, "uncut error vectors must have equal length");
    }
    for i in 0..full_n {
        let mut sum_i = OuterScalar::<C>::zero();
        for (s, err) in combo.coeffs.iter().zip(full_errors.iter()) {
            sum_i += *s * err[i];
        }
        assert!(
            sum_i.is_zero(),
            "combined uncut error must be zero at row {i}, got {:?}",
            sum_i
        );
    }

    // Check that the same coefficients do NOT annihilate the derived H vectors.
    let x_inner = vec![x0];
    let (matrices, _full0, num_constraints, n_instances, _n_witnesses) =
        synthesize_outer_with_matrices::<C>(vk_inner, x_inner, combo.proofs[0].clone())
            .expect("synthesis for H-check failed");
    let mut h_vectors = Vec::with_capacity(combo.assignments.len());
    for assignment in &combo.assignments {
        h_vectors.push(
            find_h_through_div_rem::<OuterScalar<C>>(
                &matrices,
                assignment,
                n_instances,
                num_constraints,
            )
            .expect("find_h_through_div_rem failed"),
        );
    }
    let h_len = h_vectors[0].len();
    for h in &h_vectors {
        assert_eq!(h.len(), h_len, "H vectors must have equal length");
    }
    let mut combined_h = vec![OuterScalar::<C>::zero(); h_len];
    for (s, h) in combo.coeffs.iter().zip(h_vectors.iter()) {
        for (acc, h_i) in combined_h.iter_mut().zip(h.iter()) {
            *acc += *s * *h_i;
        }
    }
    let h_is_zero = combined_h.iter().all(|v| v.is_zero());
    assert!(
        !h_is_zero,
        "expected non-zero affine combination of H-vectors, got all-zero"
    );
}

#[test]
fn legitimate_encap_decap_flow() {
    let mut rng = StdRng::seed_from_u64(1337);
    let (view, expected_k) = solvable_setup(&mut rng);
    let decapped_k = decap_e2e(&view);
    assert_eq!(decapped_k, expected_k, "decapsulated key does not match setup key");
}

#[test]
fn fake_decap_matches_real_decap_on_valid_assignment() {
    type C = Mnt4Mnt6Cycle;

    let mut rng = StdRng::seed_from_u64(1337);
    let (view, _expected_k) = solvable_setup(&mut rng);

    let x = view.x_inner[0];
    let pk_inner = view
        .pk_inner
        .as_ref()
        .expect("solvable_setup must provide pk_inner");
    let inner_proof = Groth16::<<C as RecursionCycle>::InnerE, PvugcReduction>::prove(
        pk_inner,
        AddCircuit::<InnerScalar<C>>::with_public_input(x),
        &mut StdRng::seed_from_u64(0xDECAF_u64),
    )
    .expect("inner prove failed");

    let outer_circuit = OuterCircuit::<C>::new(view.vk_inner.clone(), view.x_inner.clone(), inner_proof);
    let (_proof_lean, full_assignment) = prover_lean::prove_lean_with_randomizers(
        &view.lean_pk,
        outer_circuit,
        OuterScalar::<C>::zero(),
        OuterScalar::<C>::zero(),
    )
    .expect("lean proving failed");

    let k_real = decap_e2e(&view);
    let k_fake = fake_decap_from_full_assignment(&view, &full_assignment);
    assert_eq!(
        k_fake, k_real,
        "fake decap must match decap_e2e on valid assignment"
    );
}

#[test]
fn attack() {
    type C = Mnt4Mnt6Cycle;
    type E = <C as RecursionCycle>::OuterE;

    let mut rng = StdRng::seed_from_u64(1337);
    let (view, target_k) = unsolvable_setup(&mut rng);
    let combo = sample_combination::<C, _>(view.vk_inner.clone(), view.x_inner.clone(), &mut rng)
        .expect("sample_combination failed");

    let total = combo.assignments.len();
    let mut ks: Vec<PairingOutput<E>> = Vec::with_capacity(total);
    for (idx, assignment) in combo.assignments.iter().enumerate() {
        let k_i = fake_decap_from_full_assignment(&view, assignment);
        println!("[scratchpad::attack] fake decap progress: {}/{}", idx + 1, total);
        ks.push(k_i);
    }
    let attack_k = combine_k_with_scalars::<E>(&combo.coeffs, &ks);
    println!(
        "[scratchpad::attack] samples={}, touched_rows={}, recovered_matches_target={}",
        combo.proofs.len(),
        combo.touched_rows.len(),
        attack_k == target_k
    );
    assert_eq!(attack_k, target_k, "attack failed to recover target key");
}
