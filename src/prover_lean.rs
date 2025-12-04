//! Lean Groth16 Prover for PVUGC
//!
//! Implements a specialized Groth16 prover that works with a "Lean CRS"
//! (stripped of Powers of Tau) by using pre-computed quotient bases H_{ij}.
//! This is required to secure the One-Sided PVUGC scheme against algebraic attacks.

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM}; // AffineRepr imported
use ark_ff::{Field, PrimeField};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::{One, UniformRand, Zero};
use rayon::prelude::*;
use std::time::Instant;


#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct LeanProof<E: Pairing> {
    pub a: E::G1Affine,
    pub b: E::G2Affine,
    pub c: E::G1Affine,
    /// Compensates for α removed from A: alpha_b = e(α, B)
    pub alpha_b: PairingOutput<E>,
    /// Compensates for s*α removed from C: alpha_c = s * e(α, δ)
    pub alpha_c: PairingOutput<E>,
}

impl<E: Pairing> LeanProof<E> {
    /// Convert to a standard Groth16 proof (discards alpha_b).
    /// Use this for standard Groth16 verification.
    pub fn to_groth16_proof(&self) -> ark_groth16::Proof<E> {
        ark_groth16::Proof {
            a: self.a,
            b: self.b,
            c: self.c,
        }
    }
}

impl<E: Pairing> From<LeanProof<E>> for ark_groth16::Proof<E> {
    fn from(lean: LeanProof<E>) -> Self {
        ark_groth16::Proof {
            a: lean.a,
            b: lean.b,
            c: lean.c,
        }
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct LeanProvingKey<E: Pairing> {
    pub vk: ark_groth16::VerifyingKey<E>,
    pub beta_g1: E::G1Affine,
    pub delta_g1: E::G1Affine,
    /// Witness-only A-query bases (public slots zeroed).
    pub a_query: Vec<E::G1Affine>,
    pub b_g1_query: Vec<E::G1Affine>,
    pub b_g2_query: Vec<E::G2Affine>,
    /// Sparse H_{ij} bases for witness terms.
    /// Format: (index_i, index_j, Base)
    /// Only non-zero bases are stored.
    pub h_query_wit: Vec<(u32, u32, E::G1Affine)>,
    pub l_query: Vec<E::G1Affine>,
    pub t_beta: PairingOutput<E>,
    pub t_delta: PairingOutput<E>,
    pub t_v: Vec<PairingOutput<E>>,
}

/// Generate a Groth16 proof using the Lean CRS.
///
/// Returns: (Proof, Full Assignment)
/// The assignment is needed to construct One-Sided Commitments for PVUGC.
///
/// This function does NOT use FFTs for the quotient polynomial.
/// Instead, it computes the quotient term C via a quadratic sum of pre-computed bases:
/// C_quotient = sum_{(i,j) in sparse} a_i a_j H_{ij}
///
/// This is O(K) where K is the number of non-zero cross-terms (proportional to constraints),
/// making it highly efficient and avoiding the O(N^2) blowup.
pub fn prove_lean<E: Pairing, C: ConstraintSynthesizer<E::ScalarField>>(
    pk: &LeanProvingKey<E>,
    circuit: C,
    mut rng: impl ark_std::rand::Rng,
) -> Result<(LeanProof<E>, Vec<E::ScalarField>), ark_relations::r1cs::SynthesisError> {
    let r = E::ScalarField::rand(&mut rng);
    let s = E::ScalarField::rand(&mut rng);
    prove_lean_with_randomizers(pk, circuit, r, s)
}

pub fn prove_lean_with_randomizers<E: Pairing, C: ConstraintSynthesizer<E::ScalarField>>(
    pk: &LeanProvingKey<E>,
    circuit: C,
    r: E::ScalarField,
    s: E::ScalarField,
) -> Result<(LeanProof<E>, Vec<E::ScalarField>), ark_relations::r1cs::SynthesisError> {
    let prove_start = Instant::now();

    // 1. Synthesize circuit to get witness assignment
    let synth_start = Instant::now();
    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();

    let _matrices = cs.to_matrices().expect("matrix extraction");

    let witness = cs.borrow().unwrap().witness_assignment.clone();
    let instance = cs.borrow().unwrap().instance_assignment.clone();

    // Full assignment = [1, public_inputs..., witness...]
    let mut full_assignment = instance.clone();
    full_assignment.extend(witness);

    let num_inputs = instance.len();
    let num_vars = full_assignment.len();
    eprintln!(
        "[LeanProver] Synthesized circuit: {} vars, {} inputs in {:.2}ms",
        num_vars,
        num_inputs,
        synth_start.elapsed().as_secs_f64() * 1000.0
    );

    // 2. Compute Randomizers r, s (Passed as arguments)
    // let r = E::ScalarField::rand(&mut rng);
    // let s = E::ScalarField::rand(&mut rng);

    // 3. Compute A' = sum a_i A_i + r delta (no alpha)
    let a_start = Instant::now();
    let mut a_acc = pk.vk.alpha_g1.into_group();
    if pk.a_query.len() != num_vars {
        return Err(ark_relations::r1cs::SynthesisError::Unsatisfiable);
    }
    let scalars_bigint: Vec<_> = full_assignment.iter().map(|s| s.into_bigint()).collect();

    let a_linear = <E::G1 as VariableBaseMSM>::msm_bigint(&pk.a_query, &scalars_bigint);
    a_acc += a_linear;
    a_acc += pk.delta_g1.into_group() * r;
    eprintln!(
        "[LeanProver] A-term MSM ({} points) in {:.2}ms",
        pk.a_query.len(),
        a_start.elapsed().as_secs_f64() * 1000.0
    );

    // 4. Compute B = beta + sum a_i B_i + s delta
    let b_start = Instant::now();
    let mut b_g2_acc = pk.vk.beta_g2.into_group();
    if pk.b_g2_query.len() != num_vars {
        return Err(ark_relations::r1cs::SynthesisError::Unsatisfiable);
    }
    let b_g2_linear = <E::G2 as VariableBaseMSM>::msm_bigint(&pk.b_g2_query, &scalars_bigint);
    b_g2_acc += b_g2_linear;
    b_g2_acc += pk.vk.delta_g2.into_group() * s;

    // B_g1 for C computation
    let mut b_g1_acc = pk.beta_g1.into_group();
    let b_g1_linear = <E::G1 as VariableBaseMSM>::msm_bigint(&pk.b_g1_query, &scalars_bigint);
    b_g1_acc += b_g1_linear;
    b_g1_acc += pk.delta_g1.into_group() * s;
    eprintln!(
        "[LeanProver] B-term MSMs ({} G1 + {} G2 points) in {:.2}ms",
        pk.b_g1_query.len(),
        pk.b_g2_query.len(),
        b_start.elapsed().as_secs_f64() * 1000.0
    );

    // 5. Compute C
    // C = sum a_i L_i + sum a_i a_j H_{ij} + s A + r B - r s delta

    let mut c_acc = E::G1::zero();

    // L-term: MSM over witness L_query
    let l_start = Instant::now();
    let witness_scalars_bigint = &scalars_bigint[num_inputs..];
    if pk.l_query.len() != witness_scalars_bigint.len() {
        return Err(ark_relations::r1cs::SynthesisError::Unsatisfiable);
    }
    let l_linear = <E::G1 as VariableBaseMSM>::msm_bigint(&pk.l_query, witness_scalars_bigint);
    c_acc += l_linear;
    eprintln!(
        "[LeanProver] L-term MSM ({} points) in {:.2}ms",
        pk.l_query.len(),
        l_start.elapsed().as_secs_f64() * 1000.0
    );

    // H-term: Sparse Quadratic Sum via parallel chunked MSM (Pippenger's algorithm)
    // Process in chunks to avoid memory pressure for very large circuits
    const MSM_CHUNK_SIZE: usize = 1 << 20; // 1M points per chunk (~48MB for G1 bases)

    // Collect non-zero contributions (parallelized)
    let h_collect_start = Instant::now();
    let h_bases_scalars: Vec<(E::G1Affine, E::ScalarField)> = pk
        .h_query_wit
        .par_iter()
        .filter_map(|(i, j, base)| {
            let idx_i = *i as usize;
            let idx_j = *j as usize;
            if idx_i < full_assignment.len() && idx_j < full_assignment.len() {
                let coeff = full_assignment[idx_i] * full_assignment[idx_j];
                if !coeff.is_zero() {
                    return Some((*base, coeff));
                }
            }
            None
        })
        .collect();

    let total_h_pairs = h_bases_scalars.len();
    let num_chunks = (total_h_pairs + MSM_CHUNK_SIZE - 1) / MSM_CHUNK_SIZE;
    eprintln!(
        "[LeanProver] H-term: {} non-zero pairs (from {} total), {} chunks. Collected in {:.2}ms (parallel)",
        total_h_pairs, pk.h_query_wit.len(), num_chunks,
        h_collect_start.elapsed().as_secs_f64() * 1000.0
    );

    // Process chunks in parallel, each chunk does its own MSM (which is also parallel internally)
    let h_msm_start = Instant::now();
    let chunk_results: Vec<E::G1> = h_bases_scalars
        .par_chunks(MSM_CHUNK_SIZE)
        .enumerate()
        .map(|(chunk_idx, chunk)| {
            let chunk_start = Instant::now();
            let (h_bases, h_scalars): (Vec<E::G1Affine>, Vec<E::ScalarField>) =
                chunk.iter().cloned().unzip();
            let h_scalars_bigint: Vec<_> = h_scalars.iter().map(|s| s.into_bigint()).collect();
            let h_msm = <E::G1 as VariableBaseMSM>::msm_bigint(&h_bases, &h_scalars_bigint);

            if num_chunks > 1 {
                eprintln!(
                    "[LeanProver] H-term chunk {}/{}: {} points in {:.2}ms",
                    chunk_idx + 1,
                    num_chunks,
                    chunk.len(),
                    chunk_start.elapsed().as_secs_f64() * 1000.0
                );
            }
            h_msm
        })
        .collect();

    // Reduce chunk results (sequential, but cheap - just a few group additions)
    for partial in chunk_results {
        c_acc += partial;
    }

    eprintln!(
        "[LeanProver] H-term MSM total: {} points in {:.2}ms (parallel chunks)",
        total_h_pairs,
        h_msm_start.elapsed().as_secs_f64() * 1000.0
    );

    // Add standard C terms (randomization for zero-knowledge)
    c_acc += a_acc * s;
    c_acc += b_g1_acc * r;
    c_acc += pk.delta_g1.into_group() * (-r * s);

    eprintln!(
        "[LeanProver] Proof complete in {:.2}ms",
        prove_start.elapsed().as_secs_f64() * 1000.0
    );

    assert!(
        !full_assignment.is_empty(),
        "full assignment must contain the constant 1 column"
    );

    if full_assignment[0] != E::ScalarField::one() {
        eprintln!(
            "[LeanProver][warn] constant term != 1: {:?}",
            full_assignment[0]
        );
    }

    let alpha_b = compute_alpha_b(&full_assignment, &s, pk);
    
    // Compute alpha_c = s * e(α, δ) to compensate for the s*α term missing from C
    // This is because C = s*A + ... and A is missing α, so C is missing s*α
    let alpha_c: PairingOutput<E> = PairingOutput(pk.t_delta.0.pow(s.into_bigint()));

    Ok((
        LeanProof {
            a: a_acc.into_affine(),
            b: b_g2_acc.into_affine(),
            c: c_acc.into_affine(),
            alpha_b,
            alpha_c,
        },
        full_assignment,
    ))
}

fn compute_alpha_b<E: Pairing>(
    full_assignment: &[E::ScalarField],
    s: &E::ScalarField,
    pk: &LeanProvingKey<E>,
) -> PairingOutput<E> {
    let mut acc = pk.t_beta.0.clone();
    assert!(
        pk.t_v.len() == full_assignment.len(),
        "t_v length ({}) must equal assignment length ({})",
        pk.t_v.len(),
        full_assignment.len()
    );
    for (coeff, tv) in full_assignment.iter().zip(pk.t_v.iter()) {
        if !coeff.is_zero() {
            let pow = tv.0.pow(coeff.into_bigint());
            acc *= pow;
        }
    }
    let delta_pow = pk.t_delta.0.pow(s.into_bigint());
    acc *= delta_pow;
    PairingOutput(acc)
}
