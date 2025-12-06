//! One-Sided Decapsulation and Commitment Building
//!
//! Computes K = R^ρ using armed bases and GS commitments.
//! Also provides a simple commitment builder for PVUGC.

use crate::arming::ColumnArms;
use crate::error::{Error, Result};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField};
use ark_serialize::CanonicalSerialize;
use sha2::{Digest, Sha256};
use std::ops::Neg;

/// GS commitments for one-sided PPE
#[derive(Clone, Debug)]
pub struct OneSidedCommitments<E: Pairing> {
    /// Column commitments for B-side: X_B_j limbs per column
    pub x_b_cols: Vec<(E::G1Affine, E::G1Affine)>,
    /// Theta/C-side limbs per Υ row (keep vector for zipping to W)
    pub theta: Vec<(E::G1Affine, E::G1Affine)>,
    /// Canceller limbs for the δ-side Θ commitment (rank=1). REQUIRED.
    pub theta_delta_cancel: (E::G1Affine, E::G1Affine),
}

/// Build one-sided commitments from Groth16 proof elements and witness.
///
/// It takes the proof elements (A, C), randomizer s, and witness assignment
/// directly from the caller.
///
/// # Arguments
/// * `a` - Proof element A
/// * `c` - Proof element C
/// * `s` - Randomizer s used in proving
/// * `full_assignment` - Full assignment [1, public_inputs..., witness...]
/// * `num_instance` - Number of instance variables (including the 1-wire)
///
/// # Returns
/// `OneSidedCommitments` ready for verification and decapsulation
pub fn build_commitments<E: Pairing>(
    a: &E::G1Affine,
    c: &E::G1Affine,
    s: &E::ScalarField,
    full_assignment: &[E::ScalarField],
    num_instance: usize,
) -> OneSidedCommitments<E> {
    let a_g = a.into_group();

    // Columns: [A (aggregated public), witness columns...]
    let public_count = num_instance;
    assert!(
        public_count <= full_assignment.len(),
        "num_instance exceeds assignment length"
    );
    let witness_count = full_assignment.len().saturating_sub(public_count);
    let mut x_b_cols: Vec<(E::G1Affine, E::G1Affine)> = Vec::with_capacity(1 + witness_count);

    // Column 0: aggregated public column = 1·A
    x_b_cols.push((*a, E::G1Affine::zero()));

    // Witness columns: b_j · A aligned to witness b_g2_query entries
    for b in full_assignment.iter().skip(public_count) {
        x_b_cols.push(((a_g * b).into_affine(), E::G1Affine::zero()));
    }

    // δ-side bucket: use θ = -C + sA so e(θ, δ) = e(-C, δ) · e(A, δ)^s
    let theta0 = ((a_g * s) - c.into_group()).into_affine();

    // Derive deterministic r_Theta from (A,C,s) to simulate RAND-row
    let mut h = Sha256::new();
    let mut buf = Vec::new();
    a.serialize_compressed(&mut buf).unwrap();
    h.update(&buf);
    buf.clear();
    c.serialize_compressed(&mut buf).unwrap();
    h.update(&buf);
    buf.clear();
    h.update(&s.into_bigint().to_bytes_be());
    let bytes = h.finalize();
    let r_theta = E::ScalarField::from_le_bytes_mod_order(&bytes);
    let rand_limb = (a_g * r_theta).into_affine();

    // RAND-row limbs for Θ and matching canceller
    let theta = vec![(theta0, rand_limb)];
    let theta_delta_cancel = (rand_limb.into_group().neg().into_affine(), E::G1Affine::zero());

    OneSidedCommitments {
        x_b_cols,
        theta,
        theta_delta_cancel,
    }
}

/// Canonical decapsulation: K = R^ρ using column arms
pub fn decap<E: Pairing>(
    commitments: &OneSidedCommitments<E>,
    col_arms: &ColumnArms<E>,
) -> Result<PairingOutput<E>> {
    // Size check (always)
    if commitments.x_b_cols.len() != col_arms.y_cols_rho.len() {
        return Err(Error::MismatchedSizes);
    }

    // Subgroup checks: ONLY in debug builds (very expensive!)
    #[cfg(debug_assertions)]
    {
        use ark_ff::PrimeField;
        let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
        let is_good_g1 = |g: &E::G1Affine| {
            if g.is_zero() {
                return true;
            }
            g.mul_bigint(order).into_affine().is_zero()
        };
        for (a, b) in &commitments.x_b_cols {
            if !is_good_g1(a) || !is_good_g1(b) {
                panic!("Invalid X_B limb");
            }
        }
        for (a, b) in &commitments.theta {
            if !is_good_g1(a) || !is_good_g1(b) {
                panic!("Invalid theta limb");
            }
        }
        let (c0, c1) = commitments.theta_delta_cancel;
        if !is_good_g1(&c0) || !is_good_g1(&c1) {
            panic!("Invalid cancel limb");
        }
    }

    use ark_std::One;
    let mut k = PairingOutput::<E>(One::one());
    // Fixed-shape pairing schedule derived from pinned column counts
    let num_cols = commitments.x_b_cols.len();
    for i in 0..num_cols {
        let (x0, x1) = commitments.x_b_cols[i];
        let y_rho = col_arms.y_cols_rho[i];
        k += E::pairing(x0, y_rho);
        k += E::pairing(x1, y_rho);
    }
    let num_theta = commitments.theta.len();
    for i in 0..num_theta {
        let (t0, t1) = commitments.theta[i];
        k += E::pairing(t0, col_arms.delta_rho);
        k += E::pairing(t1, col_arms.delta_rho);
    }
    let (c0, c1) = commitments.theta_delta_cancel;
    k += E::pairing(c0, col_arms.delta_rho);
    k += E::pairing(c1, col_arms.delta_rho);
    Ok(k)
}

/// Prove a circuit and build commitments in one go.
///
/// This is useful for tests that need both a Groth16 proof and PVUGC commitments.
/// It synthesizes the circuit, samples randomizers r/s, creates the proof,
/// and builds commitments using the known assignment.
///
/// IMPORTANT: Uses PvugcReduction for the R1CS-to-QAP mapping. The proving key
/// must have been created with PvugcReduction as well.
///
/// Returns: (Proof, OneSidedCommitments, full_assignment, s)
pub fn prove_and_build_commitments<E, C, R>(
    pk: &ark_groth16::ProvingKey<E>,
    circuit: C,
    rng: &mut R,
) -> core::result::Result<
    (
        ark_groth16::Proof<E>,
        OneSidedCommitments<E>,
        Vec<E::ScalarField>,
        E::ScalarField,
    ),
    ark_relations::r1cs::SynthesisError,
>
where
    E: Pairing,
    C: ark_relations::r1cs::ConstraintSynthesizer<E::ScalarField>,
    R: ark_std::rand::Rng,
{
    use ark_ff::UniformRand;
    use ark_groth16::r1cs_to_qap::PvugcReduction;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal};

    // Sample randomizers
    let r = E::ScalarField::rand(rng);
    let s = E::ScalarField::rand(rng);

    // Synthesize circuit to get full assignment
    let cs = ConstraintSystem::<E::ScalarField>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit.generate_constraints(cs.clone())?;
    cs.finalize();

    let matrices = cs.to_matrices().expect("matrix extraction");
    let prover = cs.borrow().unwrap();
    let full_assignment: Vec<E::ScalarField> = [
        prover.instance_assignment.as_slice(),
        prover.witness_assignment.as_slice(),
    ]
    .concat();
    let num_inputs = prover.instance_assignment.len();

    // Create proof with known r, s using PvugcReduction
    let proof = ark_groth16::Groth16::<E, PvugcReduction>::create_proof_with_reduction_and_matrices(
        pk,
        r,
        s,
        &matrices,
        num_inputs,
        cs.num_constraints(),
        &full_assignment,
    )?;

    // Build commitments
    let commitments = build_commitments(&proof.a, &proof.c, &s, &full_assignment, num_inputs);

    Ok((proof, commitments, full_assignment, s))
}
