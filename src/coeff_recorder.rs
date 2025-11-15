//! Coefficient Recorder for Groth16 Prover
//!
//! Hooks into ark-groth16's MSM operations to capture the coefficients b_j
//! used to build B, allowing us to compute X^(B)_j = A^b_j for the one-sided PPE.
//!
//! SECURITY: Coefficients are handled ephemerally - never stored long-term,
//! only used to compute the aggregated X values needed for GS commitments.

use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_groth16::pvugc_hook::PvugcCoefficientHook;
use ark_groth16::VerifyingKey as Groth16VK;

/// Coefficients extracted from Groth16 prover
pub struct BCoefficients<F: Field> {
    /// Coefficients for B = Σ b_j·Y_j + s·δ
    pub b: Vec<F>,
    /// Randomness s
    pub s: F,
}

// Re-export the trait from ark-groth16
pub use ark_groth16::pvugc_hook::PvugcCoefficientHook as CoefficientRecorder;

/// Simple recorder that computes X^(B)_j = A^b_j and stores C for negation
pub struct SimpleCoeffRecorder<E: Pairing> {
    a: Option<E::G1Affine>,
    b_coeffs: Vec<E::ScalarField>,
    s: Option<E::ScalarField>,
    c: Option<E::G1Affine>,            // For C-side (will be negated)
    b_commitment: Option<E::G2Affine>, // DLREP_B commitment for joint binding
    num_instance_variables: Option<usize>,
}

impl<E: Pairing> SimpleCoeffRecorder<E> {
    pub fn new() -> Self {
        Self {
            a: None,
            b_coeffs: Vec::new(),
            s: None,
            c: None,
            b_commitment: None,
            num_instance_variables: None,
        }
    }

    /// Record number of instance (public) variables (including 1-wire)
    pub fn set_num_instance_variables(&mut self, num: usize) {
        self.num_instance_variables = Some(num);
    }

    fn instance_variable_count(&self) -> usize {
        self.num_instance_variables
            .expect("num_instance_variables must be set before use")
    }

    /// Check if A was recorded
    pub fn has_a(&self) -> bool {
        self.a.is_some()
    }

    /// Create per-column tie proofs: for each variable column j, prove X_j = b_j · A
    pub fn create_dlrep_ties<R: ark_std::rand::RngCore + rand_core::CryptoRng>(
        &self,
        rng: &mut R,
    ) -> crate::dlrep::DlrepPerColumnTies<E> {
        use crate::dlrep::prove_ties_per_column;
        let a = self.a.expect("A not recorded");
        let a_g = a.into_group();
        let num_instance = self.instance_variable_count();
        let public_count = num_instance.saturating_sub(1);
        assert!(
            public_count <= self.b_coeffs.len(),
            "num_instance_variables exceeds coefficient count"
        );
        let x_cols: Vec<E::G1Affine> = self.b_coeffs[public_count..]
            .iter()
            .map(|b| (a_g * b).into_affine())
            .collect();
        let b_commitment = self.b_commitment.expect("DLREP_B commitment not recorded");
        prove_ties_per_column(
            a,
            &x_cols,
            &self.b_coeffs[public_count..],
            b_commitment,
            rng,
        )
    }

    /// Check if C was recorded
    pub fn has_c(&self) -> bool {
        self.c.is_some()
    }

    /// Get number of coefficients recorded
    pub fn num_coeffs(&self) -> usize {
        self.b_coeffs.len()
    }

    /// Get the raw coefficients (for PoK generation)
    pub fn get_coefficients(&self) -> Option<BCoefficients<E::ScalarField>> {
        match (&self.a, &self.s) {
            (Some(_), Some(s)) => Some(BCoefficients {
                b: self.b_coeffs.clone(),
                s: *s,
            }),
            _ => None,
        }
    }
}

impl<E: Pairing> PvugcCoefficientHook<E> for SimpleCoeffRecorder<E> {
    fn on_b_computed(
        &mut self,
        assignment: &[E::ScalarField],
        a: &E::G1Affine,
        _beta_g2: &E::G2Affine,
        _b_g2_query: &[E::G2Affine],
        s: &E::ScalarField,
    ) {
        self.a = Some(*a);
        self.b_coeffs = assignment.to_vec();
        self.s = Some(*s);
    }

    fn on_c_computed(&mut self, c: &E::G1Affine, _delta_g2: &E::G2Affine) {
        // Store C for negation in GS PPE
        // PPE uses e(-C, δ) to match Groth16 equation
        self.c = Some(*c);
    }
}

impl<E: Pairing> SimpleCoeffRecorder<E> {
    /// Get the negated C for C-side PPE
    /// Returns -C to pair with +δ
    pub fn get_neg_c(&self) -> Option<E::G1Affine> {
        self.c.map(|c| c.into_group().neg().into_affine())
    }

    /// Get C as recorded (positive)
    pub fn get_c(&self) -> Option<E::G1Affine> {
        self.c
    }

    /// Create DLREP proof for B coefficients
    /// Proves: B - β = s·δ + Σ b_j·query[j]
    pub fn create_dlrep_b<R: ark_std::rand::RngCore + rand_core::CryptoRng>(
        &mut self,
        pvugc_vk: &crate::api::PvugcVk<E>,
        vk: &Groth16VK<E>,
        public_inputs: &[E::ScalarField],
        rng: &mut R,
    ) -> crate::dlrep::DlrepBProof<E> {
        use crate::dlrep::prove_b_msm;
        use ark_ec::CurveGroup;

        let b_coeffs = &self.b_coeffs; // Full assignment coeffs
        let s = self.s.expect("s not recorded");
        let num_instance = self.instance_variable_count();
        let public_count = num_instance.saturating_sub(1);
        assert!(
            public_count <= b_coeffs.len(),
            "num_instance_variables exceeds coefficient count"
        );

        let bases = crate::api::OneSidedPvugc::build_column_bases(pvugc_vk, vk, public_inputs)
            .expect("column bases must build successfully for create_dlrep_b");
        assert!(
            bases.y_cols.len() >= 1,
            "column bases must contain aggregated public column"
        );
        let witness_b_cols = &bases.y_cols[1..];
        assert_eq!(
            witness_b_cols.len(),
            b_coeffs.len().saturating_sub(public_count),
            "witness column count mismatch"
        );

        // Variable part: s·δ + Σ b_j·query[witness_indices]
        let mut b_var = pvugc_vk.delta_g2.into_group() * s;
        for (b_j, y_j) in b_coeffs
            .iter()
            .skip(public_count)
            .zip(witness_b_cols.iter())
        {
            b_var += y_j.into_group() * b_j;
        }

        // Prove over witness-only columns
        let proof = prove_b_msm(
            b_var.into_affine(),
            witness_b_cols,
            pvugc_vk.delta_g2,
            &b_coeffs[public_count..],
            s,
            rng,
        );
        // Store the B-proof commitment for later tie binding
        self.b_commitment = Some(proof.commitment);
        proof
    }

    /// Build GS commitments from recorded coefficients (column-wise)
    pub fn build_commitments(&self) -> crate::decap::OneSidedCommitments<E> {
        // Build per-column X_B_j limbs to mirror [B_pub, witness-only columns, δ₂]
        let a = self.a.expect("A not recorded");
        let a_g = a.into_group();
        // Columns: [A (B_pub), witness columns...]
        let num_instance = self.instance_variable_count();
        let public_count = num_instance.saturating_sub(1);
        assert!(
            public_count <= self.b_coeffs.len(),
            "num_instance_variables exceeds coefficient count"
        );
        let witness_count = self.b_coeffs.len().saturating_sub(public_count);
        let mut x_b_cols: Vec<(E::G1Affine, E::G1Affine)> = Vec::with_capacity(1 + witness_count);
        // Column 0: aggregated public column = 1·A
        x_b_cols.push((a, <E as Pairing>::G1Affine::zero()));
        // Witness columns: b_j · A aligned to witness b_g2_query entries
        for b in self.b_coeffs.iter().skip(public_count) {
            x_b_cols.push(((a_g * b).into_affine(), <E as Pairing>::G1Affine::zero()));
        }
        // No explicit δ column on B-side; δ-side provides e(C,
        // δ) and e(A, s·δ) via Θ = C + sA

        // δ-side bucket: use θ = -C + sA so e(θ, δ) = e(-C, δ) · e(A, δ)^s
        // Combined with B-side (which omits the δ column), yields e(A,B) + e(-C, δ) = R
        let s = self.s.expect("s not recorded");
        let theta0 = ((a_g * s) - self.get_c().expect("C not recorded").into_group()).into_affine();
        // Derive deterministic r_Theta from (A,C,s) to simulate RAND-row and provide canceller
        use ark_ff::{BigInteger, PrimeField};
        use ark_serialize::CanonicalSerialize;
        use sha2::{Digest, Sha256};
        let mut h = Sha256::new();
        let a_aff = self.a.expect("A not recorded");
        let c_aff = self.get_c().expect("C not recorded");
        let mut buf = Vec::new();
        a_aff.serialize_compressed(&mut buf).unwrap();
        h.update(&buf);
        buf.clear();
        c_aff.serialize_compressed(&mut buf).unwrap();
        h.update(&buf);
        buf.clear();
        h.update(&s.into_bigint().to_bytes_be());
        let bytes = h.finalize();
        let r_theta = <E as Pairing>::ScalarField::from_le_bytes_mod_order(&bytes);
        let rand_limb = (a_g * r_theta).into_affine();
        // RAND-row limbs for Θ and matching canceller to neutralize rand_limb pairing against δ2
        let theta = vec![(theta0, rand_limb)];
        let theta_delta_cancel = (
            rand_limb.into_group().neg().into_affine(),
            <E as Pairing>::G1Affine::zero(),
        );

        crate::decap::OneSidedCommitments {
            x_b_cols,
            theta,
            theta_delta_cancel,
        }
    }
}

use std::ops::Neg;

impl<E: Pairing> Default for SimpleCoeffRecorder<E> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;

    type E = Bls12_381;

    #[test]
    fn test_coefficient_recording() {
        let recorder = SimpleCoeffRecorder::<E>::new();
        // Test that recorder initializes correctly
        assert!(recorder.get_coefficients().is_none());
    }
}
