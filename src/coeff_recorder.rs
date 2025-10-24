//! Coefficient Recorder for Groth16 Prover
//!
//! Hooks into ark-groth16's MSM operations to capture the coefficients b_j
//! used to build B, allowing us to compute X^(B)_j = A^b_j for the one-sided PPE.
//!
//! SECURITY: Coefficients are handled ephemerally - never stored long-term,
//! only used to compute the aggregated X values needed for GS commitments.

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_ff::{Field};
use ark_groth16::pvugc_hook::PvugcCoefficientHook;

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
    c: Option<E::G1Affine>,  // For C-side (will be negated)
    b_commitment: Option<E::G2Affine>, // DLREP_B commitment for joint binding
}

impl<E: Pairing> SimpleCoeffRecorder<E> {
    pub fn new() -> Self {
        Self {
            a: None,
            b_coeffs: Vec::new(),
            s: None,
            c: None,
            b_commitment: None,
        }
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
        // x_cols correspond to variable columns only (aligned with b_g2_query[1..])
        let x_cols: Vec<E::G1Affine> = self
            .b_coeffs
            .iter()
            .map(|b| (a_g * b).into_affine())
            .collect();
        let b_commitment = self.b_commitment.expect("DLREP_B commitment not recorded");
        prove_ties_per_column(a, &x_cols, &self.b_coeffs, b_commitment, rng)
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
        rng: &mut R,
    ) -> crate::dlrep::DlrepBProof<E> {
        use crate::dlrep::prove_b_msm;
        use ark_ec::CurveGroup;
        
        let b_coeffs = &self.b_coeffs;  // These correspond to b_g2_query[1..]
        let s = self.s.expect("s not recorded");

        let b_query: &[E::G2Affine] = &pvugc_vk.b_g2_query;
        let (_, variable_b_cols) = b_query
            .split_first()
            .expect("pvugc_vk.b_g2_query must contain at least one column");
        assert_eq!(
            variable_b_cols.len(),
            b_coeffs.len(),
            "mismatched DLREP coefficients vs. Groth16 B query columns",
        );

        // Variable part: s·δ + Σ b_j·query[1..] (β and query[0] handled separately)
        let mut b_var = pvugc_vk.delta_g2.into_group() * s;
        for (b_j, y_j) in b_coeffs.iter().zip(variable_b_cols) {
            b_var += y_j.into_group() * b_j;
        }

        // Prove over query[1..] only
        let proof = prove_b_msm(
            b_var.into_affine(),
            variable_b_cols,
            pvugc_vk.delta_g2,
            b_coeffs,
            s,
            rng,
        );
        // Store the B-proof commitment for later tie binding
        self.b_commitment = Some(proof.commitment);
        proof
    }
    
    /// Build GS commitments from recorded coefficients (column-wise)
    pub fn build_commitments(
        &self,
    ) -> crate::decap::OneSidedCommitments<E> {
        // Build per-column X_B_j limbs to mirror [β₂, b_g2_query[0], b_g2_query[1..], δ₂]
        let a = self.a.expect("A not recorded");
        let a_g = a.into_group();
        // Columns: [A (β), A (b_g2_query[0]), b1·A, ..., b_{n-1}·A]
        let mut x_b_cols: Vec<(E::G1Affine, E::G1Affine)> = Vec::with_capacity(2 + self.b_coeffs.len());
        // Column 0: β column = 1·A
        x_b_cols.push((a, <E as Pairing>::G1Affine::zero()));
        // Column 1: b_g2_query[0] constant row = 1·A (hook b_coeffs covers query[1..] only)
        x_b_cols.push((a, <E as Pairing>::G1Affine::zero()));
        // Columns 2.. = b_j · A aligned to b_g2_query[1..]
        for b in self.b_coeffs.iter() {
            x_b_cols.push(((a_g * b).into_affine(), <E as Pairing>::G1Affine::zero()));
        }
        // No explicit δ column on B-side; δ-side provides e(C,
        // δ) and e(A, s·δ) via Θ = C + sA

        // δ-side bucket: use θ = -C + sA so e(θ, δ) = e(-C, δ) · e(A, δ)^s
        // Combined with B-side (which omits the δ column), yields e(A,B) + e(-C, δ) = R
        let s = self.s.expect("s not recorded");
        let theta0 = ((a_g * s) - self.get_c().expect("C not recorded").into_group()).into_affine();
        // Derive deterministic r_Theta from (A,C,s) to simulate RAND-row and provide canceller
        use sha2::{Sha256, Digest};
        use ark_ff::{PrimeField, BigInteger};
        use ark_serialize::CanonicalSerialize;
        let mut h = Sha256::new();
        let a_aff = self.a.expect("A not recorded");
        let c_aff = self.get_c().expect("C not recorded");
        let mut buf = Vec::new();
        a_aff.serialize_compressed(&mut buf).unwrap();
        h.update(&buf); buf.clear();
        c_aff.serialize_compressed(&mut buf).unwrap();
        h.update(&buf); buf.clear();
        h.update(&s.into_bigint().to_bytes_be());
        let bytes = h.finalize();
        let r_theta = <E as Pairing>::ScalarField::from_le_bytes_mod_order(&bytes);
        let rand_limb = (a_g * r_theta).into_affine();
        // RAND-row limbs for Θ and matching canceller to neutralize rand_limb pairing against δ2
        let theta = vec![(theta0, rand_limb)];
        let theta_delta_cancel = (rand_limb.into_group().neg().into_affine(), <E as Pairing>::G1Affine::zero());
        
        crate::decap::OneSidedCommitments { x_b_cols, theta, theta_delta_cancel }
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

