//! Coefficient Recorder for Groth16 Prover
//!
//! Hooks into ark-groth16's MSM operations to capture the coefficients b_j
//! used to build B, allowing us to compute X^(B)_j = A^b_j for the one-sided PPE.
//!
//! SECURITY: Coefficients are handled ephemerally - never stored long-term,
//! only used to compute the aggregated X values needed for GS commitments.

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_ff::{Field, One};
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
}

impl<E: Pairing> SimpleCoeffRecorder<E> {
    pub fn new() -> Self {
        Self {
            a: None,
            b_coeffs: Vec::new(),
            s: None,
            c: None,
        }
    }
    
    /// Check if A was recorded
    pub fn has_a(&self) -> bool {
        self.a.is_some()
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
    pub fn create_dlrep_b<R: ark_std::rand::RngCore>(
        &self,
        pvugc_vk: &crate::api::PvugcVk<E>,
        rng: &mut R,
    ) -> crate::dlrep::DlrepBProof<E> {
        use crate::dlrep::prove_b_msm;
        use ark_ec::CurveGroup;
        
        let b_coeffs = &self.b_coeffs;  // These correspond to b_g2_query[1..]
        let s = self.s.expect("s not recorded");
        
        // Variable part: s·δ + Σ b_j·query[1..] (β and query[0] handled separately)
        let mut b_var = pvugc_vk.delta_g2.into_group() * s;
        for (b_j, y_j) in b_coeffs.iter().zip(&pvugc_vk.b_g2_query[1..]) {
            b_var += y_j.into_group() * b_j;
        }
        
        // Prove over query[1..] only
        prove_b_msm(
            b_var.into_affine(),
            &pvugc_vk.b_g2_query[1..],
            pvugc_vk.delta_g2,
            b_coeffs,
            s,
            rng,
        )
    }
    
    /// Create same-scalar tie proof
    /// Column-correct path: X_agg = Σ_j X_B_j(first limb) = (Σ_j coeff_j)·A
    pub fn create_dlrep_tie<R: ark_std::rand::RngCore>(
        &self,
        rng: &mut R,
    ) -> crate::dlrep::DlrepTieProof<E> {
        use crate::dlrep::prove_tie_aggregated;
        use ark_ff::Zero;
        
        let a = self.a.expect("A not recorded");
        
        // Full coefficients aligned to columns: [1 (β), 1 (query[0]), b_1, b_2, ...]
        let mut full_coeffs = vec![E::ScalarField::one(), E::ScalarField::one()];
        full_coeffs.extend(self.b_coeffs.iter().copied());
        
        // Column aggregation: u_agg = Σ_j coeff_j to match X_agg = Σ_j coeff_j·A
        let mut u_agg = E::ScalarField::zero();
        for c in &full_coeffs { u_agg += *c; }
        
        // x_agg = u_agg · A (verifier will compute Σ C_ℓ)
        let x_agg = (a.into_group() * u_agg).into_affine();
        
        prove_tie_aggregated(a, x_agg, u_agg, rng)
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
        use ark_std::test_rng;
        let _rng = test_rng();
        
        let recorder = SimpleCoeffRecorder::<E>::new();
        
        // Test that recorder initializes correctly
        assert!(recorder.get_coefficients().is_none());
        
    }
    
}

