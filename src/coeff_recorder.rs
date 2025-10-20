//! Coefficient Recorder for Groth16 Prover
//!
//! Hooks into ark-groth16's MSM operations to capture the coefficients b_j
//! used to build B, allowing us to compute X^(B)_j = A^b_j for the one-sided PPE.
//!
//! SECURITY: Coefficients are handled ephemerally - never stored long-term,
//! only used to compute the aggregated X values needed for GS commitments.

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_ff::{Field, Zero, One};
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
    /// Proves: B - β - query[0] = s·δ + Σ b_j·query[1..]
    pub fn create_dlrep_b<R: ark_std::rand::RngCore>(
        &self,
        pvugc_vk: &crate::api::PvugcVk<E>,
        rng: &mut R,
    ) -> crate::dlrep::DlrepBProof<E> {
        use crate::dlrep::prove_b_msm;
        use ark_ec::CurveGroup;
        
        let b_coeffs = &self.b_coeffs;  // These correspond to query[1..]
        let s = self.s.expect("s not recorded");
        
        // B'' = s·δ + Σ b_j·query[1..]
        // (NOT including β or query[0] - those are constants)
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
    /// Proves: Σ C_ℓ = u_agg · A
    pub fn create_dlrep_tie<R: ark_std::rand::RngCore>(
        &self,
        gamma: &[Vec<E::ScalarField>],
        rng: &mut R,
    ) -> crate::dlrep::DlrepTieProof<E> {
        use crate::dlrep::prove_tie_aggregated;
        use ark_ff::Zero;
        
        let a = self.a.expect("A not recorded");
        
        // Full coefficients: [1 (β), 1 (query[0]), b_1, ...]
        let mut full_coeffs = vec![E::ScalarField::one()];
        full_coeffs.push(E::ScalarField::one());
        full_coeffs.extend(self.b_coeffs.iter().copied());
        
        // u_agg = Σ_ℓ (Σ_j Γ_ℓj · coeff_j)
        let mut u_agg = E::ScalarField::zero();
        for row in gamma {
            let mut u_ell = E::ScalarField::zero();
            for (g, c) in row.iter().zip(&full_coeffs) {
                u_ell += *g * c;
            }
            u_agg += u_ell;
        }
        
        // x_agg = u_agg · A (verifier will compute Σ C_ℓ)
        let x_agg = (a.into_group() * u_agg).into_affine();
        
        prove_tie_aggregated(a, x_agg, u_agg, rng)
    }
    
    /// Build GS commitments from recorded coefficients  
    pub fn build_commitments(
        &self,
        _pvugc_vk: &crate::api::PvugcVk<E>,
        gamma: &[Vec<E::ScalarField>],
    ) -> crate::decap::OneSidedCommitments<E> {
        // Use the fixed get_aggregated_x_b (now includes constants)
        let c_rows_values = self.get_aggregated_x_b(gamma);
        let c_rows: Vec<_> = c_rows_values
            .iter()
            .map(|c| (*c, <E as Pairing>::G1Affine::zero()))
            .collect();
        
        // θ = -C (to get e(-C, δ))
        let neg_c = self.get_neg_c().expect("C not recorded");
        let theta = vec![(neg_c, <E as Pairing>::G1Affine::zero())];
        
        // This cancels the -sA part in e(-C, δ)!
        let a = self.a.expect("A not recorded").into_group();
        let s = self.s.expect("s not recorded");
        let s_a = (a * s).into_affine();
        let c_delta = (s_a, <E as Pairing>::G1Affine::zero());
        
        crate::decap::OneSidedCommitments {
            c_rows,
            theta,
            c_delta,
        }
    }
    
    /// Get aggregated X^(B) values for GS
    /// Computes row aggregates: C_ℓ = Σ Γ_ℓj · coeff_j · A
    /// where coeffs = [1 (β), 1 (query[0]), b_1, b_2, ...]
    pub fn get_aggregated_x_b(
        &self,
        gamma: &[Vec<E::ScalarField>],
    ) -> Vec<E::G1Affine> {
        let a = self.a.expect("A not recorded");
        let a_group = a.into_group();
        
        // Full coefficient vector includes constants
        // [1 for β, 1 for query[0], b_1, b_2, ...]
        let mut full_coeffs = vec![E::ScalarField::one()];  // β coefficient
        full_coeffs.push(E::ScalarField::one());  // query[0] coefficient
        full_coeffs.extend(self.b_coeffs.iter().copied());  // Variable coefficients
        
        // For each row ℓ in Γ:
        // C_ℓ = Σ_j Γ_ℓj · coeff_j · A = (Σ_j Γ_ℓj · coeff_j) · A
        let mut result = Vec::with_capacity(gamma.len());
        
        for row in gamma {
            // Compute u_ℓ = Σ_j Γ_ℓj · coeff_j
            let mut u_ell = E::ScalarField::zero();
            for (gamma_ell_j, coeff_j) in row.iter().zip(&full_coeffs) {
                u_ell += *gamma_ell_j * coeff_j;
            }
            
            // C_ℓ = u_ℓ · A
            let c_ell = (a_group * u_ell).into_affine();
            result.push(c_ell);
        }
        
        result
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
    use ark_bls12_381::{Bls12_381, Fr, G1Affine, G2Affine};
    use ark_std::UniformRand;
    
    type E = Bls12_381;
    
    #[test]
    fn test_coefficient_recording() {
        use ark_std::test_rng;
        let _rng = test_rng();
        
        let recorder = SimpleCoeffRecorder::<E>::new();
        
        // Test that recorder initializes correctly
        assert!(recorder.get_coefficients().is_none());
        
    }
    
    #[test]
    fn test_aggregated_x_computation() {
        use ark_std::test_rng;
        use ark_ec::AffineRepr;
        use ark_groth16::pvugc_hook::PvugcCoefficientHook;
        
        let mut rng = test_rng();
        
        let mut recorder = SimpleCoeffRecorder::<E>::new();
        
        let a = G1Affine::rand(&mut rng);
        let b_scalars = vec![Fr::from(2u64), Fr::from(3u64)];
        let s = Fr::from(7u64);
        let beta_g2 = G2Affine::rand(&mut rng);
        let b_g2_query = vec![G2Affine::rand(&mut rng); 2];
        
        // Call the hook method directly to populate recorder
        recorder.on_b_computed(&b_scalars, &a, &beta_g2, &b_g2_query, &s);
        
        // Gamma matrix: 4x4 identity (for [1(β), 1(query[0]), b_1, b_2])
        let gamma = vec![
            vec![Fr::from(1u64), Fr::from(0u64), Fr::from(0u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(1u64), Fr::from(0u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(0u64), Fr::from(1u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(0u64), Fr::from(0u64), Fr::from(1u64)],
        ];
        
        let x_b_agg = recorder.get_aggregated_x_b(&gamma);
        
        assert_eq!(x_b_agg.len(), 4);
        
        // C_0 = 1·A (β coefficient)
        assert_eq!(x_b_agg[0], a);
        
        // C_1 = 1·A (query[0] coefficient)
        assert_eq!(x_b_agg[1], a);
        
        // C_2 = 2·A (b_1)
        let expected_c2 = (a.into_group() * Fr::from(2u64)).into_affine();
        assert_eq!(x_b_agg[2], expected_c2);
        
        // C_3 = 3·A (b_2)
        let expected_c3 = (a.into_group() * Fr::from(3u64)).into_affine();
        assert_eq!(x_b_agg[3], expected_c3);
        
    }
}

