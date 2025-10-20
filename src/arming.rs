//! One-Sided Arming for PVUGC
//!
//! Arms statement-only G₂ bases (Y_j, δ) with ρ for permissionless decap.

use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, AffineRepr};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_ff::Zero;

/// Statement-only row bases (before arming)
#[derive(Clone, Debug)]
pub struct RowBases<E: Pairing> {
    /// U_ℓ = Σ Γ_ℓj·Y_j (aggregated B-side bases)
    pub u_rows: Vec<E::G2Affine>,
    
    /// W = +δ (C-side base, typically single element)
    pub w_rows: Vec<E::G2Affine>,
    
    /// Rank decomposition matrix Γ
    pub gamma: Vec<Vec<E::ScalarField>>,
}

/// Armed bases (ρ-powered, published at deposit)
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct Arms<E: Pairing> {
    /// U_ℓ^ρ
    pub u_rows_rho: Vec<E::G2Affine>,
    
    /// W^ρ
    pub w_rows_rho: Vec<E::G2Affine>,
}

/// Arm the statement-only bases with ρ
///
/// This is done ONCE at deposit time
pub fn arm_rows<E: Pairing>(
    rows: &RowBases<E>,
    rho: &E::ScalarField,
) -> Arms<E> {
    // Arm U rows
    let u_rows_rho: Vec<E::G2Affine> = rows.u_rows
        .iter()
        .map(|u| (u.into_group() * rho).into_affine())
        .collect();
    
    // Arm W rows  
    let w_rows_rho: Vec<E::G2Affine> = rows.w_rows
        .iter()
        .map(|w| (w.into_group() * rho).into_affine())
        .collect();
    
    Arms {
        u_rows_rho,
        w_rows_rho,
    }
}

/// Build statement-only row bases from Groth16 VK
///
/// Creates U_ℓ = Σ Γ_ℓj·Y_j using rank decomposition
///
/// IMPORTANT: Uses +δ (not -δ) to match Groth16 equation
pub fn build_row_bases_from_vk<E: Pairing>(
    y_bases: &[E::G2Affine],
    delta: E::G2Affine,  // POSITIVE delta!
    gamma: Vec<Vec<E::ScalarField>>,
) -> RowBases<E> {
    let num_rows = gamma.len();
    let mut u_rows = Vec::with_capacity(num_rows);
    
    // For each row ℓ: U_ℓ = Σ_j Γ_ℓj · Y_j
    for row in &gamma {
        let mut u_ell = E::G2::zero();
        
        for (gamma_ell_j, y_j) in row.iter().zip(y_bases) {
            if !gamma_ell_j.is_zero() {
                u_ell += y_j.into_group() * gamma_ell_j;
            }
        }
        
        u_rows.push(u_ell.into_affine());
    }
    
    // W rows: Just +δ for now (can be expanded)
    // IMPORTANT: Positive delta to match e(C,δ) in Groth16
    let w_rows = vec![delta];
    
    RowBases {
        u_rows,
        w_rows,
        gamma,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, Fr, G2Affine};
    use ark_std::UniformRand;
    use ark_ec::AffineRepr;
    
    type E = Bls12_381;
    
    #[test]
    fn test_row_bases_construction() {
        use ark_std::test_rng;
        let mut rng = test_rng();
        
        // Create Y bases
        let y_bases = vec![
            G2Affine::rand(&mut rng),
            G2Affine::rand(&mut rng),
        ];
        
        let neg_delta = G2Affine::rand(&mut rng);
        
        // Gamma: Identity 2x2
        let gamma = vec![
            vec![Fr::from(1u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(1u64)],
        ];
        
        let rows: RowBases<E> = build_row_bases_from_vk(&y_bases, neg_delta, gamma);
        
        assert_eq!(rows.u_rows.len(), 2);
        assert_eq!(rows.w_rows.len(), 1);
        
        // U_0 should equal Y_0
        assert_eq!(rows.u_rows[0], y_bases[0]);
        
        // U_1 should equal Y_1
        assert_eq!(rows.u_rows[1], y_bases[1]);
        
    }
    
    #[test]
    fn test_arming() {
        use ark_std::test_rng;
        let mut rng = test_rng();
        
        let y_bases = vec![G2Affine::rand(&mut rng); 2];
        let delta = G2Affine::rand(&mut rng);  // Positive delta
        let gamma = vec![
            vec![Fr::from(1u64), Fr::from(0u64)],
            vec![Fr::from(0u64), Fr::from(1u64)],
        ];
        
        let rows: RowBases<E> = build_row_bases_from_vk(&y_bases, delta, gamma);
        
        let rho = Fr::rand(&mut rng);
        let arms = arm_rows(&rows, &rho);
        
        assert_eq!(arms.u_rows_rho.len(), 2);
        assert_eq!(arms.w_rows_rho.len(), 1);
        
        // Verify arming: U_0^ρ = ρ·U_0
        let expected_u0 = (rows.u_rows[0].into_group() * rho).into_affine();
        assert_eq!(arms.u_rows_rho[0], expected_u0);
        
    }
}

