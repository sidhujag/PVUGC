//! PVUGC Operations on Outer Curve
//!
//! Thin wrappers that apply PVUGC column operations to the OUTER proof.
//! All PVUGC logic runs on BW6-761 (outer curve) which has constant-size right-legs.

use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::AffineRepr;
use ark_groth16::VerifyingKey as Groth16VK;
#[allow(unused_imports)]
use ark_ff::{Field, PrimeField, BigInteger};
use crate::outer_compressed::{OuterE, OuterFr, InnerFr, fr_inner_to_outer};
use crate::arming::{ColumnBases, ColumnArms};
use crate::ppe::PvugcVk;

/// Build PVUGC VK from outer Groth16 VK
///
/// Extracts the G₂ bases from the outer verifier VK.
/// These are CONSTANT SIZE (small verifier circuit).
pub fn build_pvugc_vk_outer(vk_outer: &Groth16VK<OuterE>) -> PvugcVk<OuterE> {
    // The outer VK's b_g2_query comes from the proving key
    // For the wrapper, we need access to pk.b_g2_query
    // This function will be called with the full PK available
    PvugcVk {
        beta_g2: vk_outer.beta_g2,
        delta_g2: vk_outer.delta_g2,
        b_g2_query: std::sync::Arc::new(Vec::new()), // Populated from PK
    }
}

/// Build column bases from outer PVUGC VK
///
/// Y_cols = [β₂_outer] ++ b_g2_query_outer
/// These are CONSTANT SIZE (dozens, not millions)
pub fn build_column_bases_outer(pvugc_vk: &PvugcVk<OuterE>) -> ColumnBases<OuterE> {
    let mut y_cols = vec![pvugc_vk.beta_g2];
    y_cols.extend_from_slice(&**pvugc_vk.b_g2_query);
    
    ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    }
}

/// Arm column bases with ρ (outer curve)
///
/// This is identical to the inner arming logic, just on OuterE.
pub fn arm_columns_outer(bases: &ColumnBases<OuterE>, rho: &OuterFr) -> ColumnArms<OuterE> {
    crate::arming::arm_columns(bases, rho)
}

/// Compute Groth16 target R(vk_outer, x_outer) 
///
/// This is the PPE target on the OUTER verifier.
/// Converts inner public inputs to outer field before computing.
pub fn compute_target_outer(
    vk_outer: &Groth16VK<OuterE>,
    public_inputs_inner: &[InnerFr],
) -> PairingOutput<OuterE> {
    // Convert inner Fr to outer Fr via bytes
    let x_outer: Vec<OuterFr> = public_inputs_inner.iter().map(fr_inner_to_outer).collect();
    
    // Compute L(x) = γ_abc_g1[0] + Σ x_i * γ_abc_g1[i+1]
    let mut l = vk_outer.gamma_abc_g1[0].into_group();
    for (i, xi) in x_outer.iter().enumerate() {
        l += vk_outer.gamma_abc_g1[i + 1] * xi;
    }
    
    // R = e(α,β) * e(L,γ)
    OuterE::pairing(vk_outer.alpha_g1, vk_outer.beta_g2) + OuterE::pairing(l, vk_outer.gamma_g2)
}

/// Compute R^ρ for the outer target
pub fn compute_r_to_rho_outer(
    r: &PairingOutput<OuterE>,
    rho: &OuterFr,
) -> PairingOutput<OuterE> {
    let r_to_rho = r.0.pow(&rho.into_bigint());
    PairingOutput(r_to_rho)
}

