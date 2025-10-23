//! PVUGC Operations on Outer Curve
//!
//! Thin wrappers that apply PVUGC column operations to the OUTER proof.
//! All PVUGC logic runs on BW6-761 (outer curve) which has constant-size right-legs.

use crate::arming::{ColumnArms, ColumnBases};
use crate::outer_compressed::{
    fr_inner_to_outer_for, DefaultCycle, InnerFr, InnerScalar, OuterE, OuterFr, OuterScalar,
    RecursionCycle,
};
use crate::ppe::PvugcVk;
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::AffineRepr;
#[allow(unused_imports)]
use ark_ff::{BigInteger, Field, PrimeField};
use ark_groth16::VerifyingKey as Groth16VK;

/// Build PVUGC VK from outer Groth16 VK
///
/// Extracts the G₂ bases from the outer verifier VK.
/// These are CONSTANT SIZE (small verifier circuit).
pub fn build_pvugc_vk_outer_for<C: RecursionCycle>(
    vk_outer: &Groth16VK<C::OuterE>,
) -> PvugcVk<C::OuterE> {
    // The outer VK's b_g2_query comes from the proving key
    // For the wrapper, we need access to pk.b_g2_query
    // This function will be called with the full PK available
    PvugcVk {
        beta_g2: vk_outer.beta_g2,
        delta_g2: vk_outer.delta_g2,
        b_g2_query: std::sync::Arc::new(Vec::new()), // Populated from PK
    }
}

/// Default-cycle convenience wrapper around [`build_pvugc_vk_outer_for`].
pub fn build_pvugc_vk_outer(vk_outer: &Groth16VK<OuterE>) -> PvugcVk<OuterE> {
    build_pvugc_vk_outer_for::<DefaultCycle>(vk_outer)
}

/// Build column bases from outer PVUGC VK
///
/// Y_cols = [β₂_outer] ++ b_g2_query_outer
/// These are CONSTANT SIZE (dozens, not millions)
pub fn build_column_bases_outer_for<C: RecursionCycle>(
    pvugc_vk: &PvugcVk<C::OuterE>,
) -> ColumnBases<C::OuterE> {
    let mut y_cols = vec![pvugc_vk.beta_g2];
    y_cols.extend_from_slice(&**pvugc_vk.b_g2_query);

    ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    }
}

/// Default-cycle convenience wrapper around [`build_column_bases_outer_for`].
pub fn build_column_bases_outer(pvugc_vk: &PvugcVk<OuterE>) -> ColumnBases<OuterE> {
    build_column_bases_outer_for::<DefaultCycle>(pvugc_vk)
}

/// Arm column bases with ρ (outer curve)
///
/// This is identical to the inner arming logic, just on OuterE.
pub fn arm_columns_outer_for<C: RecursionCycle>(
    bases: &ColumnBases<C::OuterE>,
    rho: &OuterScalar<C>,
) -> ColumnArms<C::OuterE> {
    crate::arming::arm_columns(bases, rho).expect("arm_columns failed")
}

/// Default-cycle convenience wrapper around [`arm_columns_outer_for`].
pub fn arm_columns_outer(bases: &ColumnBases<OuterE>, rho: &OuterFr) -> ColumnArms<OuterE> {
    arm_columns_outer_for::<DefaultCycle>(bases, rho)
}

/// Compute Groth16 target R(vk_outer, x_outer)
///
/// This is the PPE target on the OUTER verifier.
/// Converts inner public inputs to outer field before computing.
pub fn compute_target_outer_for<C: RecursionCycle>(
    vk_outer: &Groth16VK<C::OuterE>,
    public_inputs_inner: &[InnerScalar<C>],
) -> PairingOutput<C::OuterE> {
    // Convert inner Fr to outer Fr via bytes
    let x_outer: Vec<OuterScalar<C>> = public_inputs_inner
        .iter()
        .map(fr_inner_to_outer_for::<C>)
        .collect();

    // Compute L(x) = γ_abc_g1[0] + Σ x_i * γ_abc_g1[i+1]
    let mut l = vk_outer.gamma_abc_g1[0].into_group();
    for (i, xi) in x_outer.iter().enumerate() {
        l += vk_outer.gamma_abc_g1[i + 1] * xi;
    }

    // R = e(α,β) * e(L,γ)
    C::OuterE::pairing(vk_outer.alpha_g1, vk_outer.beta_g2)
        + C::OuterE::pairing(l, vk_outer.gamma_g2)
}

/// Default-cycle convenience wrapper around [`compute_target_outer_for`].
pub fn compute_target_outer(
    vk_outer: &Groth16VK<OuterE>,
    public_inputs_inner: &[InnerFr],
) -> PairingOutput<OuterE> {
    compute_target_outer_for::<DefaultCycle>(vk_outer, public_inputs_inner)
}

/// Compute R^ρ for the outer target
pub fn compute_r_to_rho_outer_for<C: RecursionCycle>(
    r: &PairingOutput<C::OuterE>,
    rho: &OuterScalar<C>,
) -> PairingOutput<C::OuterE> {
    let r_to_rho = r.0.pow(&rho.into_bigint());
    PairingOutput(r_to_rho)
}

/// Default-cycle convenience wrapper around [`compute_r_to_rho_outer_for`].
pub fn compute_r_to_rho_outer(r: &PairingOutput<OuterE>, rho: &OuterFr) -> PairingOutput<OuterE> {
    compute_r_to_rho_outer_for::<DefaultCycle>(r, rho)
}
