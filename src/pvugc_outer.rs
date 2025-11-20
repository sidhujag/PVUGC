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

/// Build PVUGC VK from the OUTER proving key (populates b_g2_query)
///
/// These right-legs are constant size for the small outer verifier circuit.
pub fn build_pvugc_vk_outer_from_pk_for<C: RecursionCycle>(
    pk_outer: &ark_groth16::ProvingKey<C::OuterE>,
) -> PvugcVk<C::OuterE> {
    PvugcVk {
        beta_g2: pk_outer.vk.beta_g2,
        delta_g2: pk_outer.vk.delta_g2,
        b_g2_query: std::sync::Arc::new(pk_outer.b_g2_query.clone()),
    }
}

/// Default-cycle convenience wrapper around [`build_pvugc_vk_outer_from_pk_for`].
pub fn build_pvugc_vk_outer_from_pk(pk_outer: &ark_groth16::ProvingKey<OuterE>) -> PvugcVk<OuterE> {
    build_pvugc_vk_outer_from_pk_for::<DefaultCycle>(pk_outer)
}

/// Build column bases from outer PVUGC VK for the specific statement
///
/// Column 0 aggregates the public Groth16 inputs; remaining columns correspond
/// to witness-only rows.
pub fn build_column_bases_outer_for<C: RecursionCycle>(
    pvugc_vk: &PvugcVk<C::OuterE>,
    vk_outer: &Groth16VK<C::OuterE>,
    public_inputs_outer: &[OuterScalar<C>],
) -> ColumnBases<C::OuterE> {
    use ark_ec::CurveGroup;

    let total_instance = vk_outer.gamma_abc_g1.len();
    assert!(total_instance > 0, "Groth16 VK must expose inputs");
    let expected_inputs = total_instance - 1;
    assert!(
        public_inputs_outer.len() == expected_inputs,
        "public input length mismatch"
    );

    let mut aggregate = pvugc_vk.beta_g2.into_group();
    aggregate += pvugc_vk.b_g2_query[0].into_group();

    for (idx, coeff) in public_inputs_outer.iter().enumerate() {
        let base = pvugc_vk
            .b_g2_query
            .get(1 + idx)
            .expect("pvugc_vk missing public columns");
        aggregate += base.into_group() * coeff;
    }

    let witness_cols: Vec<_> = pvugc_vk
        .b_g2_query
        .iter()
        .skip(total_instance)
        .cloned()
        .collect();

    let mut y_cols = Vec::with_capacity(1 + witness_cols.len());
    y_cols.push(aggregate.into_affine());
    y_cols.extend(witness_cols);

    ColumnBases {
        y_cols,
        delta: pvugc_vk.delta_g2,
    }
}

/// Default-cycle convenience wrapper around [`build_column_bases_outer_for`].
pub fn build_column_bases_outer(
    pvugc_vk: &PvugcVk<OuterE>,
    vk_outer: &Groth16VK<OuterE>,
    public_inputs_outer: &[OuterFr],
) -> ColumnBases<OuterE> {
    build_column_bases_outer_for::<DefaultCycle>(pvugc_vk, vk_outer, public_inputs_outer)
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

    // Compute L_raw(x) = γ_abc_g1_raw[0] + Σ x_i * γ_abc_g1_raw[i+1]
    let mut l = vk_outer.gamma_abc_g1_raw[0].into_group();
    for (i, xi) in x_outer.iter().enumerate() {
        l += vk_outer.gamma_abc_g1_raw[i + 1] * xi;
    }

    // R = e(alpha,beta) * e(L_raw, gamma)
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
