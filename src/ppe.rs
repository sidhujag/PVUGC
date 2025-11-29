use crate::error::{Error, Result};
/// PVUGC Verifying Key wrapper exposed at deposit time
use ark_ec::pairing::Pairing;
use ark_ec::pairing::PairingOutput;
use ark_ec::AffineRepr;
use ark_ff::One; // For is_one()
use ark_ff::PrimeField;
use ark_groth16::VerifyingKey as Groth16VK;
use ark_std::Zero; // For is_zero()

#[derive(Clone, Debug)]
pub struct PvugcVk<E: Pairing> {
    pub beta_g2: E::G2Affine,
    pub delta_g2: E::G2Affine,
    /// Arc-wrapped to avoid expensive clones (BW6-761 has dozens of large G2 points)
    pub b_g2_query: std::sync::Arc<Vec<E::G2Affine>>,
    /// Per-column hints indicating whether the column is allowed to be armed.
    /// Hints must align 1:1 with `b_g2_query`.
    pub witness_zero_hints: std::sync::Arc<Vec<bool>>,
    /// Baked Quotient Points (Q_const)
    /// These allow the decapper to compute the constant quotient term H_const(x)
    /// and subtract it from the target, ensuring security against H-based attacks.
    /// q_const_points[0] is the constant term.
    /// q_const_points[1..] correspond to public inputs.
    pub q_const_points: std::sync::Arc<Vec<E::G1Affine>>,
}

impl<E: Pairing> PvugcVk<E> {
    /// Convenience constructor that marks every column as isolated.
    pub fn new_with_all_witnesses_isolated(
        beta_g2: E::G2Affine,
        delta_g2: E::G2Affine,
        b_g2_query: Vec<E::G2Affine>,
        q_const_points: Vec<E::G1Affine>,
    ) -> Self {
        let hints = vec![true; b_g2_query.len()];
        Self {
            beta_g2,
            delta_g2,
            b_g2_query: std::sync::Arc::new(b_g2_query),
            witness_zero_hints: std::sync::Arc::new(hints),
            q_const_points: std::sync::Arc::new(q_const_points),
        }
    }

    /// Ensure witness isolation hints cover all columns and mark the witness tail as safe.
    pub fn enforce_isolated_witness_block(
        &self,
        total_instance: usize,
    ) -> crate::error::Result<()> {
        if self.witness_zero_hints.len() != self.b_g2_query.len() {
            return Err(crate::error::Error::InvalidWitnessIsolationHints);
        }
        if self
            .witness_zero_hints
            .iter()
            .skip(total_instance)
            .any(|hint| !*hint)
        {
            return Err(crate::error::Error::UnsafeWitnessColumns);
        }
        Ok(())
    }
    /// Placeholder hook for the Gröbner-audit predicate. Once the symbolic
    /// remainder is known, evaluate it on `public_inputs` and error if it
    /// vanishes. Currently a no-op so the arming flow already enforces the
    /// guard location.
    pub fn enforce_public_residual_safe(
        &self,
        _public_inputs: &[E::ScalarField],
    ) -> crate::error::Result<()> {
        Ok(())
    }
}

/// Validate subgroup membership for PVUGC-VK G₂ elements
pub fn validate_pvugc_vk_subgroups<E: Pairing>(pvugc_vk: &PvugcVk<E>) -> bool {
    // All G₂ elements must lie in the prime-order subgroup
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;
    let is_good = |g: &E::G2Affine| {
        if g.is_zero() {
            return true;
        }

        g.mul_bigint(order).is_zero()
    };

    if pvugc_vk.b_g2_query.is_empty() {
        return false;
    }

    if pvugc_vk.beta_g2.is_zero() || !is_good(&pvugc_vk.beta_g2) {
        return false;
    }

    if pvugc_vk.delta_g2.is_zero() || !is_good(&pvugc_vk.delta_g2) {
        return false;
    }

    if pvugc_vk.b_g2_query.iter().any(|g| !is_good(g)) {
        return false;
    }

    // Validate q_const_points
    let is_good_g1 = |g: &E::G1Affine| {
        if g.is_zero() {
            return true;
        }
        g.mul_bigint(order).is_zero()
    };
    if pvugc_vk.q_const_points.iter().any(|g| !is_good_g1(g)) {
        return false;
    }

    true
}

/// Validate subgroup membership for Groth16 VK elements
/// - G1: alpha_g1 and all gamma_abc_g1 entries must be in the prime-order subgroup
/// - G2: beta_g2, gamma_g2, delta_g2 must be in the prime-order subgroup
pub fn validate_groth16_vk_subgroups<E: Pairing>(vk: &Groth16VK<E>) -> bool {
    let order = <<E as Pairing>::ScalarField as PrimeField>::MODULUS;

    let is_good_g1 = |g: &E::G1Affine| {
        if g.is_zero() {
            return true;
        }
        g.mul_bigint(order).is_zero()
    };

    let is_good_g2 = |g: &E::G2Affine| {
        if g.is_zero() {
            return true;
        }
        g.mul_bigint(order).is_zero()
    };

    if !is_good_g1(&vk.alpha_g1) {
        return false;
    }
    if !is_good_g2(&vk.beta_g2) {
        return false;
    }
    if !is_good_g2(&vk.gamma_g2) {
        return false;
    }
    if !is_good_g2(&vk.delta_g2) {
        return false;
    }
    if vk.gamma_abc_g1.iter().any(|g| !is_good_g1(g)) {
        return false;
    }

    true
}

pub fn extract_y_bases<E: Pairing>(pvugc_vk: &PvugcVk<E>) -> Vec<E::G2Affine> {
    // Basis choice Y^{(B)} = {β₂} ∪ b_g2_query; δ₂ kept separate on C-side
    let mut y = Vec::with_capacity(1 + pvugc_vk.b_g2_query.len());
    y.push(pvugc_vk.beta_g2);
    y.extend_from_slice(&**pvugc_vk.b_g2_query);
    y
}

/// Compute Groth16 target R_raw(vk, x)
pub fn compute_groth16_target<E: Pairing>(
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> Result<PairingOutput<E>> {
    let ic_bases = &vk.gamma_abc_g1;

    let expected_inputs = ic_bases.len().saturating_sub(1);
    if public_inputs.len() != expected_inputs {
        return Err(Error::PublicInputLength {
            expected: expected_inputs,
            actual: public_inputs.len(),
        });
    }

    // Compute L(x) over whichever IC vector is available
    let mut l = ic_bases[0].into_group();

    for (gamma, x_i) in ic_bases.iter().skip(1).zip(public_inputs.iter()) {
        // Use into_group() explicitly to satisfy type checker
        let g: <E as Pairing>::G1 = gamma.into_group();
        l += g * x_i;
    }

    // SECURITY: IC(x) ≠ 0 (specs/PVUGC.md)
    if l.is_zero() {
        return Err(Error::ZeroInstanceCommitment);
    }

    // R = e(alpha, beta) + e(L, gamma)
    let r = E::pairing(vk.alpha_g1, vk.beta_g2) + E::pairing(l, vk.gamma_g2);

    // SECURITY: R(vk,x) ≠ 1 (specs/PVUGC.md)
    if r.0.is_one() || r.0.is_zero() {
        return Err(Error::DegenerateTarget);
    }

    Ok(r)
}

/// Compute baked target R_baked(vk, x) = R_raw - T_const
/// where T_const = e(Q(x), delta)
pub fn compute_baked_target<E: Pairing>(
    vk: &Groth16VK<E>,
    pvugc_vk: &PvugcVk<E>,
    public_inputs: &[E::ScalarField],
) -> Result<PairingOutput<E>> {
    use ark_ec::CurveGroup;

    // 1. Compute raw target
    let r_raw = compute_groth16_target(vk, public_inputs)?;

    // 2. Compute baked quotient term Q(x)
    if pvugc_vk.q_const_points.len() != public_inputs.len() + 1 {
        return Err(Error::MismatchedSizes); // Should define a better error
    }

    let mut q_sum = pvugc_vk.q_const_points[0].into_group();
    for (i, x_i) in public_inputs.iter().enumerate() {
        q_sum += pvugc_vk.q_const_points[i + 1] * x_i;
    }

    // 3. Add T_const = e(Q(x), delta)
    // Standard: AB - (C_wit + Q)delta = R_raw
    // AB - C_wit delta = R_raw + Q delta
    // So R_baked = R_raw + T_const
    let t_const = E::pairing(q_sum.into_affine(), pvugc_vk.delta_g2);

    Ok(r_raw + t_const)
}

/// e(A,B) · e(C,δ) = e(α,β) · e(L(x),γ)
pub fn build_one_sided_ppe<E: Pairing>(
    pvugc_vk: &PvugcVk<E>,
    vk: &Groth16VK<E>,
    public_inputs: &[E::ScalarField],
) -> Result<(Vec<E::G2Affine>, E::G2Affine, PairingOutput<E>)> {
    // Y_j bases for B-side from PVUGC-VK wrapper
    let y_bases = extract_y_bases(pvugc_vk);

    // +δ for C-side
    let delta = pvugc_vk.delta_g2;

    // Target R_baked(vk, x)
    let target = compute_baked_target(vk, pvugc_vk, public_inputs)?;

    Ok((y_bases, delta, target))
}
