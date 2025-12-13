//! Fast Goldilocks Arithmetic - Light Operations
//!
//! Provides congruence-only Goldilocks operations without per-step canonicalization.
//!
//! ## Design Principle
//!
//! Operations enforce modular congruence rather than exact equality:
//! ```text
//! a·b = result + quotient·p_GL    (quotient unconstrained)
//! ```
//!
//! Soundness relies on:
//! - p_GL ≠ 0 in the outer field (verified by test)
//! - Congruence checks on all non-linear operations
//! - Canonicalization at serialization boundaries
//!
//! ## Constraint Complexity
//!
//! - `gl_mul_light()`: approximately 10-20 constraints
//! - `gl_add_light()`: approximately 10-20 constraints  
//! - `gl_inv_light()`: approximately 30-40 constraints
//!
//! Use for internal arithmetic. Canonicalize only when comparing to proof bytes.

use crate::stark::StarkInnerFr as InnerFr;
use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{fields::fp::FpVar, prelude::*, uint8::UInt8};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

const P_U64: u64 = 0xFFFF_FFFF_0000_0001;

#[derive(Clone)]
pub struct GlVar(pub FpVar<InnerFr>);

// Helper: p_GL as Fr constant
fn fp_p() -> FpVar<InnerFr> {
    FpVar::constant(InnerFr::from(P_U64 as u128))
}

/// Allocate u64 as 8 bytes
fn alloc_u64(
    cs: ConstraintSystemRef<InnerFr>,
    hint: Option<u64>,
) -> Result<(FpVar<InnerFr>, [UInt8<InnerFr>; 8]), SynthesisError> {
    let w = hint.unwrap_or(0);
    let bytes: [UInt8<InnerFr>; 8] = core::array::from_fn(|i| {
        UInt8::new_witness(cs.clone(), move || Ok(w.to_le_bytes()[i])).unwrap()
    });

    // Manual pack
    let mut v = FpVar::constant(InnerFr::from(0u64));
    let mut pow = FpVar::constant(InnerFr::from(1u64));
    for byte in &bytes {
        v = &v + &(&byte.to_fp()? * &pow);
        pow = &pow * &FpVar::constant(InnerFr::from(256u64));
    }
    Ok((v, bytes))
}

/// Pack a UInt64 gadget into an `FpVar` by bit decomposition.
fn u64_var_to_fp(cs: ConstraintSystemRef<InnerFr>, u: &UInt64<InnerFr>) -> Result<FpVar<InnerFr>, SynthesisError> {
    let bits = u.to_bits_le()?;
    let one = FpVar::constant(InnerFr::from(1u64));
    let zero = FpVar::constant(InnerFr::from(0u64));
    if bits.is_empty() {
        return Ok(FpVar::constant(InnerFr::from(0u64)));
    }
    let mut acc = FpVar::conditionally_select(&bits[0], &one, &zero)?;
    for (i, b) in bits.iter().enumerate().skip(1) {
        let bit_fp = FpVar::conditionally_select(b, &one, &zero)?;
        acc += bit_fp * FpVar::constant(InnerFr::from(1u64 << i));
    }
    Ok(acc)
}

/// GL add: a + b = r + s*p, s ∈ {0,1}
pub fn gl_add(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    b: &GlVar,
) -> Result<GlVar, SynthesisError> {
    let sum = &a.0 + &b.0;
    let s = Boolean::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::fr_to_gl_u64;
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok((av as u128 + bv as u128) >= P_U64 as u128)
    })?;
    let p = FpVar::constant(InnerFr::from(P_U64 as u128));
    let s_fp = FpVar::conditionally_select(&s, &p, &FpVar::zero())?;
    Ok(GlVar(sum - s_fp))
}

/// GL sub: a - b = r - t*p, t ∈ {0,1}
pub fn gl_sub(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    b: &GlVar,
) -> Result<GlVar, SynthesisError> {
    let diff = &a.0 - &b.0;
    let t = Boolean::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::fr_to_gl_u64;
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(av < bv)
    })?;
    let p = FpVar::constant(InnerFr::from(P_U64 as u128));
    let t_fp = FpVar::conditionally_select(&t, &p, &FpVar::zero())?;
    Ok(GlVar(diff + t_fp))
}

/// GL mul - witness correct result and verify congruence
pub fn gl_mul(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    b: &GlVar,
) -> Result<GlVar, SynthesisError> {
    use crate::stark::gl_u64::{fr_to_gl_u64, gl_mul as gl_mul_u64};
    use super::gl_range::enforce_lt_p_gl;

    // Witness canonical result in u64, computed inside the witness closure so CRS setup works.
    let result_u = UInt64::new_witness(cs.clone(), || {
        // During Groth16 CRS setup, witness values are not available; treat missing as 0.
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(gl_mul_u64(av, bv))
    })?;
    enforce_lt_p_gl(&result_u)?;
    let result_fp = u64_var_to_fp(cs.clone(), &result_u)?;
    let result = GlVar(result_fp.clone());

    // Witness k such that: a*b = result + k*p (in the outer field).
    let k_u = UInt64::new_witness(cs.clone(), || {
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let prod_u128 = (av as u128) * (bv as u128);
        let res_u128 = gl_mul_u64(av, bv) as u128;
        Ok(((prod_u128 - res_u128) / (P_U64 as u128)) as u64)
    })?;
    let k_fp = u64_var_to_fp(cs.clone(), &k_u)?;

    // Verify: a * b == result + k * p
    let p = FpVar::constant(InnerFr::from(P_U64 as u128));
    let prod_fr = &a.0 * &b.0;
    let right = &result_fp + &(&k_fp * &p);
    prod_fr.enforce_equal(&right)?;

    Ok(result)
}

/// GL inversion
pub fn gl_inv(cs: ConstraintSystemRef<InnerFr>, v: &GlVar) -> Result<GlVar, SynthesisError> {
    use crate::stark::gl_u64::{fr_to_gl_u64, gl_inv};
    use super::gl_range::enforce_lt_p_gl;

    let inv_u = UInt64::new_witness(cs.clone(), || {
        let v_fr = v.0.value().unwrap_or_else(|_| InnerFr::from(0u64));
        Ok(gl_inv(fr_to_gl_u64(v_fr)))
    })?;
    enforce_lt_p_gl(&inv_u)?;
    let inv_fp = u64_var_to_fp(cs.clone(), &inv_u)?;
    let inv = GlVar(inv_fp);

    // Enforce: v * inv = 1 (gl_mul returns canonical GL, so plain equality works)
    let prod = gl_mul(cs.clone(), v, &inv)?;
    let one = FpVar::constant(InnerFr::from(1u64));
    prod.0.enforce_equal(&one)?;

    Ok(inv)
}

// ============================================================================
// Light GL operations - congruence-only, no byte packing/range checks
// These are much cheaper but don't guarantee canonical representation
// ============================================================================

/// Light GL add: a + b = r + s·p where s ∈ {0,1}
/// ~10-20 constraints (1 boolean + equality)
pub fn gl_add_light(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    b: &GlVar,
) -> Result<GlVar, SynthesisError> {
    // Witness the result (may not be canonical)
    let r = FpVar::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::{fr_to_gl_u64, gl_add};
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(InnerFr::from(gl_add(av, bv) as u128))
    })?;

    // Witness quotient s ∈ {0,1}
    let s = Boolean::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::fr_to_gl_u64;
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok((av as u128 + bv as u128) >= P_U64 as u128)
    })?;

    // Enforce: a + b = r + s·p
    let s_fp: FpVar<InnerFr> = s.into();
    (a.0.clone() + b.0.clone()).enforce_equal(&(r.clone() + s_fp * fp_p()))?;
    Ok(GlVar(r))
}

/// Light GL add with a public constant (keeps quotient bounded to {0,1}).
pub fn gl_add_const_light(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    c: u64,
) -> Result<GlVar, SynthesisError> {
    let c_var = GlVar(FpVar::constant(InnerFr::from(c as u128)));
    gl_add_light(cs, a, &c_var)
}

/// Light GL sub: a - b = r - t·p where t ∈ {0,1}
/// ~10-20 constraints (1 boolean + equality)
pub fn gl_sub_light(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    b: &GlVar,
) -> Result<GlVar, SynthesisError> {
    // Witness the result
    let r = FpVar::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::{fr_to_gl_u64, gl_sub};
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(InnerFr::from(gl_sub(av, bv) as u128))
    })?;

    // Witness quotient t ∈ {0,1}
    let t = Boolean::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::fr_to_gl_u64;
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(av < bv)
    })?;

    // Enforce: a - b = r - t·p
    let t_fp: FpVar<InnerFr> = t.into();
    (a.0.clone() - b.0.clone()).enforce_equal(&(r.clone() - t_fp * fp_p()))?;
    Ok(GlVar(r))
}

/// Light GL mul: a·b = r + k·p
/// ~5-8 constraints (1 mul + 2 witness + equality)
pub fn gl_mul_light(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    b: &GlVar,
) -> Result<GlVar, SynthesisError> {
    // Witness the GL-reduced result
    let r = FpVar::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::{fr_to_gl_u64, gl_mul};
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(InnerFr::from(gl_mul(av, bv) as u128))
    })?;

    // Witness quotient k
    let k = FpVar::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::fr_to_gl_u64;
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let bv = fr_to_gl_u64(b.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let prod = (av as u128) * (bv as u128);
        let res = crate::stark::gl_u64::gl_mul(av, bv) as u128;
        Ok(InnerFr::from((prod - res) / P_U64 as u128))
    })?;

    // Enforce: a·b = r + k·p
    (a.0.clone() * b.0.clone()).enforce_equal(&(r.clone() + k * fp_p()))?;
    Ok(GlVar(r))
}

/// Light GL mul by a public constant: a·c = r + k·p
/// Avoids a variable multiplication gate by folding the constant into the linear combination.
pub fn gl_mul_const_light(
    cs: ConstraintSystemRef<InnerFr>,
    a: &GlVar,
    c: u64,
) -> Result<GlVar, SynthesisError> {
    // Witness the GL-reduced result
    let r = FpVar::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::{fr_to_gl_u64, gl_mul};
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        Ok(InnerFr::from(gl_mul(av, c) as u128))
    })?;

    // Witness quotient k for congruence check
    let k = FpVar::new_witness(cs.clone(), || {
        use crate::stark::gl_u64::fr_to_gl_u64;
        let av = fr_to_gl_u64(a.0.value().unwrap_or_else(|_| InnerFr::from(0u64)));
        let prod = (av as u128) * (c as u128);
        let res = crate::stark::gl_u64::gl_mul(av, c) as u128;
        Ok(InnerFr::from((prod - res) / P_U64 as u128))
    })?;

    // Enforce: a·c = r + k·p using a constant-scaled product (no mul gate)
    let prod = &a.0 * InnerFr::from(c as u128);
    prod.enforce_equal(&(r.clone() + k * fp_p()))?;
    Ok(GlVar(r))
}

/// Light GL inverse - witness and verify with single mul
pub fn gl_inv_light(cs: ConstraintSystemRef<InnerFr>, v: &GlVar) -> Result<GlVar, SynthesisError> {
    use crate::stark::gl_u64::{fr_to_gl_u64, gl_inv};

    // Witness the inverse (compute inside witness closure so CRS setup works).
    let inv = GlVar(FpVar::new_witness(cs.clone(), || {
        // During setup, treat missing values as 0.
        let v_fr = v.0.value().unwrap_or_else(|_| InnerFr::from(0u64));
        let inv_val = gl_inv(fr_to_gl_u64(v_fr));
        Ok(InnerFr::from(inv_val as u128))
    })?);

    // Verify: v * inv = 1 using light mul
    let prod = gl_mul_light(cs.clone(), v, &inv)?;
    let one = FpVar::constant(InnerFr::from(1u64));
    prod.0.enforce_equal(&one)?;

    Ok(inv)
}

/// Light batch inversion for GL elements: returns inverses of all inputs
pub fn gl_batch_inv_light(
    cs: ConstraintSystemRef<InnerFr>,
    values: &[GlVar],
) -> Result<Vec<GlVar>, SynthesisError> {
    if values.is_empty() {
        return Ok(Vec::new());
    }
    // Prefix products
    let mut prefix: Vec<GlVar> = Vec::with_capacity(values.len());
    let mut acc = GlVar(FpVar::constant(InnerFr::from(1u64)));
    for v in values {
        acc = gl_mul_light(cs.clone(), &acc, v)?;
        prefix.push(acc.clone());
    }
    // Invert total product once
    let mut inv_total = gl_inv_light(cs.clone(), prefix.last().unwrap())?;
    // Backwards pass
    let mut invs: Vec<GlVar> = vec![GlVar(FpVar::constant(InnerFr::from(0u64))); values.len()];
    for i in (0..values.len()).rev() {
        let prev = if i == 0 {
            GlVar(FpVar::constant(InnerFr::from(1u64)))
        } else {
            prefix[i - 1].clone()
        };
        // invs[i] = inv_total * prev
        invs[i] = gl_mul_light(cs.clone(), &inv_total, &prev)?;
        // inv_total = inv_total * values[i]
        inv_total = gl_mul_light(cs.clone(), &inv_total, &values[i])?;
    }
    Ok(invs)
}
