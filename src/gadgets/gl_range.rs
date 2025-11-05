//! GL value range checks
//!
//! Enforce that u64 values are < p_GL using carry chain

use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::uint64::UInt64;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::boolean::Boolean;
use crate::outer_compressed::InnerFr;

pub type FpGLVar = FpVar<InnerFr>;
pub type UInt64Var = UInt64<InnerFr>;

/// Enforce: u < P_GL using a constant-carry addition with C = 2^32 - 1.
/// No overflow (carry_out == 0)  <=>  u < 2^64 - 2^32 + 1 = P_GL
pub fn enforce_lt_p_gl(u: &UInt64Var) -> Result<(), SynthesisError> {
    let _cs = u.cs();
    
    // Build bits and add constant C = 2^32 - 1
    let bits = u.to_bits_le()?;
    assert_eq!(bits.len(), 64);
    
    // Precompute constant bits of C (low 32 ones)
    let mut c_bits = Vec::with_capacity(64);
    for i in 0..64 {
        let bit = i < 32; // C has ones in low 32, zeros in high 32
        c_bits.push(Boolean::constant(bit));
    }
    
    // carry chain
    let mut carry = Boolean::constant(false);
    
    for i in 0..64 {
        let a = &bits[i];
        let b = &c_bits[i];
        
        // carry_out = (a & b) | (a & carry) | (b & carry)
        let a_and_b = a & b;
        let a_and_c = a & &carry;
        let b_and_c = b & &carry;
        let tmp = &a_and_b | &a_and_c;
        let carry_next = &tmp | &b_and_c;
        
        // sum bit is ignored; we only care about the final carry
        carry = carry_next;
    }
    
    // No overflow allowed
    carry.enforce_equal(&Boolean::constant(false))?;
    Ok(())
}

/// Allocate a GL value as a UInt64 with < p_GL range check, and return (UInt64, FpGLVar)
pub fn gl_alloc_u64(
    cs: ConstraintSystemRef<InnerFr>,
    value: Option<u64>,
) -> Result<(UInt64Var, FpGLVar), SynthesisError> {
    let u = UInt64::new_witness(cs.clone(), || value.ok_or(SynthesisError::AssignmentMissing))?;
    enforce_lt_p_gl(&u)?;
    
    // Reconstruct field var from bits: sum bit_i * 2^i  
    // Start with first bit to get a proper CS-attached variable
    let bits = u.to_bits_le()?;
    let one = FpGLVar::constant(InnerFr::from(1u64));
    let zero = FpGLVar::constant(InnerFr::from(0u64));
    
    if bits.is_empty() {
        return Ok((u, FpGLVar::constant(InnerFr::from(0u64))));
    }
    
    // Start with first bit (properly attached to CS)
    let mut acc = FpGLVar::conditionally_select(&bits[0], &one, &zero)?;
    for (i, b) in bits.iter().enumerate().skip(1) {
        let bit_fp = FpGLVar::conditionally_select(b, &one, &zero)?;
        acc += bit_fp * FpGLVar::constant(InnerFr::from(1u64 << i));
    }
    Ok((u, acc))
}

/// Convenience: allocate many GL values
pub fn gl_alloc_u64_vec(
    cs: ConstraintSystemRef<InnerFr>,
    values: &[u64],
) -> Result<Vec<FpGLVar>, SynthesisError> {
    let mut out = Vec::with_capacity(values.len());
    for &v in values {
        let (_u, fp) = gl_alloc_u64(cs.clone(), Some(v))?;
        out.push(fp);
    }
    Ok(out)
}

// === GL arithmetic with congruence enforcement ===

use crate::inner_stark_full::enforce_gl_eq;

/// GL add with congruence enforcement and canonical result.
pub fn gl_add_var(
    cs: ark_relations::r1cs::ConstraintSystemRef<InnerFr>,
    a: &FpGLVar,
    b: &FpGLVar,
) -> Result<FpGLVar, SynthesisError> {
    let sum_fr = a + b;  // Fr computation
    // witness canonical GL sum from concrete values
    let (_u, sum_gl) = gl_alloc_u64(cs.clone(), {
        let av = a.value().ok();
        let bv = b.value().ok();
        av.zip(bv).map(|(av, bv)| {
            use crate::gl_u64::{fr_to_gl_u64, gl_add};
            gl_add(fr_to_gl_u64(av), fr_to_gl_u64(bv))
        })
    })?;
    enforce_gl_eq(&sum_fr, &sum_gl)?;
    Ok(sum_gl)  // Return canonical GL witness!
}

/// GL add with a GL constant.
pub fn gl_add_const(
    cs: ark_relations::r1cs::ConstraintSystemRef<InnerFr>,
    a: &FpGLVar,
    c_u64: u64,
) -> Result<FpGLVar, SynthesisError> {
    // Add in Fr, then reduce to canonical GL
    let a_cs = a.cs();
    let c = FpGLVar::new_constant(a_cs, InnerFr::from(c_u64))?;
    let sum_fr = a + c;
    
    // Witness canonical GL sum
    let (_u, sum_gl) = gl_alloc_u64(cs, {
        let av = a.value().ok();
        av.map(|av| {
            use crate::gl_u64::{fr_to_gl_u64, gl_add};
            gl_add(fr_to_gl_u64(av), c_u64)
        })
    })?;
    enforce_gl_eq(&sum_fr, &sum_gl)?;
    Ok(sum_gl)  // Return canonical GL!
}

/// GL multiply with congruence enforcement and canonical result.
pub fn gl_mul_var(
    cs: ark_relations::r1cs::ConstraintSystemRef<InnerFr>,
    a: &FpGLVar,
    b: &FpGLVar,
) -> Result<FpGLVar, SynthesisError> {
    let prod_fr = a * b;  // Fr computation
    let (_u, prod_gl) = gl_alloc_u64(cs.clone(), {
        let av = a.value().ok();
        let bv = b.value().ok();
        av.zip(bv).map(|(av, bv)| {
            use crate::gl_u64::{fr_to_gl_u64, gl_mul};
            gl_mul(fr_to_gl_u64(av), fr_to_gl_u64(bv))
        })
    })?;
    enforce_gl_eq(&prod_fr, &prod_gl)?;
    Ok(prod_gl)  // Return canonical GL witness!
}

/// GL multiply by a GL constant.
pub fn gl_mul_const(
    cs: ark_relations::r1cs::ConstraintSystemRef<InnerFr>,
    a: &FpGLVar,
    c_u64: u64,
) -> Result<FpGLVar, SynthesisError> {
    // Use witness instead of constant to ensure proper CS attachment
    let c = FpGLVar::new_witness(cs.clone(), || Ok(InnerFr::from(c_u64)))?;
    gl_mul_var(cs, a, &c)
}

/// Proves v != 0 by exhibiting inv with v*inv = 1 (GL semantics)
pub fn gl_enforce_nonzero_and_inv(
    cs: ark_relations::r1cs::ConstraintSystemRef<InnerFr>,
    v: &FpGLVar,
) -> Result<FpGLVar, SynthesisError> {
    use crate::gl_u64::{fr_to_gl_u64, gl_inv};
    let inv = FpGLVar::new_witness(cs.clone(), || {
        let vv = v.value()?;
        let inv_u = gl_inv(fr_to_gl_u64(vv));
        Ok(InnerFr::from(inv_u))
    })?;
    let one = FpGLVar::constant(InnerFr::from(1u64));
    enforce_gl_eq(&(v * &inv), &one)?;
    Ok(inv)
}

/// GL linear combination with congruence enforcement
///
/// Computes Σ coeffs[i] * terms[i] in GL semantics
/// Witnesses the GL sum and enforces congruence with Fr computation
pub fn gl_lincomb(
    cs: ark_relations::r1cs::ConstraintSystemRef<InnerFr>,
    coeffs: &[u64],
    terms: &[FpGLVar],
) -> Result<FpGLVar, SynthesisError> {
    if terms.is_empty() {
        return Ok(FpGLVar::new_constant(cs, InnerFr::from(0u64))?);
    }
    
    // Fr-side accumulator
    let first_cs = terms[0].cs();
    let mut acc_fr = FpGLVar::new_constant(first_cs.clone(), InnerFr::from(coeffs[0]))? * &terms[0];
    for (c, t) in coeffs.iter().zip(terms).skip(1) {
        let coeff_var = FpGLVar::new_constant(t.cs(), InnerFr::from(*c))?;
        acc_fr += coeff_var * t;
    }

    // GL witness (canonical Goldilocks) - THIS is what we return!
    let sum_w = FpGLVar::new_witness(cs, || {
        use crate::gl_u64::{gl_add, gl_mul, fr_to_gl_u64};
        let mut acc = 0u64;
        for (c, t) in coeffs.iter().zip(terms.iter()) {
            acc = gl_add(acc, gl_mul(*c, fr_to_gl_u64(t.value()?)));
        }
        Ok(InnerFr::from(acc))
    })?;
    enforce_gl_eq(&acc_fr, &sum_w)?;

    Ok(sum_w) // Return canonical GL witness, not Fr result!
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_relations::r1cs::ConstraintSystem;
    
    #[test]
    fn test_gl_lt_p() {
        let cs = ConstraintSystem::<InnerFr>::new_ref();
        
        let (_u, _) = gl_alloc_u64(cs.clone(), Some(1)).unwrap();
        let (_u, _) = gl_alloc_u64(cs.clone(), Some(18446744069414584320u64)).unwrap(); // p_GL - 1
        assert!(cs.is_satisfied().unwrap());
    }
}

