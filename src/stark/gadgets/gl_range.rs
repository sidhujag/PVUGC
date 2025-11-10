//! GL Value Range Checks and Input Validation
//!
//! ## Purpose
//!
//! Provides canonical Goldilocks allocation with range enforcement:
//! - `gl_alloc_u64()`: Allocates u64 with 0 <= x < p_GL check
//! - `gl_alloc_u64_vec()`: Batch allocation for witness inputs
//!
//! ## Usage Pattern
//!
//! Use at input boundaries to validate witness data:
//! ```text
//! // Allocate witness data with range check
//! let inputs = gl_alloc_u64_vec(cs, &witness_values)?;
//! ```
//!
//! Then use light operations (from gl_fast) for internal computation.
//!
//! Also used by `canonicalize_to_bytes()` to enforce canonical representation
//! when comparing computed digests to proof bytes.

use crate::outer_compressed::InnerFr;
use ark_r1cs_std::boolean::Boolean;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_r1cs_std::uint64::UInt64;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

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
    let u = UInt64::new_witness(cs.clone(), || {
        value.ok_or(SynthesisError::AssignmentMissing)
    })?;
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
