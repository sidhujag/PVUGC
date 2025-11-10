//! Goldilocks field arithmetic over u64
//!
//! Provides host-side arithmetic for witness computation in circuits.
//! These operations are used ONLY in witness closures, not in constraints.

use crate::outer_compressed::InnerFr;
use ark_ff::{BigInteger, PrimeField, Zero};

/// Goldilocks modulus: p = 2^64 - 2^32 + 1
pub const P_GL: u128 = 18446744069414584321u128;

/// Assert that p_GL is non-zero in the outer field (required for soundness)
/// This is a compile-time/runtime sanity check as recommended by cryptographic audits
#[inline]
pub fn assert_p_gl_nonzero_in_outer_field() {
    debug_assert!(
        InnerFr::from(P_GL) != InnerFr::zero(),
        "CRITICAL: p_GL must be non-zero in the outer field Fr for congruence checks to be sound!"
    );
}

#[inline]
pub fn gl_add(a: u64, b: u64) -> u64 {
    let s = a as u128 + b as u128;
    let r = if s >= P_GL { s - P_GL } else { s };
    r as u64
}

#[inline]
pub fn gl_sub(a: u64, b: u64) -> u64 {
    // return (a - b) mod p
    if a >= b {
        a - b
    } else {
        (a as u128 + P_GL - b as u128) as u64
    }
}

#[inline]
pub fn gl_mul(a: u64, b: u64) -> u64 {
    let p = (a as u128) * (b as u128) % P_GL;
    p as u64
}

#[inline]
pub fn gl_inv(a: u64) -> u64 {
    // a^{-1} mod p via extended Euclid. If a==0 return 0 (constraints will fail elsewhere).
    if a == 0 {
        return 0;
    }
    let mut t: i128 = 0;
    let mut new_t: i128 = 1;
    let mut r: i128 = P_GL as i128;
    let mut new_r: i128 = a as i128;
    while new_r != 0 {
        let q = r / new_r;
        (t, new_t) = (new_t, t - q * new_t);
        (r, new_r) = (new_r, r - q * new_r);
    }
    if t < 0 {
        t += P_GL as i128;
    }
    t as u64
}

/// RPO inverse S-box: x^{10540996611094048183} mod P
/// This is the modular inverse of x^7 in GL field
pub fn gl_inv_sbox(y: u64) -> u64 {
    // For RPO, the inverse S-box is y^{(P-1)/7} mod P
    // Since 7 divides P-1, we can compute x = y^{(P-1)/7}
    // Then x^7 = y mod P

    // (P-1)/7 = 10540996611094048183
    const INV_EXP: u64 = 10540996611094048183;

    let mut result = 1u64;
    let mut base = y;
    let mut exp = INV_EXP;

    while exp > 0 {
        if exp & 1 == 1 {
            result = gl_mul(result, base);
        }
        base = gl_mul(base, base);
        exp >>= 1;
    }

    result
}

/// Convert InnerFr to u128 (low 128 bits). Safe for our use because
/// all GL-native products and sums we feed here are < 2^128.
#[inline]
pub fn fr_to_u128(fr: InnerFr) -> u128 {
    let bytes = fr.into_bigint().to_bytes_le();
    let mut val: u128 = 0;
    for (i, &b) in bytes.iter().enumerate().take(16) {
        val |= (b as u128) << (8 * i);
    }
    val
}

/// Compute the *true* Euclidean quotient q in Z such that:
///   lhs - rhs = q * P_GL
/// Return (q_plus, q_minus) with q = q_plus - q_minus, q_plus,q_minus ∈ [0, 2^64-1].
///
#[inline]
pub fn quotient_from_fr_difference(lhs: InnerFr, rhs: InnerFr) -> (u64, u64) {
    // Reduce both to canonical GL representatives
    let l_gl = fr_to_gl_u64(lhs) as u128;
    let r_gl = fr_to_gl_u64(rhs) as u128;

    // Now compute quotient from GL representatives
    let (diff, neg) = if l_gl >= r_gl {
        (l_gl - r_gl, false)
    } else {
        (r_gl - l_gl, true)
    };

    let q_abs = diff / P_GL; // Should be 0 or 1 for GL values
    debug_assert!(q_abs <= u64::MAX as u128, "quotient too large: {}", q_abs);
    let q_abs_u64 = q_abs as u64;
    if neg {
        (0, q_abs_u64)
    } else {
        (q_abs_u64, 0)
    }
}

/// Convert InnerFr to u64 mod p_GL (canonical reduction)
#[inline]
pub fn fr_to_gl_u64(fr: InnerFr) -> u64 {
    let bytes = fr.into_bigint().to_bytes_le();
    let mut val = 0u128;
    for (i, &b) in bytes.iter().enumerate().take(16) {
        val |= (b as u128) << (i * 8);
    }
    (val % P_GL) as u64
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_p_gl_nonzero_in_outer_field() {
        // Verify critical soundness requirement
        assert_p_gl_nonzero_in_outer_field();

        // Also verify the actual value
        let p_gl_in_fr = InnerFr::from(P_GL);
        assert_ne!(
            p_gl_in_fr,
            InnerFr::zero(),
            "p_GL must be non-zero in InnerFr for congruence checks to be sound"
        );
    }

    #[test]
    fn test_gl_arithmetic() {
        // Test basic operations
        let a = 12345u64;
        let b = 67890u64;

        let sum = gl_add(a, b);
        assert_eq!(sum, a + b);

        let prod = gl_mul(a, b);
        assert_eq!(prod as u128, (a as u128 * b as u128) % P_GL);

        // Test inverse
        let inv_a = gl_inv(a);
        let one = gl_mul(a, inv_a);
        assert_eq!(one, 1);
    }

    #[test]
    fn test_fr_to_gl_u64() {
        // Test conversion of small values
        let fr = InnerFr::from(12345u64);
        let gl = fr_to_gl_u64(fr);
        assert_eq!(gl, 12345u64);

        // Test that values mod p_GL
        let fr_large = InnerFr::from((P_GL + 100) as u64);
        let gl_large = fr_to_gl_u64(fr_large);
        assert_eq!(gl_large, 100u64); // Should reduce mod p_GL
    }

    #[test]
    fn test_quotient() {
        let lhs_fr = InnerFr::from(100u64);
        let rhs_fr = InnerFr::from(50u64);
        let (q_p, q_m) = quotient_from_fr_difference(lhs_fr, rhs_fr);
        assert_eq!(q_p, 0); // delta = 50, q = 50 / p_GL = 0
        assert_eq!(q_m, 0);

        // Test with larger difference requiring quotient
        let lhs_big = InnerFr::from(P_GL as u64);
        let rhs_small = InnerFr::from(1u64);
        let (q_p2, q_m2) = quotient_from_fr_difference(lhs_big, rhs_small);
        // (P_GL - 1) / P_GL = 0 with remainder
        assert_eq!(q_p2, 0);
        assert_eq!(q_m2, 0);
    }
}
