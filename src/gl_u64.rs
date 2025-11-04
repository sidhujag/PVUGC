//! Goldilocks field arithmetic over u64
//!
//! Provides host-side arithmetic for witness computation in circuits.
//! These operations are used ONLY in witness closures, not in constraints.

use ark_ff::{PrimeField, BigInteger};
use crate::outer_compressed::InnerFr;

/// Goldilocks modulus: p = 2^64 - 2^32 + 1
pub const P_GL: u128 = 18446744069414584321u128;

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
    // a^{-1} mod p via extended Euclid (a!=0 in our usage)
    let mut t: i128 = 0;
    let mut new_t: i128 = 1;
    let mut r: i128 = P_GL as i128;
    let mut new_r: i128 = a as i128;
    while new_r != 0 {
        let q = r / new_r;
        (t, new_t) = (new_t, t - q * new_t);
        (r, new_r) = (new_r, r - q * new_r);
    }
    if t < 0 { t += P_GL as i128; }
    t as u64
}

/// Compute the signed quotient q in Z such that lhs - rhs = q * p_GL.
/// Returns (q_plus, q_minus) with q = q_plus - q_minus, each u64.
#[inline]
pub fn gl_congruence_quotient(lhs_u128: u128, rhs_u128: u128) -> (u64, u64) {
    let delta = lhs_u128 as i128 - rhs_u128 as i128;
    if delta >= 0 {
        (((delta as u128) / P_GL) as u64, 0u64)
    } else {
        (0u64, (((-delta) as u128) / P_GL) as u64)
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
    fn test_quotient() {
        let lhs = 100u128;
        let rhs = 50u128;
        let (q_p, q_m) = gl_congruence_quotient(lhs, rhs);
        assert_eq!(q_p, 0);  // delta = 50, q = 50 / p_GL = 0
        assert_eq!(q_m, 0);
    }
}

