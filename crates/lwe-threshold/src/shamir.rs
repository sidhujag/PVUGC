//! Minimal Shamir secret sharing over GF(256) for 32-byte secrets.
//!
//! This is a small, dependency-free implementation intended for the lockset scaffold:
//! - split a 32-byte secret into N shares with threshold T
//! - reconstruct from any T valid shares
//!
//! Security note: this is information-theoretic given correct usage; it is *not* the cryptographic
//! hardness layer. The hardness is intended to come from the upstream DPP→LWE “decap” mechanism.

use rand_core::RngCore;
use thiserror::Error;

#[derive(Clone, Copy, Debug)]
pub struct ShamirConfig {
    pub threshold: usize,
    pub shares: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShamirShare {
    /// Share index in \([1..=N]\).
    pub index: u32,
    /// The 32-byte share payload (one byte per secret byte, independently shared).
    pub value: [u8; 32],
}

#[derive(Debug, Error)]
pub enum ShamirError {
    #[error("invalid parameters")]
    InvalidParams,
    #[error("insufficient shares")]
    InsufficientShares,
    #[error("duplicate share index")]
    DuplicateIndex,
    #[error("share index out of range")]
    IndexOutOfRange,
}

/// Split a 32-byte secret into `cfg.shares` shares with threshold `cfg.threshold`.
pub fn split_secret_32(
    rng: &mut dyn RngCore,
    cfg: &ShamirConfig,
    secret: [u8; 32],
) -> Result<Vec<ShamirShare>, ShamirError> {
    if cfg.threshold < 2 || cfg.shares < cfg.threshold || cfg.shares > u32::MAX as usize {
        return Err(ShamirError::InvalidParams);
    }

    // For each byte position, sample a random degree-(t-1) polynomial with constant term = secret[b].
    // Then evaluate it at x=1..=N in GF(256).
    let t = cfg.threshold;
    let n = cfg.shares;

    let mut coeffs: Vec<[u8; 32]> = Vec::with_capacity(t);
    coeffs.push(secret);
    for _ in 1..t {
        let mut c = [0u8; 32];
        rng.fill_bytes(&mut c);
        coeffs.push(c);
    }

    let mut out = Vec::with_capacity(n);
    for i in 1..=n {
        let x = i as u8; // n <= 2^32 but we require i<=255 for GF(256) x coords
        if x == 0 {
            return Err(ShamirError::InvalidParams);
        }
        if i > 255 {
            // This GF(256) implementation supports only 255 nonzero x-coordinates.
            return Err(ShamirError::InvalidParams);
        }

        let mut y = [0u8; 32];
        for b in 0..32 {
            // Horner: ((((a_{t-1} x + a_{t-2}) x + ...) x + a_0)
            let mut acc = coeffs[t - 1][b];
            for k in (0..(t - 1)).rev() {
                acc = gf256_add(gf256_mul(acc, x), coeffs[k][b]);
            }
            y[b] = acc;
        }
        out.push(ShamirShare {
            index: i as u32,
            value: y,
        });
    }
    Ok(out)
}

/// Reconstruct a 32-byte secret from any `cfg.threshold` shares using Lagrange interpolation at x=0.
pub fn reconstruct_secret_32(
    cfg: &ShamirConfig,
    shares: &[ShamirShare],
) -> Result<[u8; 32], ShamirError> {
    if cfg.threshold < 2 || cfg.shares < cfg.threshold {
        return Err(ShamirError::InvalidParams);
    }
    if shares.len() < cfg.threshold {
        return Err(ShamirError::InsufficientShares);
    }

    // Take first t shares (caller typically filters/validates).
    let t = cfg.threshold;
    let xs: Vec<u8> = shares
        .iter()
        .take(t)
        .map(|s| {
            if s.index == 0 || s.index > 255 {
                0
            } else {
                s.index as u8
            }
        })
        .collect();

    // Validate indices (nonzero, unique).
    for &x in &xs {
        if x == 0 {
            return Err(ShamirError::IndexOutOfRange);
        }
    }
    for i in 0..xs.len() {
        for j in (i + 1)..xs.len() {
            if xs[i] == xs[j] {
                return Err(ShamirError::DuplicateIndex);
            }
        }
    }

    // Lagrange basis at 0:
    // λ_i(0) = Π_{j≠i} x_j / (x_j - x_i)  in GF(256), where subtraction is XOR (same as add).
    let mut secret = [0u8; 32];
    for b in 0..32 {
        let mut acc = 0u8;
        for i in 0..t {
            let xi = xs[i];
            let yi = shares[i].value[b];

            let mut num = 1u8;
            let mut den = 1u8;
            for j in 0..t {
                if i == j {
                    continue;
                }
                let xj = xs[j];
                num = gf256_mul(num, xj);
                den = gf256_mul(den, gf256_add(xj, xi)); // (xj - xi) == (xj + xi) in char-2
            }
            let li = gf256_mul(num, gf256_inv(den));
            acc = gf256_add(acc, gf256_mul(li, yi));
        }
        secret[b] = acc;
    }
    Ok(secret)
}

// ------------------------- GF(256) arithmetic -------------------------
// Field: GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1 (0x11b).

#[inline]
fn gf256_add(a: u8, b: u8) -> u8 {
    a ^ b
}

#[inline]
fn gf256_mul(mut a: u8, mut b: u8) -> u8 {
    let mut p: u8 = 0;
    for _ in 0..8 {
        if (b & 1) != 0 {
            p ^= a;
        }
        let hi = a & 0x80;
        a <<= 1;
        if hi != 0 {
            a ^= 0x1b; // reduction for 0x11b
        }
        b >>= 1;
    }
    p
}

#[inline]
fn gf256_pow(mut a: u8, mut e: u16) -> u8 {
    let mut r: u8 = 1;
    while e > 0 {
        if (e & 1) == 1 {
            r = gf256_mul(r, a);
        }
        a = gf256_mul(a, a);
        e >>= 1;
    }
    r
}

#[inline]
fn gf256_inv(a: u8) -> u8 {
    // a^(2^8-2) = a^254 for nonzero a
    // We rely on upstream validation to avoid inverting 0.
    gf256_pow(a, 254)
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand_chacha::ChaCha20Rng;
    use rand_core::SeedableRng;

    #[test]
    fn test_split_reconstruct_32() {
        let mut rng = ChaCha20Rng::seed_from_u64(123);
        let cfg = ShamirConfig {
            threshold: 5,
            shares: 20,
        };
        let secret = [7u8; 32];
        let shares = split_secret_32(&mut rng, &cfg, secret).unwrap();
        assert_eq!(shares.len(), cfg.shares);

        // Take any 5 shares.
        let rec = reconstruct_secret_32(&cfg, &shares[3..8]).unwrap();
        assert_eq!(rec, secret);
    }

    #[test]
    fn test_duplicate_index_reject() {
        let cfg = ShamirConfig {
            threshold: 2,
            shares: 3,
        };
        let s = ShamirShare {
            index: 1,
            value: [1u8; 32],
        };
        let bad = reconstruct_secret_32(&cfg, &[s.clone(), s]);
        assert!(matches!(bad, Err(ShamirError::DuplicateIndex)));
    }
}

