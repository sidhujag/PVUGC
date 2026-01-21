//! Noisy linear hint + AEAD lock for a single Shamir share.
//!
//! This follows the intent of Architecture‑T:
//! - derive a secret query vector `q` from (seed, statement, j)
//! - produce noisy hint vectors `h0 = s0*q + e0 (mod 2^64)` and `h1 = s1*q + e1 (mod 2^64)`
//! - let a decapper compute `inner0 = <h0, w> ≈ s0*<q,w>` and `inner1 = <h1, w> ≈ s1*<q,w>`
//!   and derive an AEAD key from `Round(inner0) || Round(inner1)`.
//!
//! This design **requires** the upstream DPP to ensure `<q,w>` is a fixed statement-derived target
//! (e.g. singleton accepting set) for valid witnesses.

use aes_gcm::{
    aead::{Aead, KeyInit},
    Aes256Gcm, Nonce,
};
use rand::RngCore;
use rand_distr::{Distribution, Normal};
use sha2::{Digest, Sha256};
use thiserror::Error;

use crate::shamir::{reconstruct_secret_32, split_secret_32, ShamirConfig, ShamirShare};

#[derive(Clone, Debug)]
pub struct ArmConfig {
    /// Vector dimension (must match the witness vector length used in decap).
    pub dim: usize,
    /// Noise standard deviation (prototype parameter).
    pub noise_sigma: f64,
}

#[derive(Clone, Debug)]
pub struct DecapConfig {
    /// Same dim as used at arming time.
    pub dim: usize,
}

/// The AEAD key identifier for a lock: derived from statement + lock index.
#[derive(Clone, Debug)]
pub struct ArmKey {
    pub lock_index: u32,
    pub statement_hash: [u8; 32],
}

/// Compute the binding hash for a statement, including a VK hash.
///
/// The armer should use this as `statement_hash` so locks are bound to `(vk_hash || statement_x)`.
pub fn statement_hash(vk_hash: [u8; 32], statement_x: &[u8]) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"PVUGC_WE_STATEMENT_V1");
    h.update(&vk_hash);
    h.update(&(statement_x.len() as u64).to_le_bytes());
    h.update(statement_x);
    h.finalize().into()
}

/// Derive a *public* per-lock target `t_j` from the statement binding hash.
///
/// In the full design, `t_j` should come from the DPP verifier (singleton accepting set / rounded
/// target). This helper provides a deterministic placeholder derived from the statement.
pub fn derive_target_u32(statement_hash: [u8; 32], lock_index: u32) -> u32 {
    let mut h = Sha256::new();
    h.update(b"PVUGC_LWE_TARGET_V1");
    h.update(&statement_hash);
    h.update(&lock_index.to_le_bytes());
    let digest = h.finalize();
    u32::from_le_bytes(digest[..4].try_into().unwrap())
}

#[derive(Clone, Debug)]
pub struct LockArtifact {
    pub lock_index: u32,
    pub statement_hash: [u8; 32],
    /// Noisy hint vector h0 (length = dim), interpreted in Z/2^64Z.
    pub hint0: Vec<u64>,
    /// Noisy hint vector h1 (length = dim), interpreted in Z/2^64Z.
    pub hint1: Vec<u64>,
    /// AEAD nonce.
    pub nonce: [u8; 12],
    /// Ciphertext of the Shamir share bytes.
    pub ciphertext: Vec<u8>,
}

#[derive(Debug, Error)]
pub enum LockError {
    #[error("invalid parameters")]
    InvalidParams,
    #[error("aead decrypt failed")]
    DecryptFailed,
    #[error("shamir error: {0}")]
    Shamir(#[from] crate::shamir::ShamirError),
}

/// Derive a query vector `q` in (Z/2^64Z)^dim from (seed, statement_hash, lock_index).
///
/// This is deterministic and **secret** to the armer (seed is secret).
pub fn derive_query_u64(
    seed: [u8; 32],
    statement_hash: [u8; 32],
    lock_index: u32,
    dim: usize,
) -> Vec<u64> {
    // XOF-ish expansion using SHA256 in counter mode.
    let mut out = Vec::with_capacity(dim);
    let mut ctr = 0u32;
    while out.len() < dim {
        let mut h = Sha256::new();
        h.update(b"PVUGC_LWE_QUERY_V1");
        h.update(&seed);
        h.update(&statement_hash);
        h.update(&lock_index.to_le_bytes());
        h.update(&ctr.to_le_bytes());
        let digest = h.finalize();
        // 32 bytes -> 4 u64
        for chunk in digest.chunks_exact(8) {
            if out.len() == dim {
                break;
            }
            out.push(u64::from_le_bytes(chunk.try_into().unwrap()));
        }
        ctr = ctr.wrapping_add(1);
    }
    out
}

/// Arm (lock) a single share using a noisy hint and AEAD.
///
/// - `seed` is armer-secret and must never be revealed.
/// - `statement_hash` must bind to (vk_hash || statement_x || ...).
/// - `target` is the expected value `<q,w>` for valid witnesses (singleton accepting set).
pub fn arm_share(
    rng: &mut dyn RngCore,
    cfg: &ArmConfig,
    seed: [u8; 32],
    statement_hash: [u8; 32],
    lock_index: u32,
    target: u64,
    plaintext_share: &[u8],
) -> Result<LockArtifact, LockError> {
    if cfg.dim == 0 || !cfg.noise_sigma.is_finite() || cfg.noise_sigma < 0.0 {
        return Err(LockError::InvalidParams);
    }

    let q = derive_query_u64(seed, statement_hash, lock_index, cfg.dim);

    // Sample scalar secrets s0,s1 (uniform mod 2^64).
    let s0 = next_u64(rng);
    let s1 = next_u64(rng);

    // Noise e_i ~ N(0, sigma) rounded to i64, then embedded in Z/2^64Z.
    let normal = Normal::new(0.0, cfg.noise_sigma).map_err(|_| LockError::InvalidParams)?;
    let mut hint0 = Vec::with_capacity(cfg.dim);
    let mut hint1 = Vec::with_capacity(cfg.dim);
    for &qi in &q {
        let e0: i64 = normal.sample(&mut rand_adapter(rng)).round() as i64;
        let e1: i64 = normal.sample(&mut rand_adapter(rng)).round() as i64;
        let h0 = qi.wrapping_mul(s0).wrapping_add(e0 as u64); // wraps mod 2^64
        let h1 = qi.wrapping_mul(s1).wrapping_add(e1 as u64); // wraps mod 2^64
        hint0.push(h0);
        hint1.push(h1);
    }

    // Derive AEAD key from (k0,k1) where kℓ = sℓ * target (mod 2^64).
    let k0 = s0.wrapping_mul(target);
    let k1 = s1.wrapping_mul(target);
    let key = derive_aead_key(statement_hash, lock_index, k0, k1);
    let cipher = Aes256Gcm::new_from_slice(&key).expect("aes key length");

    // Random nonce.
    let mut nonce = [0u8; 12];
    rng.fill_bytes(&mut nonce);
    let ct = cipher
        .encrypt(Nonce::from_slice(&nonce), plaintext_share)
        .map_err(|_| LockError::InvalidParams)?;

    Ok(LockArtifact {
        lock_index,
        statement_hash,
        hint0,
        hint1,
        nonce,
        ciphertext: ct,
    })
}

/// Attempt to decapsulate a single share given the witness vector `w`.
pub fn decap_share(
    cfg: &DecapConfig,
    artifact: &LockArtifact,
    witness_vec: &[u64],
) -> Result<Vec<u8>, LockError> {
    if cfg.dim == 0
        || artifact.hint0.len() != cfg.dim
        || artifact.hint1.len() != cfg.dim
        || witness_vec.len() != cfg.dim
    {
        return Err(LockError::InvalidParams);
    }
    if artifact.statement_hash == [0u8; 32] {
        return Err(LockError::InvalidParams);
    }

    // innerℓ = <hintℓ, w> in Z/2^64Z.
    let mut inner0: u64 = 0;
    let mut inner1: u64 = 0;
    for i in 0..cfg.dim {
        let w = witness_vec[i];
        inner0 = inner0.wrapping_add(artifact.hint0[i].wrapping_mul(w));
        inner1 = inner1.wrapping_add(artifact.hint1[i].wrapping_mul(w));
    }

    // Candidate key derived from Round(inner0)||Round(inner1).
    // For now: take innerℓ as-is (mod 2^64).
    // Concrete schemes typically include scaling/rounding; the upstream boundedness of w and
    // noise choice determine the correctness probability.
    let key = derive_aead_key(artifact.statement_hash, artifact.lock_index, inner0, inner1);
    let cipher = Aes256Gcm::new_from_slice(&key).expect("aes key length");

    cipher
        .decrypt(Nonce::from_slice(&artifact.nonce), artifact.ciphertext.as_ref())
        .map_err(|_| LockError::DecryptFailed)
}

/// Arm a full threshold-lock set:
/// - split `secret` into Shamir shares (T-of-N),
/// - arm each share into a `LockArtifact`,
/// - using a per-lock `target_j` (statement-derived).
pub fn arm_lockset(
    rng: &mut dyn RngCore,
    arm: &ArmConfig,
    shamir: &ShamirConfig,
    seed: [u8; 32],
    statement_hash: [u8; 32],
    targets: &[u64],
    secret: [u8; 32],
) -> Result<Vec<LockArtifact>, LockError> {
    if shamir.threshold < 2 || shamir.shares < shamir.threshold {
        return Err(LockError::InvalidParams);
    }
    if shamir.shares > u32::MAX as usize {
        return Err(LockError::InvalidParams);
    }
    if targets.len() != shamir.shares {
        return Err(LockError::InvalidParams);
    }
    let shares: Vec<ShamirShare> = split_secret_32(rng, shamir, secret)?;
    let mut out = Vec::with_capacity(shares.len());
    for (j, s) in shares.into_iter().enumerate() {
        // Bind the lock_index to the Shamir share index.
        let lock_index = s.index;
        let target = targets[j];
        let art = arm_share(
            rng,
            arm,
            seed,
            statement_hash,
            lock_index,
            target,
            &s.value,
        )?;
        debug_assert_eq!(j + 1, lock_index as usize);
        out.push(art);
    }
    Ok(out)
}

/// Attempt to decapsulate a lockset:
/// - try to decrypt every artifact using `witness_vec`,
/// - keep the first `threshold` valid shares,
/// - reconstruct the 32-byte secret via Shamir.
pub fn decap_lockset(
    decap: &DecapConfig,
    shamir: &ShamirConfig,
    statement_hash: [u8; 32],
    artifacts: &[LockArtifact],
    witness_vec: &[u64],
) -> Result<[u8; 32], LockError> {
    if shamir.threshold < 2 || shamir.shares < shamir.threshold {
        return Err(LockError::InvalidParams);
    }
    if artifacts.is_empty() {
        return Err(LockError::InvalidParams);
    }

    let mut recovered: Vec<ShamirShare> = Vec::new();
    for art in artifacts {
        // Require binding to the exact statement hash.
        if art.statement_hash != statement_hash {
            continue;
        }
        if let Ok(plain) = decap_share(decap, art, witness_vec) {
            if plain.len() == 32 {
                let mut share_bytes = [0u8; 32];
                share_bytes.copy_from_slice(&plain);
                recovered.push(ShamirShare {
                    index: art.lock_index,
                    value: share_bytes,
                });
                if recovered.len() >= shamir.threshold {
                    break;
                }
            }
        }
    }

    Ok(reconstruct_secret_32(shamir, &recovered)?)
}

fn derive_aead_key(statement_hash: [u8; 32], lock_index: u32, k0: u64, k1: u64) -> [u8; 32] {
    let mut h = Sha256::new();
    h.update(b"PVUGC_LWE_KEY_V1");
    h.update(&statement_hash);
    h.update(&lock_index.to_le_bytes());
    h.update(&k0.to_le_bytes());
    h.update(&k1.to_le_bytes());
    h.finalize().into()
}

fn next_u32(rng: &mut dyn RngCore) -> u32 {
    let mut b = [0u8; 4];
    rng.fill_bytes(&mut b);
    u32::from_le_bytes(b)
}

fn next_u64(rng: &mut dyn RngCore) -> u64 {
    let mut b = [0u8; 8];
    rng.fill_bytes(&mut b);
    u64::from_le_bytes(b)
}

// rand_distr expects a `rand::Rng` but we only require `RngCore` at the API boundary.
// This small adapter keeps the public API minimal.
fn rand_adapter<'a>(rng: &'a mut dyn RngCore) -> RandCoreAdapter<'a> {
    RandCoreAdapter { rng }
}

struct RandCoreAdapter<'a> {
    rng: &'a mut dyn RngCore,
}

impl rand::RngCore for RandCoreAdapter<'_> {
    fn next_u32(&mut self) -> u32 {
        next_u32(self.rng)
    }
    fn next_u64(&mut self) -> u64 {
        let hi = self.next_u32() as u64;
        let lo = self.next_u32() as u64;
        (hi << 32) | lo
    }
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        self.rng.fill_bytes(dest)
    }
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand::Error> {
        self.rng.fill_bytes(dest);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    #[test]
    fn test_arm_decap_roundtrip_toy() {
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let seed = [9u8; 32];
        let statement_hash = statement_hash([2u8; 32], b"statement_x");
        let cfg = ArmConfig {
            dim: 8,
            noise_sigma: 0.0,
        };
        let share = b"hello-share".to_vec();

        // Choose witness w and set target = <q,w>.
        // Here noise_sigma=0, so correctness is deterministic.
        let lock_index = 3;
        let q = derive_query_u64(seed, statement_hash, lock_index, cfg.dim);
        let w = vec![1u64; cfg.dim];
        let mut target: u64 = 0;
        for qi in &q {
            target = target.wrapping_add(*qi);
        }

        let art =
            arm_share(&mut rng, &cfg, seed, statement_hash, lock_index, target, &share).unwrap();
        let dec = decap_share(&DecapConfig { dim: cfg.dim }, &art, &w).unwrap();
        assert_eq!(dec, share);
    }

    #[test]
    fn test_arm_decap_lockset_threshold_roundtrip() {
        let mut rng = ChaCha20Rng::seed_from_u64(9);
        let seed = [1u8; 32];
        let statement_hash = statement_hash([3u8; 32], b"statement_x");
        let arm = ArmConfig {
            dim: 16,
            noise_sigma: 0.0,
        };
        let decap = DecapConfig { dim: arm.dim };
        let shamir = ShamirConfig {
            threshold: 5,
            shares: 64,
        };

        // Witness vector and target definition (toy): w all-ones, target_j = Σ q_{j,i}.
        let w = vec![1u64; arm.dim];
        let mut targets = vec![0u64; shamir.shares];
        for j in 1..=shamir.shares {
            let q = derive_query_u64(seed, statement_hash, j as u32, arm.dim);
            let mut t: u64 = 0;
            for qi in &q {
                t = t.wrapping_add(*qi);
            }
            targets[j - 1] = t;
        }

        let secret = [0x42u8; 32];
        let locks = arm_lockset(&mut rng, &arm, &shamir, seed, statement_hash, &targets, secret)
            .unwrap();
        assert_eq!(locks.len(), shamir.shares);

        let got = decap_lockset(&decap, &shamir, statement_hash, &locks, &w).unwrap();
        assert_eq!(got, secret);

        // Wrong statement hash should not open.
        let bad = decap_lockset(&decap, &shamir, [0u8; 32], &locks, &w);
        assert!(bad.is_err());
    }
}
