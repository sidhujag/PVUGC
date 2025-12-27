use anyhow::{anyhow, Result};
use sha2::{Digest, Sha256};

use super::{ArmerId, ShapeId, StatementHash32};
pub use pq_basis_blob::WeightsKind;

/// Weights matrix W(x) ∈ Z_p^{N×s} for a particular limb modulus p.
#[derive(Clone, Debug)]
pub struct WeightsMatrix {
    pub modulus: u64,
    pub n_armers: usize,
    pub s_basis: usize,
    /// Row-major: w[i][j]
    pub w: Vec<u64>,
    /// Retry counter used to obtain full rank.
    pub retry_counter: u32,
    pub kind: WeightsKind,
}

impl WeightsMatrix {
    pub fn get(&self, i: usize, j: usize) -> u64 {
        self.w[i * self.s_basis + j]
    }
}

/// Deterministically derive a full-rank (rank ≥ N) weight matrix over Z_p.
///
/// Seed material follows GPT Pro guidance:
/// H(domainsep || shape_id || statement_hash || epoch || retry_counter)
pub fn derive_weights_matrix(
    domainsep: &[u8],
    shape_id: &ShapeId,
    statement_hash: &StatementHash32,
    epoch: u64,
    n_armers: usize,
    s_basis: usize,
    modulus: u64,
) -> Result<WeightsMatrix> {
    derive_weights_matrix_with_kind(
        domainsep,
        shape_id,
        statement_hash,
        epoch,
        n_armers,
        s_basis,
        modulus,
        WeightsKind::Full,
    )
}

pub fn derive_weights_matrix_with_kind(
    domainsep: &[u8],
    shape_id: &ShapeId,
    statement_hash: &StatementHash32,
    epoch: u64,
    n_armers: usize,
    s_basis: usize,
    modulus: u64,
    kind: WeightsKind,
) -> Result<WeightsMatrix> {
    anyhow::ensure!(n_armers > 0, "n_armers must be > 0");
    anyhow::ensure!(s_basis > 0, "s_basis must be > 0");
    anyhow::ensure!(s_basis >= n_armers, "need s_basis >= n_armers for rank >= N");
    anyhow::ensure!(modulus > 2, "modulus must be > 2");

    for retry_counter in 0u32..10_000 {
        let mut w = vec![0u64; n_armers * s_basis];
        fill_prg_matrix(
            &mut w,
            domainsep,
            &shape_id.0,
            &statement_hash.0,
            epoch,
            retry_counter,
            modulus,
            kind,
        );
        if rank_ge_n(&w, n_armers, s_basis, modulus)? {
            return Ok(WeightsMatrix {
                modulus,
                n_armers,
                s_basis,
                w,
                retry_counter,
                kind,
            });
        }
    }
    Err(anyhow!("failed to derive full-rank W(x) after many retries"))
}

fn fill_prg_matrix(
    out: &mut [u64],
    domainsep: &[u8],
    shape_id: &str,
    statement_hash: &[u8; 32],
    epoch: u64,
    retry_counter: u32,
    modulus: u64,
    kind: WeightsKind,
) {
    // Expand with a simple hash-stream (sufficient for deterministic engineering; crypto model is via H).
    // Each block emits 32 bytes; we consume 8 bytes at a time to form u64 and reduce mod p.
    let mut ctr: u64 = 0;
    let mut i = 0usize;
    while i < out.len() {
        let mut h = Sha256::new();
        h.update(domainsep);
        h.update(shape_id.as_bytes());
        h.update(statement_hash);
        h.update(epoch.to_le_bytes());
        h.update(retry_counter.to_le_bytes());
        h.update(ctr.to_le_bytes());
        let digest = h.finalize();

        for chunk in digest.chunks_exact(8) {
            if i >= out.len() {
                break;
            }
            let mut b = [0u8; 8];
            b.copy_from_slice(chunk);
            let v = u64::from_le_bytes(b) % modulus;
            out[i] = match kind {
                WeightsKind::Full => v,
                WeightsKind::Binary01 => v & 1,
            };
            i += 1;
        }
        ctr += 1;
    }
}

/// Check whether rank(W) >= n over Z_p using Gaussian elimination.
fn rank_ge_n(w: &[u64], n: usize, s: usize, p: u64) -> Result<bool> {
    // Copy matrix (row-major) for elimination.
    let mut a = w.to_vec();
    let mut rank = 0usize;
    let mut col = 0usize;
    while rank < n && col < s {
        // Find pivot row.
        let mut pivot = None;
        for r in rank..n {
            if a[r * s + col] % p != 0 {
                pivot = Some(r);
                break;
            }
        }
        if pivot.is_none() {
            col += 1;
            continue;
        }
        let pivot = pivot.unwrap();
        if pivot != rank {
            // swap rows
            for c in 0..s {
                a.swap(rank * s + c, pivot * s + c);
            }
        }

        let piv = a[rank * s + col] % p;
        let inv = mod_inv(piv, p).ok_or_else(|| anyhow!("no inverse mod p (p not prime?)"))?;

        // Normalize pivot row.
        for c in col..s {
            a[rank * s + c] = mod_mul(a[rank * s + c] % p, inv, p);
        }

        // Eliminate other rows.
        for r in 0..n {
            if r == rank {
                continue;
            }
            let f = a[r * s + col] % p;
            if f == 0 {
                continue;
            }
            for c in col..s {
                let rc = r * s + c;
                let pc = rank * s + c;
                let sub = mod_mul(f, a[pc] % p, p);
                a[rc] = mod_sub(a[rc] % p, sub, p);
            }
        }

        rank += 1;
        col += 1;
    }
    Ok(rank >= n)
}

#[inline]
fn mod_add(a: u64, b: u64, p: u64) -> u64 {
    ((a as u128 + b as u128) % (p as u128)) as u64
}

#[inline]
fn mod_sub(a: u64, b: u64, p: u64) -> u64 {
    let aa = a as i128;
    let bb = b as i128;
    let pp = p as i128;
    let mut v = aa - bb;
    v %= pp;
    if v < 0 {
        v += pp;
    }
    v as u64
}

#[inline]
fn mod_mul(a: u64, b: u64, p: u64) -> u64 {
    ((a as u128 * b as u128) % (p as u128)) as u64
}

// Extended Euclid for inverse; assumes p is prime in the intended use.
fn mod_inv(a: u64, p: u64) -> Option<u64> {
    let mut t: i128 = 0;
    let mut new_t: i128 = 1;
    let mut r: i128 = p as i128;
    let mut new_r: i128 = (a % p) as i128;
    while new_r != 0 {
        let q = r / new_r;
        (t, new_t) = (new_t, t - q * new_t);
        (r, new_r) = (new_r, r - q * new_r);
    }
    if r != 1 {
        return None;
    }
    if t < 0 {
        t += p as i128;
    }
    Some(t as u64)
}

#[allow(dead_code)]
fn _weights_row_domain_sep_example(armer: ArmerId) -> Vec<u8> {
    // Helpful domain separation example: include armer id at the caller side.
    let mut d = b"pvugc.weights.v0".to_vec();
    d.extend_from_slice(&armer.0.to_le_bytes());
    d
}


