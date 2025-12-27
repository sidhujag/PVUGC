//! GPT-Pro Phase 2+3 glue crate.
//!
//! This crate owns the **public** `EvalTag(x,π)` streaming evaluator plumbing:
//! - read PVRS blocks (strict streaming)
//! - EvalTagBasis under BFV/BGV (ct×pt + adds; SlotSum once at end)
//! - CombineWeights (binary adds for v0)
//! - fake gate (dev): decrypt+compare

use anyhow::{anyhow, Context, Result};
use std::fs;
use std::io::Read;
use std::path::Path;

use pq_basis_blob::{ShapeBlobManifestV0, WeightsKind};

#[derive(Clone, Debug)]
pub struct PvrsHeaderV0 {
    pub slot_count: u32,
    pub block_count: u64,
    pub residuals_emitted: u64,
    pub statement_hash: [u8; 32],
    pub shape_id_hash: [u8; 32],
}

/// Parse PVRS v0 header.
///
/// Layout matches SP1 `PvrsHeaderV0` (magic, version, slot_count, block_count, residuals_emitted,
/// statement_hash, shape_id_hash).
pub fn parse_pvrs_header_v0(path: &Path) -> Result<PvrsHeaderV0> {
    let mut f = fs::File::open(path).with_context(|| format!("open {}", path.display()))?;
    let mut buf = [0u8; 92];
    f.read_exact(&mut buf).with_context(|| format!("read pvrs header {}", path.display()))?;

    // SP1 header (fixed 92 bytes):
    // magic[4], version[u32], slot_count[u32], block_count[u64], residuals_emitted[u64],
    // statement_hash[32], shape_id_hash[32]
    anyhow::ensure!(&buf[0..4] == b"PVRS", "bad PVRS magic");
    let version = u32::from_le_bytes(buf[4..8].try_into().unwrap());
    anyhow::ensure!(version == 0, "unsupported PVRS version {version}");
    let slot_count = u32::from_le_bytes(buf[8..12].try_into().unwrap());
    let block_count = u64::from_le_bytes(buf[12..20].try_into().unwrap());
    let residuals_emitted = u64::from_le_bytes(buf[20..28].try_into().unwrap());
    let mut statement_hash = [0u8; 32];
    statement_hash.copy_from_slice(&buf[28..60]);
    let mut shape_id_hash = [0u8; 32];
    shape_id_hash.copy_from_slice(&buf[60..92]);
    Ok(PvrsHeaderV0 {
        slot_count,
        block_count,
        residuals_emitted,
        statement_hash,
        shape_id_hash,
    })
}

/// Minimal v0 input derived from armer artifacts (demo trust).
#[derive(Clone, Debug)]
pub struct ArmerInputV0 {
    pub armer_id: u32,
    pub statement_hash: [u8; 32],
    pub alpha_limbs: Vec<u64>, // len = d
    pub sigma_i_clear: [u8; 32],
    pub c_i_sha256: [u8; 32],
    pub weights_row: Vec<Vec<u64>>, // vec[d][s]
}

#[cfg(feature = "pq-openfhe")]
pub fn decap_openfhe(shape_blob_dir: &Path, residual_file: &Path, armers: &[ArmerInputV0]) -> Result<()> {
    use pq_fhe_backend::FheBackend;
    use pq_fhe_openfhe::{decrypt_packed_with_len, CtChunkReader, OpenFheBackend};

    // Load manifest
    let manifest_path = shape_blob_dir.join("manifest.json");
    let manifest_bytes =
        fs::read(&manifest_path).with_context(|| format!("read {}", manifest_path.display()))?;
    let m: ShapeBlobManifestV0 = serde_json::from_slice(&manifest_bytes).context("parse manifest.json")?;
    anyhow::ensure!(m.version == 0, "unsupported manifest version {}", m.version);
    anyhow::ensure!(
        m.weights_kind == WeightsKind::Binary01,
        "v0 decap_openfhe requires weights_kind=Binary01"
    );
    let of = m
        .openfhe
        .clone()
        .ok_or_else(|| anyhow!("manifest missing openfhe section; run setup-shape-openfhe"))?;
    anyhow::ensure!(of.scheme == "BFVRNS", "unsupported scheme {}", of.scheme);
    let serial_mode = OpenFheBackend::parse_serial_mode(&of.serial_mode)?;

    // PVRS checks
    let pvrs = parse_pvrs_header_v0(residual_file)?;
    anyhow::ensure!(pvrs.slot_count as usize == m.slot_count, "slot_count mismatch (pvrs vs manifest)");
    anyhow::ensure!(pvrs.block_count as usize == m.block_count, "block_count mismatch (pvrs vs manifest)");
    for a in armers {
        anyhow::ensure!(
            a.statement_hash == pvrs.statement_hash,
            "statement_hash mismatch (armer vs pvrs)"
        );
    }

    // Track AND across limbs (real gate wants all limbs to match).
    let mut ok_all_limbs = vec![true; armers.len()];

    // Stream blocks once per limb (v0 simple implementation).
    for limb in 0..m.d_limbs {
        let limb_cfg = of
            .limbs
            .iter()
            .find(|x| x.limb == limb)
            .ok_or_else(|| anyhow!("missing openfhe limb {limb}"))?
            .clone();
        let pt_mod = limb_cfg.plaintext_modulus;

        // Deserialize OpenFHE artifacts for this limb.
        let ctx = OpenFheBackend::deserialize_crypto_context(
            shape_blob_dir.join(&limb_cfg.crypto_context_path).to_string_lossy().as_ref(),
            serial_mode,
        )?;
        let pk = OpenFheBackend::deserialize_public_key(
            shape_blob_dir.join(&limb_cfg.public_key_path).to_string_lossy().as_ref(),
            serial_mode,
        )?;
        let sk = OpenFheBackend::deserialize_private_key(
            shape_blob_dir.join(&limb_cfg.private_key_path).to_string_lossy().as_ref(),
            serial_mode,
        )?;
        OpenFheBackend::deserialize_eval_mult_key(
            shape_blob_dir.join(&limb_cfg.eval_mult_key_path).to_string_lossy().as_ref(),
            serial_mode,
        )?;
        OpenFheBackend::deserialize_eval_rot_key(
            shape_blob_dir.join(&limb_cfg.eval_rot_key_path).to_string_lossy().as_ref(),
            serial_mode,
        )?;

        // Prepare Enc(0-vector) for basis accumulators.
        let zeros = vec![0i64; m.slot_count];
        let pt_zero = OpenFheBackend::make_packed_plaintext(&ctx, &zeros)?;
        let mut ct_acc_basis: Vec<_> = (0..m.s_basis)
            .map(|_| OpenFheBackend::encrypt(&ctx, &pk, &pt_zero))
            .collect::<Result<Vec<_>>>()?;

        // Stream PVRS blocks and chunked ciphertexts together.
        let mut pvrs_f = fs::File::open(residual_file).with_context(|| format!("open {}", residual_file.display()))?;
        let mut header = [0u8; 92];
        pvrs_f.read_exact(&mut header)?;
        let mut block_buf = vec![0u8; m.slot_count * 4];

        let mut chunk_start = 0usize;
        while chunk_start < m.block_count {
            let chunk_end = (chunk_start + m.blocks_per_chunk).min(m.block_count);
            let chunk_len = chunk_end - chunk_start;

            // Open one ciphertext reader per basis j for this chunk.
            let mut readers: Vec<CtChunkReader> = Vec::with_capacity(m.s_basis);
            for j in 0..m.s_basis {
                let ct_path = m.basis_chunk_path(shape_blob_dir, limb, j, chunk_start, chunk_end);
                let ct_path_s = ct_path.to_string_lossy().into_owned();
                readers.push(CtChunkReader::open(&ct_path_s, serial_mode)?);
            }

            for off in 0..chunk_len {
                let b = chunk_start + off;
                pvrs_f
                    .read_exact(&mut block_buf)
                    .with_context(|| format!("read pvrs block {b}"))?;
                let mut r_vals = Vec::with_capacity(m.slot_count);
                for s in 0..m.slot_count {
                    let offb = s * 4;
                    let w = u32::from_le_bytes(block_buf[offb..offb + 4].try_into().unwrap());
                    r_vals.push(((w as u64) % pt_mod) as i64);
                }
                let pt_r = OpenFheBackend::make_packed_plaintext(&ctx, &r_vals)?;

                // EvalTagBasis using chunk readers (one ciphertext per (j,b)).
                for j in 0..m.s_basis {
                    let ct_k = readers[j]
                        .next()?
                        .ok_or_else(|| anyhow!("unexpected EOF in ct chunk (limb={limb}, j={j}, b={b})"))?;
                    let ct_mul = OpenFheBackend::eval_mult_plain(&ctx, &ct_k, &pt_r)?;
                    ct_acc_basis[j] = OpenFheBackend::eval_add(&ctx, &ct_acc_basis[j], &ct_mul)?;
                }
            }

            chunk_start = chunk_end;
        }

        // SlotSum each basis accumulator once.
        // SlotSum is linear, so for many armers it's cheaper to pre-sum the basis ciphertexts and
        // then only do CombineWeights (adds) per armer.
        let mut ct_acc_basis_summed = Vec::with_capacity(m.s_basis);
        for mut ct in ct_acc_basis.into_iter() {
            let mut shift = 1i32;
            while (shift as usize) < m.slot_count {
                let rot = OpenFheBackend::eval_rotate(&ctx, &ct, shift)?;
                ct = OpenFheBackend::eval_add(&ctx, &ct, &rot)?;
                shift <<= 1;
            }
            ct_acc_basis_summed.push(ct);
        }

        // For each armer: CombineWeights (binary) on summed basis -> +alpha -> decrypt+compare.
        for (ai, a) in armers.iter().enumerate() {
            anyhow::ensure!(a.alpha_limbs.len() == m.d_limbs, "alpha limbs mismatch");
            anyhow::ensure!(a.weights_row.len() == m.d_limbs, "weights_row limb mismatch");
            let row = &a.weights_row[limb];
            anyhow::ensure!(row.len() == m.s_basis, "weights_row width mismatch");

            let alpha = a.alpha_limbs[limb] % pt_mod;
            let mut ct_i = OpenFheBackend::encrypt(&ctx, &pk, &pt_zero)?;
            for j in 0..m.s_basis {
                let w = row[j];
                anyhow::ensure!(w == 0 || w == 1, "binary weight expected (got {w})");
                if w == 1 {
                    ct_i = OpenFheBackend::eval_add(&ctx, &ct_i, &ct_acc_basis_summed[j])?;
                }
            }

            // Add alpha across all slots.
            let pt_alpha =
                OpenFheBackend::make_packed_plaintext(&ctx, &vec![alpha as i64; m.slot_count])?;
            let ct_tag = OpenFheBackend::eval_add_plain(&ctx, &ct_i, &pt_alpha)?;

            // Fake gate: decrypt and compare slot0 to alpha.
            let dec = decrypt_packed_with_len(&ctx, &sk, &ct_tag, m.slot_count)?;
            let t0 = *dec.get(0).unwrap_or(&0);
            // BFV packed decoding can return centered representatives (negative values).
            // Normalize to [0, t) before comparing to alpha mod t.
            let t_i64 = pt_mod as i64;
            let mut t0_mod = t0 % t_i64;
            if t0_mod < 0 {
                t0_mod += t_i64;
            }
            let ok = t0_mod == (alpha as i64);
            ok_all_limbs[ai] &= ok;
        }
    }

    for (ai, a) in armers.iter().enumerate() {
        println!(
            "decap-openfhe armer_id={} UNLOCK={}",
            a.armer_id,
            if ok_all_limbs[ai] { "YES" } else { "NO" }
        );
        if ok_all_limbs[ai] {
            println!("sigma_i_hex={}", hex::encode(a.sigma_i_clear));
            println!("c_i_sha256={}", hex::encode(a.c_i_sha256));
        }
    }

    Ok(())
}

