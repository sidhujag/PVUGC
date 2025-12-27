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
use std::collections::HashSet;
use std::sync::{Arc, Mutex};
use std::thread;

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
    f.read_exact(&mut buf)
        .with_context(|| format!("read pvrs header {}", path.display()))?;

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

/// Read PVRS v0 blocks into memory as raw u32 words (little-endian).
///
/// Layout: header (92 bytes), then `block_count` blocks, each `slot_count` u32's.
fn read_pvrs_blocks_u32(path: &Path, slot_count: usize, block_count: usize) -> Result<Vec<u32>> {
    let mut f = fs::File::open(path).with_context(|| format!("open {}", path.display()))?;
    let mut header = [0u8; 92];
    f.read_exact(&mut header)
        .with_context(|| format!("read pvrs header {}", path.display()))?;
    let mut buf = vec![0u8; slot_count * block_count * 4];
    f.read_exact(&mut buf)
        .with_context(|| format!("read pvrs blocks {}", path.display()))?;
    let mut out = vec![0u32; slot_count * block_count];
    for i in 0..out.len() {
        let off = i * 4;
        out[i] = u32::from_le_bytes(buf[off..off + 4].try_into().unwrap());
    }
    Ok(out)
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
pub fn decap_openfhe(
    shape_blob_dir: &Path,
    residual_file: &Path,
    armers: &[ArmerInputV0],
) -> Result<()> {
    decap_openfhe_with_basis_parallelism(shape_blob_dir, residual_file, armers, 1, None)
}

/// OpenFHE decap with **one** parallelism knob.
///
/// `basis_parallelism` parallelizes the dominant ct×pt work across basis index `j` (capped at `s_basis`).
/// Limbs are always processed sequentially (simple + avoids oversubscription).
#[cfg(feature = "pq-openfhe")]
pub fn decap_openfhe_with_basis_parallelism(
    shape_blob_dir: &Path,
    residual_file: &Path,
    armers: &[ArmerInputV0],
    basis_parallelism: usize,
    emit_lwe_out_dir: Option<&Path>,
) -> Result<()> {
    use pq_fhe_backend::FheBackend;
    use pq_fhe_openfhe::{
        decrypt_packed_with_len, extract_lwe_coeff0_from_ciphertext_tower, CtChunkReader,
        CtChunkWriter, OpenFheBackend,
    };

    // Load manifest
    let manifest_path = shape_blob_dir.join("manifest.json");
    let manifest_bytes =
        fs::read(&manifest_path).with_context(|| format!("read {}", manifest_path.display()))?;
    let m: ShapeBlobManifestV0 =
        serde_json::from_slice(&manifest_bytes).context("parse manifest.json")?;
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
    anyhow::ensure!(
        pvrs.slot_count as usize == m.slot_count,
        "slot_count mismatch (pvrs vs manifest)"
    );
    anyhow::ensure!(
        pvrs.block_count as usize == m.block_count,
        "block_count mismatch (pvrs vs manifest)"
    );
    for a in armers {
        anyhow::ensure!(
            a.statement_hash == pvrs.statement_hash,
            "statement_hash mismatch (armer vs pvrs)"
        );
    }

    anyhow::ensure!(basis_parallelism > 0, "basis_parallelism must be > 0");

    // Only load PVRS blocks into memory when we need basis-parallelism. Otherwise keep strict streaming.
    let pvrs_blocks_u32: Option<Arc<Vec<u32>>> = if basis_parallelism > 1 {
        Some(Arc::new(read_pvrs_blocks_u32(
            residual_file,
            m.slot_count,
            m.block_count,
        )?))
    } else {
        None
    };

    let basis_shared_across_limbs = m.basis_shared_across_limbs;
    let basis_chunk_path = |limb: usize, j: usize, start_block: usize, end_block: usize| -> std::path::PathBuf {
        let limb = if basis_shared_across_limbs { 0 } else { limb };
        shape_blob_dir.join(format!(
            "basis/l{limb}/j{j}/blocks_{start_block}_{end_block}.bin"
        ))
    };

    // OpenFHE stores eval keys in a global map keyed by tag; inserting the same key twice in-process throws.
    // Track which limb indices' eval keys we've loaded, so shared-basis mode doesn't crash.
    let mut eval_keys_loaded_for_limb: HashSet<usize> = HashSet::new();

    let mut do_limb = |limb: usize| -> Result<Vec<bool>> {
        let limb_idx = if m.basis_shared_across_limbs { 0 } else { limb };
        let limb_cfg = of
            .limbs
            .iter()
            .find(|x| x.limb == limb_idx)
            .ok_or_else(|| anyhow!("missing openfhe limb {limb_idx}"))?
            .clone();
        let pt_mod = limb_cfg.plaintext_modulus;

        // Deserialize OpenFHE artifacts for this limb.
        let ctx = OpenFheBackend::deserialize_crypto_context(
            shape_blob_dir
                .join(&limb_cfg.crypto_context_path)
                .to_string_lossy()
                .as_ref(),
            serial_mode,
        )?;
        let pk = OpenFheBackend::deserialize_public_key(
            shape_blob_dir
                .join(&limb_cfg.public_key_path)
                .to_string_lossy()
                .as_ref(),
            serial_mode,
        )?;
        let sk = OpenFheBackend::deserialize_private_key(
            shape_blob_dir
                .join(&limb_cfg.private_key_path)
                .to_string_lossy()
                .as_ref(),
            serial_mode,
        )?;
        // Eval keys (ct×pt mult + SlotSum rotations).
        //
        // IMPORTANT: OpenFHE stores eval keys in a global map keyed by tag; inserting the same
        // key twice in-process throws. So we must deserialize them exactly once per limb index.
        if eval_keys_loaded_for_limb.insert(limb_idx) {
            OpenFheBackend::deserialize_eval_mult_key(
                shape_blob_dir
                    .join(&limb_cfg.eval_mult_key_path)
                    .to_string_lossy()
                    .as_ref(),
                serial_mode,
            )?;
            OpenFheBackend::deserialize_eval_rot_key(
                shape_blob_dir
                    .join(&limb_cfg.eval_rot_key_path)
                    .to_string_lossy()
                    .as_ref(),
                serial_mode,
            )?;
        }

        // Prepare Enc(0-vector) for basis accumulators.
        let zeros = vec![0i64; m.slot_count];
        let pt_zero = OpenFheBackend::make_packed_plaintext(&ctx, &zeros)?;
        let ct_acc_basis_summed = if basis_parallelism <= 1 {
            // Sequential basis-first evaluation (simple, streaming).
            let mut ct_acc_basis: Vec<_> = (0..m.s_basis)
                .map(|_| OpenFheBackend::encrypt(&ctx, &pk, &pt_zero))
                .collect::<Result<Vec<_>>>()?;

            // Stream PVRS blocks and chunked ciphertexts together.
            let mut pvrs_f = fs::File::open(residual_file)
                .with_context(|| format!("open {}", residual_file.display()))?;
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
                    let ct_path = basis_chunk_path(limb, j, chunk_start, chunk_end);
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
                        let ct_k = readers[j].next()?.ok_or_else(|| {
                            anyhow!("unexpected EOF in ct chunk (limb={limb}, j={j}, b={b})")
                        })?;
                        let ct_mul = OpenFheBackend::eval_mult_plain(&ctx, &ct_k, &pt_r)?;
                        ct_acc_basis[j] =
                            OpenFheBackend::eval_add(&ctx, &ct_acc_basis[j], &ct_mul)?;
                    }
                }

                chunk_start = chunk_end;
            }

            // SlotSum each basis accumulator once.
            let mut out = Vec::with_capacity(m.s_basis);
            for mut ct in ct_acc_basis.into_iter() {
                let mut shift = 1i32;
                while (shift as usize) < m.slot_count {
                    let rot = OpenFheBackend::eval_rotate(&ctx, &ct, shift)?;
                    ct = OpenFheBackend::eval_add(&ctx, &ct, &rot)?;
                    shift <<= 1;
                }
                out.push(ct);
            }
            out
        } else {
            // Basis-parallel evaluation: split basis indices `j` across threads.
            //
            // Each thread keeps its own OpenFHE ctx/keys (no pointer sharing) and writes each
            // resulting ctAcc_basis_summed[j] to a temp file as a single-element ciphertext stream.
            // The main thread reads them back and does CombineWeights + fake gate.
            //
            // This is designed to light up many cores (dominant ct×pt multiplies) while avoiding
            // OpenFHE thread-safety pitfalls around shared C++ pointers.
            let n_threads = basis_parallelism.min(m.s_basis).max(1);
            let tmp_dir = std::env::temp_dir().join("pvugc_pq_decap_tmp");
            fs::create_dir_all(&tmp_dir).ok();

            let out_paths: Arc<Mutex<Vec<Option<String>>>> =
                Arc::new(Mutex::new(vec![None; m.s_basis]));

            // Copy strings for thread moves.
            let cc_path = shape_blob_dir
                .join(&limb_cfg.crypto_context_path)
                .to_string_lossy()
                .into_owned();
            let pk_path = shape_blob_dir
                .join(&limb_cfg.public_key_path)
                .to_string_lossy()
                .into_owned();
            let _em_path = shape_blob_dir
                .join(&limb_cfg.eval_mult_key_path)
                .to_string_lossy()
                .into_owned();
            let _er_path = shape_blob_dir
                .join(&limb_cfg.eval_rot_key_path)
                .to_string_lossy()
                .into_owned();

            // Work partition: contiguous chunks.
            let mut parts: Vec<Vec<usize>> = vec![Vec::new(); n_threads];
            for j in 0..m.s_basis {
                parts[j % n_threads].push(j);
            }

            thread::scope(|scope| -> Result<()> {
                let mut handles = Vec::with_capacity(n_threads);
                for (ti, js) in parts.into_iter().enumerate() {
                    let out_paths = Arc::clone(&out_paths);
                    let pvrs_blocks_u32 = Arc::clone(pvrs_blocks_u32.as_ref().expect("pvrs_blocks_u32 must exist"));
                    let tmp_dir = tmp_dir.clone();
                    let cc_path = cc_path.clone();
                    let pk_path = pk_path.clone();

                    let h = scope.spawn(move || -> Result<()> {
                        let ctx = OpenFheBackend::deserialize_crypto_context(&cc_path, serial_mode)?;
                        let pk = OpenFheBackend::deserialize_public_key(&pk_path, serial_mode)?;

                        let zeros = vec![0i64; m.slot_count];
                        let pt_zero = OpenFheBackend::make_packed_plaintext(&ctx, &zeros)?;
                        let mut r_vals = vec![0i64; m.slot_count];

                        for &j in &js {
                            let mut ct_acc = OpenFheBackend::encrypt(&ctx, &pk, &pt_zero)?;

                            // Read ctK[j,b,limb] in strict order (chunked), and multiply by PVRS residuals.
                            let mut chunk_start = 0usize;
                            while chunk_start < m.block_count {
                                let chunk_end = (chunk_start + m.blocks_per_chunk).min(m.block_count);
                                let chunk_len = chunk_end - chunk_start;
                                let ct_path = basis_chunk_path(limb, j, chunk_start, chunk_end);
                                let mut reader = CtChunkReader::open(&ct_path.to_string_lossy(), serial_mode)?;

                                for off in 0..chunk_len {
                                    let b = chunk_start + off;
                                    let base = b * m.slot_count;
                                    for s in 0..m.slot_count {
                                        let w = pvrs_blocks_u32[base + s];
                                        r_vals[s] = ((w as u64) % pt_mod) as i64;
                                    }
                                    let pt_r = OpenFheBackend::make_packed_plaintext(&ctx, &r_vals)?;
                                    let ct_k = reader
                                        .next()?
                                        .ok_or_else(|| anyhow!("unexpected EOF in ct chunk (limb={limb}, j={j}, b={b})"))?;
                                    let ct_mul = OpenFheBackend::eval_mult_plain(&ctx, &ct_k, &pt_r)?;
                                    ct_acc = OpenFheBackend::eval_add(&ctx, &ct_acc, &ct_mul)?;
                                }

                                chunk_start = chunk_end;
                            }

                            // SlotSum.
                            let mut shift = 1i32;
                            while (shift as usize) < m.slot_count {
                                let rot = OpenFheBackend::eval_rotate(&ctx, &ct_acc, shift)?;
                                ct_acc = OpenFheBackend::eval_add(&ctx, &ct_acc, &rot)?;
                                shift <<= 1;
                            }

                            // Write to temp as a single-element ciphertext stream.
                            let nonce = (ti as u64) ^ ((j as u64) << 32);
                            let out_path = tmp_dir.join(format!("l{limb}_j{j}_n{nonce}.bin"));
                            let out_path_s = out_path.to_string_lossy().into_owned();
                            let mut w = CtChunkWriter::create(&out_path_s, serial_mode)?;
                            w.append(&ct_acc.ct)?;

                            out_paths.lock().unwrap()[j] = Some(out_path_s);
                        }

                        Ok(())
                    });
                    handles.push(h);
                }

                for h in handles {
                    h.join().expect("basis-parallel thread panicked")?;
                }
                Ok(())
            })
            .context("basis-parallel worker scope")?;

            // Read back ciphertexts into this limb's main thread.
            let mut out = Vec::with_capacity(m.s_basis);
            let mut paths = out_paths.lock().unwrap();
            for j in 0..m.s_basis {
                let p = paths[j].take().ok_or_else(|| {
                    anyhow!("missing temp basis accumulator for limb={limb} j={j}")
                })?;
                let mut r = CtChunkReader::open(&p, serial_mode)?;
                let ct = r
                    .next()?
                    .ok_or_else(|| anyhow!("temp ct file had no ciphertext: {p}"))?;
                let _ = fs::remove_file(&p);
                out.push(ct);
            }
            out
        };

        // For each armer: CombineWeights (binary) on summed basis -> (optional bridge dump) -> +alpha -> decrypt+compare.
        let mut ok = vec![false; armers.len()];
        for (ai, a) in armers.iter().enumerate() {
            anyhow::ensure!(a.alpha_limbs.len() == m.d_limbs, "alpha limbs mismatch");
            anyhow::ensure!(
                a.weights_row.len() == m.d_limbs,
                "weights_row limb mismatch"
            );
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

            // Option B bridge: dump LWE boundary sample for this limb/armer (before adding alpha).
            if let Some(dir) = emit_lwe_out_dir {
                fs::create_dir_all(dir).ok();
                let sample = extract_lwe_coeff0_from_ciphertext_tower(&ct_i, 0)?;
                let p = dir.join(format!("armer{}_limb{}.lwe0", a.armer_id, limb));
                sample.write_to_file(&p)?;
            }

            let pt_alpha =
                OpenFheBackend::make_packed_plaintext(&ctx, &vec![alpha as i64; m.slot_count])?;
            let ct_tag = OpenFheBackend::eval_add_plain(&ctx, &ct_i, &pt_alpha)?;

            let dec = decrypt_packed_with_len(&ctx, &sk, &ct_tag, m.slot_count)?;
            let t0 = *dec.get(0).unwrap_or(&0);
            let t_i64 = pt_mod as i64;
            let mut t0_mod = t0 % t_i64;
            if t0_mod < 0 {
                t0_mod += t_i64;
            }
            ok[ai] = t0_mod == (alpha as i64);
        }

        Ok(ok)
    };

    // Limbs are processed sequentially; parallelism is used inside the limb to split the basis work.
    let mut limb_ok: Vec<Vec<bool>> = Vec::with_capacity(m.d_limbs);
    for limb in 0..m.d_limbs {
        limb_ok.push(do_limb(limb)?);
    }

    let mut ok_all_limbs = vec![true; armers.len()];
    for limb in 0..m.d_limbs {
        for ai in 0..armers.len() {
            ok_all_limbs[ai] &= limb_ok[limb][ai];
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
