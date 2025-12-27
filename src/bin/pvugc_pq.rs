use std::{fs, path::PathBuf};

use anyhow::{anyhow, Context, Result};
use clap::{Parser, Subcommand};
use rand_core::OsRng;
use rayon::prelude::*;
use sha2::{Digest, Sha256};

use arkworks_groth16::pq_we::{
    derive_weights_matrix_with_kind, rotations_powers_of_two, AlphaCrt, ArmerId, LockArtifactV0,
    LockId, ShapeBlobManifestV0, ShapeId, StatementHash32, TagCrt, WeightsKind,
};
use pq_stream_tag::ArmerInputV0;

// OpenFHE types are used only inside `pq-fhe-openfhe` / `pq-stream-tag` crates (GPT-Pro separation).

#[derive(Parser, Debug)]
#[command(author, version, about = "PVUGC PQ streaming (v0 skeleton, GPT-Pro aligned)")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand, Debug)]
enum Cmd {
    /// Create a v0 "shape blob manifest" (no OpenFHE yet; parameters only).
    SetupShape {
        /// Output directory (created if missing). Writes `manifest.json` inside it.
        #[arg(long)]
        out_dir: PathBuf,
        #[arg(long, default_value = "shrink_v1")]
        shape_id: String,
        /// Number of armers N.
        #[arg(long, default_value_t = 15)]
        n_armers: usize,
        /// Basis size s.
        #[arg(long, default_value_t = 16)]
        s_basis: usize,
        /// CRT limb count d.
        #[arg(long, default_value_t = 4)]
        d_limbs: usize,
        /// Plaintext moduli per limb (comma-separated u64). If omitted, uses 4 hardcoded 64-bit primes.
        #[arg(long)]
        moduli_csv: Option<String>,
        /// Epoch value to include in W(x) derivation (protocol-controlled; can be 0 for v0).
        #[arg(long, default_value_t = 0)]
        epoch: u64,

        /// Slot count B for batching (power-of-two recommended).
        #[arg(long, default_value_t = 8192)]
        slot_count: usize,

        /// Block count Bcnt (how many residual blocks the full scan emits).
        ///
        /// v0 placeholder: set to 0 if unknown; fill in once measured.
        #[arg(long, default_value_t = 0)]
        block_count: usize,

        /// Blocks per chunk file in the blob (chunk-addressing only; ciphertexts added later).
        #[arg(long, default_value_t = 1024)]
        blocks_per_chunk: usize,

        /// Prefer binary weights w∈{0,1} for CombineWeights (ciphertext adds only).
        #[arg(long, default_value_t = false)]
        binary_weights: bool,
    },

    /// Create a per-shape OpenFHE-backed blob (v0): keys + basis ciphertexts (ctK[j,b,ℓ]).
    ///
    /// This is the one-time heavy setup artifact (shape-CRS) reused across statements/armings.
    #[cfg(feature = "pq-openfhe")]
    SetupShapeOpenfhe {
        /// Output directory (created if missing). Writes `manifest.json` and OpenFHE artifacts inside it.
        #[arg(long)]
        out_dir: PathBuf,
        #[arg(long, default_value = "shrink_v1")]
        shape_id: String,
        /// Number of armers N.
        #[arg(long, default_value_t = 15)]
        n_armers: usize,
        /// Basis size s.
        #[arg(long, default_value_t = 16)]
        s_basis: usize,
        /// CRT limb count d.
        #[arg(long, default_value_t = 4)]
        d_limbs: usize,
        /// Plaintext moduli per limb (comma-separated u64). Must fit in i64 for OpenFHE packed encoding.
        ///
        /// If omitted, uses 4 hardcoded ~60-bit primes (fits i64).
        #[arg(long)]
        moduli_csv: Option<String>,
        /// Epoch value to include in W(x) derivation.
        #[arg(long, default_value_t = 0)]
        epoch: u64,
        /// Slot count B (packed length).
        #[arg(long, default_value_t = 8192)]
        slot_count: usize,
        /// Block count Bcnt (must match PVRS residual stream block count).
        #[arg(long)]
        block_count: usize,
        /// Blocks per chunk file.
        ///
        /// Stored as concatenated ciphertexts in `basis/l{limb}/j{j}/blocks_{start}_{end}.bin`.
        #[arg(long, default_value_t = 1)]
        blocks_per_chunk: usize,
        /// Prefer binary weights w∈{0,1} for CombineWeights (ciphertext adds only).
        #[arg(long, default_value_t = true)]
        binary_weights: bool,
        /// BFV multiplicative depth.
        #[arg(long, default_value_t = 2)]
        multiplicative_depth: u32,
        /// OpenFHE serialization mode: "BINARY" or "JSON".
        #[arg(long, default_value = "BINARY")]
        serial_mode: String,
        /// Parallelism for basis ciphertext generation across `j` during setup.
        ///
        /// Default 1 is safest. Increase cautiously; some OpenFHE builds can segfault under high
        /// concurrency.
        #[arg(long, default_value_t = 1)]
        basis_parallelism: usize,
    },

    /// Internal worker: generate OpenFHE basis ciphertexts for a limb and j-range.
    ///
    /// This is used by `setup-shape-openfhe` to do **multi-process** basis generation when
    /// `--basis-parallelism > 1`.
    #[cfg(feature = "pq-openfhe")]
    #[command(hide = true)]
    OpenfheBasisWorker {
        #[arg(long)]
        shape_blob_dir: PathBuf,
        #[arg(long)]
        limb: usize,
        #[arg(long)]
        j_start: usize,
        #[arg(long)]
        j_end: usize,
    },

    /// Arm a statement for one armer (v0: stores alpha + sigma in clear for correctness testing).
    Arm {
        #[arg(long)]
        shape_manifest: PathBuf,
        #[arg(long)]
        out: PathBuf,
        /// Statement hash hex (32 bytes) from SP1 `derive_shrink_statement` (statement_hash).
        #[arg(long)]
        statement_hash_hex: Option<String>,
        /// Alternatively, path to SP1 `derive_shrink_statement` stdout (we parse `statement_hash:`).
        #[arg(long)]
        statement_from_sp1_out: Option<PathBuf>,
        /// Armer index i.
        #[arg(long)]
        armer_id: u32,
        /// Epoch (must match setup/consumers).
        #[arg(long, default_value_t = 0)]
        epoch: u64,
    },

    /// Convenience helper: generate many armer artifacts into a directory.
    ///
    /// This simulates the production situation where each armer runs `arm` independently, while
    /// letting us quickly produce a batch for testing `decap-openfhe --armer-artifact ...` with
    /// many armers.
    ArmMany {
        #[arg(long)]
        shape_manifest: PathBuf,
        /// Output directory (created if missing). Writes `armer_<id>.json` files inside.
        #[arg(long)]
        out_dir: PathBuf,
        /// Statement hash hex (32 bytes) from SP1 `derive_shrink_statement` (statement_hash).
        #[arg(long)]
        statement_hash_hex: Option<String>,
        /// Alternatively, path to SP1 `derive_shrink_statement` stdout (we parse `statement_hash:`).
        #[arg(long)]
        statement_from_sp1_out: Option<PathBuf>,
        /// Starting armer id (inclusive).
        #[arg(long, default_value_t = 0)]
        armer_id_start: u32,
        /// Ending armer id (exclusive).
        #[arg(long)]
        armer_id_end: u32,
        /// Epoch (must match manifest).
        #[arg(long, default_value_t = 0)]
        epoch: u64,
    },

    /// Decap (v0): compare tag limbs against alpha limbs and release sigma_i on match.
    Decap {
        #[arg(long)]
        armer_artifact: PathBuf,
        /// Tag limbs in hex, one per limb (repeat flag d times). Must be 16-hex-digit chunks.
        ///
        /// Matches SP1 printing: `tag.tag_256 (4x64 mod primes): <l0> <l1> <l2> <l3>`.
        #[arg(long, num_args = 1..)]
        tag_limb_hex: Vec<String>,
        /// Alternatively, path to SP1 `shrink_tag` stdout (we parse the printed tag limb line).
        #[arg(long)]
        tag_from_sp1_out: Option<PathBuf>,
    },

    /// Decap using OpenFHE (v0 fake gate): stream PVRS, evaluate tag under BFV, decrypt+compare.
    #[cfg(feature = "pq-openfhe")]
    DecapOpenfhe {
        /// Shape blob directory (contains `manifest.json`, OpenFHE artifacts, and basis ciphertexts).
        #[arg(long)]
        shape_blob_dir: PathBuf,
        /// PVRS residual stream file path (from `sp1-prover shrink_residual_stream`).
        #[arg(long)]
        residual_file: PathBuf,
        /// Armer artifacts (repeat). v0: uses alpha_clear + sigma_i_clear from these artifacts.
        #[arg(long, num_args = 1..)]
        armer_artifact: Vec<PathBuf>,
        /// Alternatively, load *all* `*.json` armer artifacts from a directory (non-recursive).
        /// This avoids shell loops when decapping against many armers.
        #[arg(long)]
        armer_artifact_dir: Option<PathBuf>,
        /// Parallelize the **basis accumulation** across basis index `j` (this is the dominant ct×pt work).
        #[arg(long, default_value_t = 1)]
        basis_parallelism: usize,
    },

    /// Print the deterministic weights row w_i(x) implied by the shape manifest and statement hash.
    ///
    /// This is a debugging/repro tool to validate CombineWeights later (OpenFHE integration) without
    /// changing any artifact formats.
    WeightsRow {
        #[arg(long)]
        shape_manifest: PathBuf,
        /// Statement hash hex (32 bytes) from SP1 `derive_shrink_statement` (statement_hash).
        #[arg(long)]
        statement_hash_hex: Option<String>,
        /// Alternatively, path to SP1 `derive_shrink_statement` stdout (we parse `statement_hash:`).
        #[arg(long)]
        statement_from_sp1_out: Option<PathBuf>,
        /// Armer index i.
        #[arg(long)]
        armer_id: u32,
        /// Epoch (must match manifest).
        #[arg(long, default_value_t = 0)]
        epoch: u64,
        /// Print JSON instead of human-readable text.
        #[arg(long, default_value_t = false)]
        json: bool,
    },

    /// Inspect a PVRS(v0) residual stream file produced by SP1 and optionally sanity-check
    /// it against a shape manifest.
    ResidualInfo {
        /// PVRS file path (from `sp1-prover shrink_residual_stream --out ...`).
        #[arg(long)]
        residual_file: PathBuf,
        /// Optional shape manifest to check slot_count/block_count/shape_id hash expectations.
        #[arg(long)]
        shape_manifest: Option<PathBuf>,
    },

    /// Convenience helper: create a corrupted copy of a PVRS v0 file (flip one u32 residual).
    ///
    /// Used to sanity-check that `decap-openfhe` fails (UNLOCK=NO) on invalid streams.
    CorruptPvrsOne {
        /// Input PVRS file path.
        #[arg(long)]
        in_pvrs: PathBuf,
        /// Output PVRS file path (written).
        #[arg(long)]
        out_pvrs: PathBuf,
        /// Which block index to corrupt (0-based, after the 92-byte header).
        #[arg(long, default_value_t = 0)]
        block_idx: u64,
        /// Which slot within the block to corrupt (0-based).
        #[arg(long, default_value_t = 0)]
        slot_idx: u32,
        /// XOR mask applied to the chosen u32.
        #[arg(long, default_value_t = 1)]
        xor_mask: u32,
    },

    /// End-to-end demo: real BFV evaluation over SP1 PVRS residual stream + fake gate (decrypt+compare).
    ///
    /// This is the fastest way to validate the GPT-Pro streaming loop with a real HE backend,
    /// before building the huge reusable per-shape basis blob.
    #[cfg(feature = "pq-openfhe")]
    DemoOpenfhe {
        /// PVRS file path produced by `sp1-prover shrink_residual_stream`.
        #[arg(long)]
        residual_file: PathBuf,
        /// Slot count B (must match PVRS header).
        #[arg(long)]
        slot_count: u32,
        /// BFV plaintext modulus t (must fit in i64; recommend a 50–60 bit prime).
        #[arg(long)]
        plaintext_modulus: u64,
        /// Multiplicative depth (small; we only need ct×pt + adds + rotations).
        #[arg(long, default_value_t = 2)]
        multiplicative_depth: u32,
        /// If set, also print the decrypted tag value (slot 0) and alpha used.
        #[arg(long, default_value_t = false)]
        verbose: bool,
    },
}

#[derive(serde::Serialize, serde::Deserialize, Debug, Clone)]
struct ArmerArtifactV0 {
    version: u32,
    lock: LockArtifactV0,

    /// Published commitment to sigma (as GPT Pro: c_i = H(σ_i)).
    c_i_sha256: [u8; 32],

    /// v0 ONLY: sigma_i in clear.
    sigma_i_clear: [u8; 32],

    /// Derived weights row per limb modulus (for debugging / reproducibility).
    /// Stored as vec[d][s].
    weights_row: Vec<Vec<u64>>,

    /// Weight generation kind used.
    weights_kind: WeightsKind,
}

#[derive(serde::Serialize, Debug, Clone)]
struct WeightsRowOutV0 {
    version: u32,
    shape_id: String,
    statement_hash_hex: String,
    armer_id: u32,
    epoch: u64,
    weights_kind: WeightsKind,
    moduli: Vec<u64>,
    /// Stored as vec[d][s].
    weights_row: Vec<Vec<u64>>,
}

fn parse_hex_32(name: &str, s: &str) -> Result<[u8; 32]> {
    let b = hex::decode(s.trim()).with_context(|| format!("decode {name}"))?;
    anyhow::ensure!(b.len() == 32, "{name} must be 32 bytes (64 hex chars)");
    let mut out = [0u8; 32];
    out.copy_from_slice(&b);
    Ok(out)
}

fn parse_csv_u64(s: &str) -> Result<Vec<u64>> {
    let mut out = Vec::new();
    for part in s.split(',').map(|x| x.trim()).filter(|x| !x.is_empty()) {
        out.push(part.parse::<u64>().with_context(|| format!("parse u64 '{part}'"))?);
    }
    Ok(out)
}

fn default_moduli_4() -> Vec<u64> {
    vec![
        18446744069414584321,
        18446744073709551557,
        18446744073709551533,
        18446744073709551521,
    ]
}

#[cfg(feature = "pq-openfhe")]
fn default_moduli_4_openfhe_i64() -> Vec<u64> {
    // 4 ~60-bit primes that fit in i64 (OpenFHE packed i64 API).
    // (We still reduce all values mod p in code, so primality is the only property we really need here.)
    vec![
        1152921504606847009, // 2^60 + 33 (prime)
        1152921504606846883, // 2^60 - 93 (prime)
        1152921504606846719, // 2^60 - 257 (prime)
        1152921504606846621, // 2^60 - 355 (prime)
    ]
}

// OpenFHE serialization mode parsing is handled inside `pq-fhe-openfhe` / `pq-stream-tag`.

fn parse_hex_u64_fixed(name: &str, s: &str) -> Result<u64> {
    let t = s.trim();
    anyhow::ensure!(
        t.len() == 16 && t.chars().all(|c| c.is_ascii_hexdigit()),
        "{name} must be 16 hex chars (u64 limb), got '{t}'"
    );
    Ok(u64::from_str_radix(t, 16).with_context(|| format!("parse {name}"))?)
}

fn read_text(path: &PathBuf) -> Result<String> {
    let b = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    Ok(String::from_utf8_lossy(&b).to_string())
}

#[derive(Debug, Clone)]
struct PvrsHeaderV0 {
    slot_count: u32,
    block_count: u64,
    residuals_emitted: u64,
    statement_hash: [u8; 32],
    shape_id_hash: [u8; 32],
}

fn parse_pvrs_header_v0(path: &PathBuf) -> Result<PvrsHeaderV0> {
    let b = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    anyhow::ensure!(b.len() >= 92, "PVRS file too small (need >= 92 bytes)");
    anyhow::ensure!(&b[0..4] == b"PVRS", "bad PVRS magic");
    let version = u32::from_le_bytes(b[4..8].try_into().unwrap());
    anyhow::ensure!(version == 0, "unsupported PVRS version {}", version);
    let slot_count = u32::from_le_bytes(b[8..12].try_into().unwrap());
    let block_count = u64::from_le_bytes(b[12..20].try_into().unwrap());
    let residuals_emitted = u64::from_le_bytes(b[20..28].try_into().unwrap());
    let mut statement_hash = [0u8; 32];
    statement_hash.copy_from_slice(&b[28..60]);
    let mut shape_id_hash = [0u8; 32];
    shape_id_hash.copy_from_slice(&b[60..92]);
    Ok(PvrsHeaderV0 { slot_count, block_count, residuals_emitted, statement_hash, shape_id_hash })
}

fn sha256_32(data: &[u8]) -> [u8; 32] {
    let d = Sha256::digest(data);
    let mut out = [0u8; 32];
    out.copy_from_slice(&d);
    out
}

#[cfg(feature = "pq-openfhe")]
fn coeff_u64_for_demo(statement_hash: &[u8; 32], block_idx: u64, slot_idx: u32, modulus: u64) -> u64 {
    // Deterministic per-(statement, block, slot) coefficient. Security isn't the goal here;
    // we just want a large-domain dot-product fingerprint.
    let mut h = Sha256::new();
    h.update(b"pvugc.openfhe.demo.coeff.v0");
    h.update(statement_hash);
    h.update(&block_idx.to_le_bytes());
    h.update(&slot_idx.to_le_bytes());
    let d = h.finalize();
    let mut w = [0u8; 8];
    w.copy_from_slice(&d[..8]);
    u64::from_le_bytes(w) % modulus
}

fn parse_statement_hash_from_sp1_out(text: &str) -> Result<[u8; 32]> {
    // Expect a line: "statement_hash: <64 hex>"
    for line in text.lines() {
        let l = line.trim();
        if let Some(rest) = l.strip_prefix("statement_hash:") {
            return parse_hex_32("statement_hash", rest.trim());
        }
    }
    Err(anyhow!("could not find `statement_hash:` line in SP1 output"))
}

fn parse_tag_limbs_from_sp1_out(text: &str) -> Result<Vec<String>> {
    // Expect a line:
    // "tag.tag_256 (4x64 mod primes): <l0> <l1> <l2> <l3>"
    for line in text.lines() {
        let l = line.trim();
        if let Some(rest) = l.strip_prefix("tag.tag_256 (4x64 mod primes):") {
            let toks: Vec<&str> = rest.split_whitespace().collect();
            if toks.len() >= 4 {
                return Ok(toks[toks.len() - 4..].iter().map(|s| s.to_string()).collect());
            }
        }
    }
    Err(anyhow!("could not find `tag.tag_256 (4x64 mod primes):` line in SP1 output"))
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.cmd {
        Cmd::SetupShape {
            out_dir,
            shape_id,
            n_armers,
            s_basis,
            d_limbs,
            moduli_csv,
            epoch,
            slot_count,
            block_count,
            blocks_per_chunk,
            binary_weights,
        } => {
            let moduli = if let Some(csv) = moduli_csv {
                parse_csv_u64(&csv)?
            } else {
                default_moduli_4()
            };
            anyhow::ensure!(moduli.len() == d_limbs, "moduli.len must equal d_limbs");

            let m = ShapeBlobManifestV0 {
                version: 0,
                shape_id,
                n_armers,
                s_basis,
                d_limbs,
                moduli,
                epoch,
                slot_count,
                block_count,
                blocks_per_chunk,
                required_rotations: rotations_powers_of_two(slot_count),
                weights_kind: if binary_weights { WeightsKind::Binary01 } else { WeightsKind::Full },
                ciphertext_encoding_version: 0,
                openfhe: None,
            };
            fs::create_dir_all(&out_dir).with_context(|| format!("create {}", out_dir.display()))?;
            // Create placeholder basis directory structure (future ciphertext chunks live here).
            fs::create_dir_all(out_dir.join("basis")).ok();
            for l in 0..m.d_limbs {
                for j in 0..m.s_basis {
                    let p = out_dir.join(format!("basis/l{l}/j{j}"));
                    fs::create_dir_all(&p).ok();
                }
            }
            let manifest_path = out_dir.join("manifest.json");
            let bytes = serde_json::to_vec_pretty(&m).context("serialize manifest")?;
            fs::write(&manifest_path, bytes).with_context(|| format!("write {}", manifest_path.display()))?;
            println!("wrote {}", manifest_path.display());
        }

        Cmd::Arm { shape_manifest, out, statement_hash_hex, statement_from_sp1_out, armer_id, epoch } => {
            let manifest_bytes =
                fs::read(&shape_manifest).with_context(|| format!("read {}", shape_manifest.display()))?;
            let m: ShapeBlobManifestV0 =
                serde_json::from_slice(&manifest_bytes).context("parse shape manifest")?;
            anyhow::ensure!(m.version == 0, "unsupported manifest version {}", m.version);
            anyhow::ensure!(m.epoch == epoch, "epoch mismatch (manifest {}, arg {})", m.epoch, epoch);

            let sh = if let Some(hex) = statement_hash_hex.as_deref() {
                parse_hex_32("--statement-hash-hex", hex)?
            } else if let Some(p) = statement_from_sp1_out.as_ref() {
                let t = read_text(p)?;
                parse_statement_hash_from_sp1_out(&t)?
            } else {
                return Err(anyhow!("need either --statement-hash-hex or --statement-from-sp1-out"));
            };
            let statement_hash = StatementHash32(sh);

            // Derive W(x) row for each limb modulus; store only this armer's row i.
            let mut weights_row: Vec<Vec<u64>> = Vec::with_capacity(m.d_limbs);
            for &p in &m.moduli {
                let wm = derive_weights_matrix_with_kind(
                    b"pvugc.weights.v0",
                    &ShapeId(m.shape_id.clone()),
                    &statement_hash,
                    epoch,
                    m.n_armers,
                    m.s_basis,
                    p,
                    m.weights_kind,
                )?;
                let i = armer_id as usize;
                anyhow::ensure!(i < wm.n_armers, "armer_id out of range");
                let mut row = Vec::with_capacity(wm.s_basis);
                for j in 0..wm.s_basis {
                    row.push(wm.get(i, j));
                }
                weights_row.push(row);
            }

            // v0: generate fresh sigma_i and alpha_i in clear (dev only).
            let mut sigma_i_clear = [0u8; 32];
            rand_core::RngCore::fill_bytes(&mut OsRng, &mut sigma_i_clear);
            let mut hasher = Sha256::new();
            hasher.update(&sigma_i_clear);
            let c_i: [u8; 32] = hasher.finalize().into();

            // alpha limbs: sample from OS randomness and reduce mod p (dev only).
            let mut alpha_limbs = Vec::with_capacity(m.d_limbs);
            for &p in &m.moduli {
                let r = rand_core::RngCore::next_u64(&mut OsRng) % p;
                alpha_limbs.push(r);
            }

            let lock = LockArtifactV0 {
                lock_id: LockId(format!("lock_v0:{}:{}:{}", m.shape_id, hex::encode(sh), armer_id)),
                shape_id: ShapeId(m.shape_id.clone()),
                armer_id: ArmerId(armer_id),
                statement_hash,
                moduli: m.moduli.clone(),
                alpha_clear: Some(AlphaCrt { moduli: m.moduli.clone(), limbs: alpha_limbs.clone() }),
            };

            let artifact = ArmerArtifactV0 {
                version: 0,
                lock,
                c_i_sha256: c_i,
                sigma_i_clear,
                weights_row,
                weights_kind: m.weights_kind,
            };

            let bytes = serde_json::to_vec_pretty(&artifact).context("serialize armer artifact")?;
            fs::write(&out, bytes).with_context(|| format!("write {}", out.display()))?;
            println!("wrote {}", out.display());
            println!(
                "alpha_limbs_hex ({}x64): {}",
                m.d_limbs,
                alpha_limbs
                    .iter()
                    .map(|x| format!("{:016x}", x))
                    .collect::<Vec<_>>()
                    .join(" ")
            );
            println!("c_i_sha256: {}", hex::encode(c_i));
        }

        Cmd::ArmMany {
            shape_manifest,
            out_dir,
            statement_hash_hex,
            statement_from_sp1_out,
            armer_id_start,
            armer_id_end,
            epoch,
        } => {
            anyhow::ensure!(armer_id_end > armer_id_start, "need armer_id_end > armer_id_start");

            let manifest_bytes =
                fs::read(&shape_manifest).with_context(|| format!("read {}", shape_manifest.display()))?;
            let m: ShapeBlobManifestV0 =
                serde_json::from_slice(&manifest_bytes).context("parse shape manifest")?;
            anyhow::ensure!(m.version == 0, "unsupported manifest version {}", m.version);
            anyhow::ensure!(m.epoch == epoch, "epoch mismatch (manifest {}, arg {})", m.epoch, epoch);

            let sh = if let Some(hex) = statement_hash_hex.as_deref() {
                parse_hex_32("--statement-hash-hex", hex)?
            } else if let Some(p) = statement_from_sp1_out.as_ref() {
                let t = read_text(p)?;
                parse_statement_hash_from_sp1_out(&t)?
            } else {
                return Err(anyhow!("need either --statement-hash-hex or --statement-from-sp1-out"));
            };
            let statement_hash = StatementHash32(sh);

            fs::create_dir_all(&out_dir).with_context(|| format!("create {}", out_dir.display()))?;

            // Parallelize across armer_id (independent output files).
            // Note: derive_weights_matrix_with_kind is deterministic and pure; safe to call in parallel.
            (armer_id_start..armer_id_end)
                .into_par_iter()
                .try_for_each(|armer_id| -> Result<()> {
                    let out = out_dir.join(format!("armer_{armer_id}.json"));

                    let mut weights_row: Vec<Vec<u64>> = Vec::with_capacity(m.d_limbs);
                    for &p in &m.moduli {
                        let wm = derive_weights_matrix_with_kind(
                            b"pvugc.weights.v0",
                            &ShapeId(m.shape_id.clone()),
                            &statement_hash,
                            epoch,
                            m.n_armers,
                            m.s_basis,
                            p,
                            m.weights_kind,
                        )?;
                        let i = armer_id as usize;
                        anyhow::ensure!(i < wm.n_armers, "armer_id out of range");
                        let mut row = Vec::with_capacity(wm.s_basis);
                        for j in 0..wm.s_basis {
                            row.push(wm.get(i, j));
                        }
                        weights_row.push(row);
                    }

                    // Thread-local randomness (dev v0).
                    let mut rng = OsRng;
                    let mut sigma_i_clear = [0u8; 32];
                    rand_core::RngCore::fill_bytes(&mut rng, &mut sigma_i_clear);
                    let mut hasher = Sha256::new();
                    hasher.update(&sigma_i_clear);
                    let c_i: [u8; 32] = hasher.finalize().into();

                    let mut alpha_limbs = Vec::with_capacity(m.d_limbs);
                    for &p in &m.moduli {
                        let r = rand_core::RngCore::next_u64(&mut rng) % p;
                        alpha_limbs.push(r);
                    }

                    let lock = LockArtifactV0 {
                        lock_id: LockId(format!(
                            "lock_v0:{}:{}:{}",
                            m.shape_id,
                            hex::encode(sh),
                            armer_id
                        )),
                        shape_id: ShapeId(m.shape_id.clone()),
                        armer_id: ArmerId(armer_id),
                        statement_hash: StatementHash32(sh),
                        moduli: m.moduli.clone(),
                        alpha_clear: Some(AlphaCrt { moduli: m.moduli.clone(), limbs: alpha_limbs }),
                    };

                    let artifact = ArmerArtifactV0 {
                        version: 0,
                        lock,
                        c_i_sha256: c_i,
                        sigma_i_clear,
                        weights_row,
                        weights_kind: m.weights_kind,
                    };

                    let bytes = serde_json::to_vec_pretty(&artifact).context("serialize armer artifact")?;
                    fs::write(&out, bytes).with_context(|| format!("write {}", out.display()))?;
                    Ok(())
                })?;

            for armer_id in armer_id_start..armer_id_end {
                println!("wrote {}", out_dir.join(format!("armer_{armer_id}.json")).display());
            }
        }

        Cmd::Decap { armer_artifact, tag_limb_hex, tag_from_sp1_out } => {
            let art_bytes =
                fs::read(&armer_artifact).with_context(|| format!("read {}", armer_artifact.display()))?;
            let a: ArmerArtifactV0 = serde_json::from_slice(&art_bytes).context("parse armer artifact")?;
            anyhow::ensure!(a.version == 0, "unsupported armer artifact version {}", a.version);

            let moduli = a.lock.moduli.clone();
            let tag_limb_hex = if let Some(p) = tag_from_sp1_out.as_ref() {
                let t = read_text(p)?;
                parse_tag_limbs_from_sp1_out(&t)?
            } else {
                tag_limb_hex
            };
            anyhow::ensure!(tag_limb_hex.len() == moduli.len(), "need exactly d={} tag limbs", moduli.len());
            let mut limbs = Vec::with_capacity(moduli.len());
            for (i, s) in tag_limb_hex.iter().enumerate() {
                let v = parse_hex_u64_fixed("--tag-limb-hex", s)?;
                limbs.push(v % moduli[i]);
            }

            let tag = TagCrt { moduli: moduli.clone(), limbs: limbs.clone() };
            let alpha = a
                .lock
                .alpha_clear
                .clone()
                .ok_or_else(|| anyhow!("artifact missing alpha_clear (not v0)"))?;
            anyhow::ensure!(alpha.moduli == tag.moduli, "alpha/tag moduli mismatch");

            if tag.limbs == alpha.limbs {
                println!("UNLOCK=YES");
                println!("sigma_i_hex={}", hex::encode(a.sigma_i_clear));
                // Sanity: print c_i
                println!("c_i_sha256={}", hex::encode(a.c_i_sha256));
            } else {
                println!("UNLOCK=NO");
            }
        }

        Cmd::WeightsRow {
            shape_manifest,
            statement_hash_hex,
            statement_from_sp1_out,
            armer_id,
            epoch,
            json,
        } => {
            let manifest_bytes =
                fs::read(&shape_manifest).with_context(|| format!("read {}", shape_manifest.display()))?;
            let m: ShapeBlobManifestV0 =
                serde_json::from_slice(&manifest_bytes).context("parse shape manifest")?;
            anyhow::ensure!(m.version == 0, "unsupported manifest version {}", m.version);
            anyhow::ensure!(m.epoch == epoch, "epoch mismatch (manifest {}, arg {})", m.epoch, epoch);

            let sh = if let Some(hex) = statement_hash_hex.as_deref() {
                parse_hex_32("--statement-hash-hex", hex)?
            } else if let Some(p) = statement_from_sp1_out.as_ref() {
                let t = read_text(p)?;
                parse_statement_hash_from_sp1_out(&t)?
            } else {
                return Err(anyhow!("need either --statement-hash-hex or --statement-from-sp1-out"));
            };
            let statement_hash = StatementHash32(sh);

            let mut weights_row: Vec<Vec<u64>> = Vec::with_capacity(m.d_limbs);
            for &p in &m.moduli {
                let wm = derive_weights_matrix_with_kind(
                    b"pvugc.weights.v0",
                    &ShapeId(m.shape_id.clone()),
                    &statement_hash,
                    epoch,
                    m.n_armers,
                    m.s_basis,
                    p,
                    m.weights_kind,
                )?;
                let i = armer_id as usize;
                anyhow::ensure!(i < wm.n_armers, "armer_id out of range");
                let mut row = Vec::with_capacity(wm.s_basis);
                for j in 0..wm.s_basis {
                    row.push(wm.get(i, j));
                }
                weights_row.push(row);
            }

            if json {
                let out = WeightsRowOutV0 {
                    version: 0,
                    shape_id: m.shape_id.clone(),
                    statement_hash_hex: hex::encode(sh),
                    armer_id,
                    epoch,
                    weights_kind: m.weights_kind,
                    moduli: m.moduli.clone(),
                    weights_row,
                };
                let bytes = serde_json::to_vec_pretty(&out).context("serialize weights-row json")?;
                println!("{}", String::from_utf8_lossy(&bytes));
            } else {
                println!("shape_id: {}", m.shape_id);
                println!("statement_hash_hex: {}", hex::encode(sh));
                println!("armer_id: {}", armer_id);
                println!("epoch: {}", epoch);
                println!("weights_kind: {:?}", m.weights_kind);
                for (l, (p, row)) in m.moduli.iter().zip(weights_row.iter()).enumerate() {
                    let row_hex = row.iter().map(|x| format!("{:016x}", x)).collect::<Vec<_>>().join(" ");
                    println!("w_row_l{l} (p={}): {}", p, row_hex);
                }
            }
        }

        Cmd::ResidualInfo { residual_file, shape_manifest } => {
            let h = parse_pvrs_header_v0(&residual_file)?;
            println!("pvrs.slot_count: {}", h.slot_count);
            println!("pvrs.block_count: {}", h.block_count);
            println!("pvrs.residuals_emitted: {}", h.residuals_emitted);
            println!("pvrs.statement_hash: {}", hex::encode(h.statement_hash));
            println!("pvrs.shape_id_hash: {}", hex::encode(h.shape_id_hash));

            if let Some(manifest_path) = shape_manifest.as_ref() {
                let mb = fs::read(manifest_path).with_context(|| format!("read {}", manifest_path.display()))?;
                let m: ShapeBlobManifestV0 = serde_json::from_slice(&mb).context("parse shape manifest")?;
                anyhow::ensure!(m.version == 0, "unsupported manifest version {}", m.version);
                let expect_shape_hash = sha256_32(m.shape_id.as_bytes());

                anyhow::ensure!(
                    h.slot_count as usize == m.slot_count,
                    "slot_count mismatch: pvrs {} vs manifest {}",
                    h.slot_count,
                    m.slot_count
                );
                anyhow::ensure!(
                    h.shape_id_hash == expect_shape_hash,
                    "shape_id hash mismatch: pvrs {} vs sha256(manifest.shape_id) {}",
                    hex::encode(h.shape_id_hash),
                    hex::encode(expect_shape_hash)
                );

                if m.block_count != 0 {
                    anyhow::ensure!(
                        h.block_count as usize == m.block_count,
                        "block_count mismatch: pvrs {} vs manifest {}",
                        h.block_count,
                        m.block_count
                    );
                }
                println!("pvrs.manifest_check: OK");
            }
        }

        Cmd::CorruptPvrsOne { in_pvrs, out_pvrs, block_idx, slot_idx, xor_mask } => {
            let mut b = fs::read(&in_pvrs).with_context(|| format!("read {}", in_pvrs.display()))?;
            anyhow::ensure!(b.len() >= 92, "PVRS file too small (need >= 92 bytes)");
            anyhow::ensure!(&b[0..4] == b"PVRS", "bad PVRS magic");
            let version = u32::from_le_bytes(b[4..8].try_into().unwrap());
            anyhow::ensure!(version == 0, "unsupported PVRS version {}", version);
            let slot_count = u32::from_le_bytes(b[8..12].try_into().unwrap());
            let block_count = u64::from_le_bytes(b[12..20].try_into().unwrap());
            anyhow::ensure!(slot_idx < slot_count, "slot_idx out of range (slot_count={slot_count})");
            anyhow::ensure!(block_idx < block_count, "block_idx out of range (block_count={block_count})");

            let header = 92usize;
            let block_bytes = (slot_count as usize) * 4;
            let off = header + (block_idx as usize) * block_bytes + (slot_idx as usize) * 4;
            anyhow::ensure!(off + 4 <= b.len(), "corruption offset out of bounds");
            let mut w = u32::from_le_bytes(b[off..off + 4].try_into().unwrap());
            w ^= xor_mask;
            b[off..off + 4].copy_from_slice(&w.to_le_bytes());

            fs::write(&out_pvrs, b).with_context(|| format!("write {}", out_pvrs.display()))?;
            println!(
                "wrote {} (corrupted block_idx={}, slot_idx={}, xor_mask=0x{:08x})",
                out_pvrs.display(),
                block_idx,
                slot_idx,
                xor_mask
            );
        }

        #[cfg(feature = "pq-openfhe")]
        Cmd::DemoOpenfhe { .. } => {
            anyhow::bail!("demo-openfhe removed: use setup-shape-openfhe + decap-openfhe (GPT-Pro separation)");
        }

        #[cfg(feature = "pq-openfhe")]
        Cmd::SetupShapeOpenfhe {
            out_dir,
            shape_id,
            n_armers,
            s_basis,
            d_limbs,
            moduli_csv,
            epoch,
            slot_count,
            block_count,
            blocks_per_chunk,
            binary_weights,
            multiplicative_depth,
            serial_mode,
            basis_parallelism,
        } => {
            let moduli = if let Some(csv) = moduli_csv {
                parse_csv_u64(&csv)?
            } else {
                default_moduli_4_openfhe_i64()
            };
            anyhow::ensure!(moduli.len() == d_limbs, "moduli.len must equal d_limbs");
            for (i, &m) in moduli.iter().enumerate() {
                anyhow::ensure!(m > 2, "moduli[{i}] must be > 2");
                anyhow::ensure!(
                    m <= (i64::MAX as u64),
                    "moduli[{i}] too large for OpenFHE packed i64 API (need <= i64::MAX)"
                );
            }
            let args = pq_fhe_openfhe::SetupShapeBlobArgs {
                out_dir: out_dir.clone(),
                shape_id,
                n_armers,
                s_basis,
                d_limbs,
                moduli,
                epoch,
                slot_count,
                block_count,
                blocks_per_chunk,
                weights_kind: if binary_weights { WeightsKind::Binary01 } else { WeightsKind::Full },
                multiplicative_depth,
                serial_mode,
                basis_parallelism,
            };

            if basis_parallelism <= 1 {
                // Single-process (sequential) setup.
                pq_fhe_openfhe::setup_shape_blob_openfhe(args)?;
            } else {
                // Multi-process basis generation (reliable; avoids OpenFHE thread-safety issues).
                pq_fhe_openfhe::setup_shape_blob_openfhe_keys_only(&args)?;

                let exe = std::env::current_exe().context("current_exe for OpenFHE basis workers")?;
                for limb in 0..d_limbs {
                    let workers = basis_parallelism.min(s_basis).max(1);
                    let chunk = (s_basis + workers - 1) / workers;
                    let mut children = Vec::new();

                    for w in 0..workers {
                        let j_start = w * chunk;
                        let j_end = ((w + 1) * chunk).min(s_basis);
                        if j_start >= j_end {
                            continue;
                        }

                        let mut cmd = std::process::Command::new(&exe);
                        cmd.arg("openfhe-basis-worker")
                            .arg("--shape-blob-dir")
                            .arg(out_dir.as_os_str())
                            .arg("--limb")
                            .arg(limb.to_string())
                            .arg("--j-start")
                            .arg(j_start.to_string())
                            .arg("--j-end")
                            .arg(j_end.to_string());
                        cmd.stdout(std::process::Stdio::inherit());
                        cmd.stderr(std::process::Stdio::inherit());
                        children.push(cmd.spawn().context("spawn openfhe-basis-worker")?);
                    }

                    for mut c in children {
                        let st = c.wait().context("wait openfhe-basis-worker")?;
                        anyhow::ensure!(st.success(), "openfhe-basis-worker failed with status {st}");
                    }
                }
            }
        }

        #[cfg(feature = "pq-openfhe")]
        Cmd::OpenfheBasisWorker { shape_blob_dir, limb, j_start, j_end } => {
            pq_fhe_openfhe::openfhe_generate_basis_worker(&shape_blob_dir, limb, j_start, j_end)?;
        }

        #[cfg(feature = "pq-openfhe")]
        Cmd::DecapOpenfhe {
            shape_blob_dir,
            residual_file,
            armer_artifact,
            armer_artifact_dir,
            basis_parallelism,
        } => {
            // Load armer artifacts and convert to `pq_stream_tag` inputs (demo trust v0).
            let mut paths = armer_artifact.clone();
            if let Some(dir) = armer_artifact_dir.as_ref() {
                let mut extra = fs::read_dir(dir)
                    .with_context(|| format!("read_dir {}", dir.display()))?
                    .filter_map(|e| e.ok())
                    .map(|e| e.path())
                    .filter(|p| p.extension().map(|x| x == "json").unwrap_or(false))
                    .collect::<Vec<_>>();
                extra.sort();
                paths.extend(extra);
            }
            anyhow::ensure!(!paths.is_empty(), "need at least one armer artifact (paths empty)");

            let mut armers_in: Vec<ArmerInputV0> = Vec::new();
            for p in &paths {
                let b = fs::read(p).with_context(|| format!("read {}", p.display()))?;
                let a: ArmerArtifactV0 = serde_json::from_slice(&b).context("parse armer artifact")?;
                let alpha = a
                    .lock
                    .alpha_clear
                    .as_ref()
                    .ok_or_else(|| anyhow!("armer artifact missing alpha_clear (not v0)"))?
                    .limbs
                    .clone();
                armers_in.push(ArmerInputV0 {
                    armer_id: a.lock.armer_id.0,
                    statement_hash: a.lock.statement_hash.0,
                    alpha_limbs: alpha,
                    sigma_i_clear: a.sigma_i_clear,
                    c_i_sha256: a.c_i_sha256,
                    weights_row: a.weights_row,
                });
            }

            pq_stream_tag::decap_openfhe_with_basis_parallelism(
                &shape_blob_dir,
                &residual_file,
                &armers_in,
                basis_parallelism,
            )?;
        }
    }

    Ok(())
}


