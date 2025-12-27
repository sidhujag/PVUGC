use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WeightsKind {
    Full,
    Binary01,
}

pub fn rotations_powers_of_two(slot_count: usize) -> Vec<i32> {
    let mut out = Vec::new();
    let mut k = 1i32;
    while (k as usize) < slot_count {
        out.push(k);
        k <<= 1;
    }
    out
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OpenFheManifestV0 {
    pub version: u32,
    pub scheme: String,
    pub multiplicative_depth: u32,
    pub serial_mode: String,
    pub limbs: Vec<OpenFheLimbFilesV0>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct OpenFheLimbFilesV0 {
    pub limb: usize,
    pub plaintext_modulus: u64,
    pub crypto_context_path: String,
    pub public_key_path: String,
    /// Dev-only fake gate.
    pub private_key_path: String,
    pub eval_mult_key_path: String,
    pub eval_rot_key_path: String,
}

/// Gate-bridge manifest (v0): parameters + path for the stream->gate LWE key switching key.
///
/// This is Option B2 plumbing: it does not define the gate construction; only the stable boundary.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct BridgeManifestV0 {
    pub version: u32,
    /// Which OpenFHE tower (RNS prime) we use when extracting the LWE sample.
    pub tower_index: u32,
    /// Output (gate) LWE dimension.
    pub gate_dim: usize,
    /// Keyswitch decomposition base log2 (B = 2^base_log).
    pub base_log: usize,
    /// Keyswitch decomposition level count.
    pub level_count: usize,
    /// Path to the serialized key-switch key (format TBD; intended to be TFHE-compatible bytes).
    pub ksk_path: String,
}

/// On-disk shape blob manifest (v0).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ShapeBlobManifestV0 {
    pub version: u32,
    pub shape_id: String,
    pub n_armers: usize,
    pub s_basis: usize,
    pub d_limbs: usize,
    pub moduli: Vec<u64>,
    pub epoch: u64,
    pub slot_count: usize,
    pub block_count: usize,
    pub blocks_per_chunk: usize,
    pub required_rotations: Vec<i32>,
    pub weights_kind: WeightsKind,
    /// If true, all limbs reuse the same basis ciphertext files (limb 0 paths).
    ///
    /// This is a blob-size optimization. Limb separation must then come from per-limb
    /// weights domain separation (or a different limb-derivation mechanism).
    #[serde(default)]
    pub basis_shared_across_limbs: bool,
    /// If true, derive weights with an explicit limb domain separator.
    ///
    /// This is required when `moduli` contains duplicates (e.g., 16 limbs all mod 65537),
    /// otherwise all limbs would use the same weights and become identical under a shared basis.
    #[serde(default)]
    pub weights_domain_sep_per_limb: bool,
    pub ciphertext_encoding_version: u32,
    #[serde(default)]
    pub openfhe: Option<OpenFheManifestV0>,
    /// Optional: stream->gate bridge config (Option B2).
    #[serde(default)]
    pub bridge: Option<BridgeManifestV0>,
}

impl ShapeBlobManifestV0 {
    /// File naming convention (v0): one ciphertext per file (blocks_per_chunk == 1).
    pub fn basis_chunk_rel_path(
        &self,
        limb: usize,
        j: usize,
        start_block: usize,
        end_block: usize,
    ) -> PathBuf {
        let limb = if self.basis_shared_across_limbs { 0 } else { limb };
        PathBuf::from(format!(
            "basis/l{limb}/j{j}/blocks_{start_block}_{end_block}.bin"
        ))
    }

    pub fn basis_chunk_path(
        &self,
        shape_blob_dir: &Path,
        limb: usize,
        j: usize,
        start_block: usize,
        end_block: usize,
    ) -> PathBuf {
        shape_blob_dir.join(self.basis_chunk_rel_path(limb, j, start_block, end_block))
    }
}
