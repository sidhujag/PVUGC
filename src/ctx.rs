//! Context Binding for PVUGC (Spec §3: Layered Context Hashing)
//!
//! Implements complete context binding architecture with:
//! - Layered hashes (ctx_core, arming_pkg_hash, presig_pkg_hash)
//! - epoch_nonce for instance uniqueness
//! - NUMS key derivation setup
//! - Domain-separated hash tags per BIP-340 style
//!
//! This ensures all protocol components (statement, transaction, arming, signing)
//! are cryptographically bound together, preventing:
//! - Transaction substitution attacks
//! - Cross-path exploitation
//! - Replay across instances

use sha2::{Digest, Sha256};

/// Layered context binding per PVUGC spec §3
///
/// Architecture:
/// ```text
/// y_cols_digest = H_bytes("PVUGC/YCOLS" || ser(B_pub(vk,x)) || ser(b_g2_query[witness-only]))
/// epoch_nonce = CSPRNG(32 bytes)  // unique per instance, MUST NOT reuse
///
/// ctx_core = H_bytes("PVUGC/CTX_CORE" || vk_hash || H(x) || tapleaf_hash
///                    || tapleaf_version || txid_template || path_tag
///                    || y_cols_digest || epoch_nonce)
///
/// arming_pkg_hash = H_bytes("PVUGC/ARM" || {D_j} || D_δ || header_meta)
/// presig_pkg_hash = H_bytes("PVUGC/PRESIG" || m || T || R || signer_set || coeffs)
///
/// ctx_hash = H_bytes("PVUGC/CTX" || ctx_core || arming_pkg_hash
///                    || presig_pkg_hash || dlrep_transcripts)
/// ```
#[derive(Clone, Debug)]
pub struct PvugcContextBuilder {
    /// SHA-256 hash of verifying key
    vk_hash: [u8; 32],

    /// SHA-256 hash of public inputs (statement x)
    x_hash: [u8; 32],

    /// Hash of Y-basis column digest
    y_cols_digest: [u8; 32],

    /// Taproot leaf hash (script commitment)
    tapleaf_hash: Option<[u8; 32]>,

    /// Taproot leaf version (usually 0xc0 for OP_1)
    tapleaf_version: u8,

    /// Transaction template bytes (frozen at arming time)
    txid_template: Vec<u8>,

    /// Spending path tag (e.g., "compute", "abort")
    path_tag: String,

    /// Unique per-instance nonce (256 bits from OS CSPRNG)
    /// MUST NOT be reused; prevents cross-instance replay
    epoch_nonce: [u8; 32],
}

/// Fully constructed context hash with all three layers
#[derive(Clone, Debug)]
pub struct PvugcContext {
    /// Layer 1: Statement + transaction binding
    pub ctx_core: [u8; 32],

    /// Layer 2: Arming artifacts binding (masks + header metadata)
    pub arming_pkg_hash: Option<[u8; 32]>,

    /// Layer 3: Pre-signature binding (MuSig2 params)
    pub presig_pkg_hash: Option<[u8; 32]>,

    /// Final context hash (all layers combined)
    pub ctx_hash: [u8; 32],

    /// Epoch nonce (kept for verification)
    pub epoch_nonce: [u8; 32],
}

impl PvugcContextBuilder {
    /// Create new context builder with minimal inputs
    pub fn new(
        vk_hash: [u8; 32],
        x_hash: [u8; 32],
        y_cols_digest: [u8; 32],
        epoch_nonce: [u8; 32],
    ) -> Self {
        Self {
            vk_hash,
            x_hash,
            y_cols_digest,
            tapleaf_hash: None,
            tapleaf_version: 0xc0, // OP_1
            txid_template: vec![],
            path_tag: "compute".to_string(),
            epoch_nonce,
        }
    }

    /// Set Taproot script path commitment
    pub fn with_tapleaf(mut self, tapleaf_hash: [u8; 32], version: u8) -> Self {
        self.tapleaf_hash = Some(tapleaf_hash);
        self.tapleaf_version = version;
        self
    }

    /// Set transaction template (frozen at arming)
    pub fn with_txid_template(mut self, template_bytes: Vec<u8>) -> Self {
        self.txid_template = template_bytes;
        self
    }

    /// Set spending path tag ("compute" or "abort")
    pub fn with_path_tag(mut self, tag: &str) -> Self {
        self.path_tag = tag.to_string();
        self
    }

    /// Build ctx_core (Layer 1: statement + transaction)
    /// Per spec §3, line 61
    pub fn build_ctx_core(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"PVUGC/CTX_CORE");
        hasher.update(&self.vk_hash);
        hasher.update(&self.x_hash);

        // Tapleaf binding (prevents cross-path exploitation)
        if let Some(tapleaf) = self.tapleaf_hash {
            hasher.update(&tapleaf);
            hasher.update(&[self.tapleaf_version]);
        }

        // Transaction template binding (prevents tx substitution)
        hasher.update(&self.txid_template);

        // Path tag binding
        hasher.update(self.path_tag.as_bytes());

        // Y-basis digest (guards against base substitution)
        hasher.update(&self.y_cols_digest);

        // Epoch nonce (prevents cross-instance replay)
        hasher.update(&self.epoch_nonce);

        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }

    /// Build arming package hash (Layer 2)
    /// Per spec §3, line 62
    /// Called after arming with armed bases {D_j}, D_δ
    pub fn build_arming_pkg_hash(armed_bases_bytes: &[u8], header_metadata: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"PVUGC/ARM");
        hasher.update(armed_bases_bytes);
        hasher.update(header_metadata);

        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }

    /// Build pre-signature package hash (Layer 3)
    /// Per spec §3, line 63
    /// Called after MuSig2 presignature
    pub fn build_presig_pkg_hash(
        m: &[u8],            // SIGHASH_ALL
        t: &[u8],            // Adaptor point T
        r: &[u8],            // MuSig2 nonce aggregate R
        signer_set: &[u8],   // Signer pubkeys
        musig_coeffs: &[u8], // KeyAgg coefficients
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"PVUGC/PRESIG");
        hasher.update(m);
        hasher.update(t);
        hasher.update(r);
        hasher.update(signer_set);
        hasher.update(musig_coeffs);

        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }

    /// Finalize all layers into complete ctx_hash
    pub fn finalize(
        self,
        arming_pkg_hash: Option<[u8; 32]>,
        presig_pkg_hash: Option<[u8; 32]>,
    ) -> PvugcContext {
        let ctx_core = self.build_ctx_core();

        // Layer 3: Combine all packages
        let mut hasher = Sha256::new();
        hasher.update(b"PVUGC/CTX");
        hasher.update(&ctx_core);

        if let Some(hash) = arming_pkg_hash {
            hasher.update(&hash);
        }
        if let Some(hash) = presig_pkg_hash {
            hasher.update(&hash);
        }

        let mut ctx_hash = [0u8; 32];
        ctx_hash.copy_from_slice(&hasher.finalize());

        PvugcContext {
            ctx_core,
            arming_pkg_hash,
            presig_pkg_hash,
            ctx_hash,
            epoch_nonce: self.epoch_nonce,
        }
    }
}

/// NUMS key derivation (Spec §2, line 46)
///
/// Derive deterministic, unspendable internal key for Taproot:
/// ```text
/// Q_nums <- hash_to_curve("PVUGC/NUMS" || vk_hash || H(x)
///                         || tapleaf_hash || tapleaf_version || epoch_nonce)
/// internal_key = xonly_even_y(Q_nums)
/// ```
///
/// Properties:
/// - Deterministic (same inputs → same key)
/// - Publicly derivable (no secret)
/// - Unspendable (no one knows discrete log)
/// - Cycle-free (different instances → different keys)
pub struct NumsKeyDerivation {
    vk_hash: [u8; 32],
    x_hash: [u8; 32],
    tapleaf_hash: Option<[u8; 32]>,
    tapleaf_version: u8,
    epoch_nonce: [u8; 32],
}

impl NumsKeyDerivation {
    /// Create NUMS key derivation context
    pub fn new(vk_hash: [u8; 32], x_hash: [u8; 32], epoch_nonce: [u8; 32]) -> Self {
        Self {
            vk_hash,
            x_hash,
            tapleaf_hash: None,
            tapleaf_version: 0xc0,
            epoch_nonce,
        }
    }

    /// Add tapleaf information
    pub fn with_tapleaf(mut self, tapleaf_hash: [u8; 32], version: u8) -> Self {
        self.tapleaf_hash = Some(tapleaf_hash);
        self.tapleaf_version = version;
        self
    }

    /// Compute NUMS challenge string for hash-to-curve
    /// Returns the domain-separated input for secp256k1 hash-to-curve
    pub fn compute_nums_challenge(&self) -> Vec<u8> {
        let mut challenge = Vec::new();
        challenge.extend_from_slice(b"PVUGC/NUMS");
        challenge.extend_from_slice(&self.vk_hash);
        challenge.extend_from_slice(&self.x_hash);

        if let Some(tapleaf) = self.tapleaf_hash {
            challenge.extend_from_slice(&tapleaf);
            challenge.push(self.tapleaf_version);
        }

        challenge.extend_from_slice(&self.epoch_nonce);
        challenge
    }
}

/// Verify epoch nonce uniqueness
/// Per spec §3, line 81: "MUST reject nonce reuse"
pub struct EpochNonceRegistry {
    seen_nonces: std::collections::HashSet<[u8; 32]>,
}

impl EpochNonceRegistry {
    pub fn new() -> Self {
        Self {
            seen_nonces: std::collections::HashSet::new(),
        }
    }

    /// Register a nonce; return error if already seen
    pub fn register(&mut self, nonce: [u8; 32]) -> Result<(), String> {
        if self.seen_nonces.contains(&nonce) {
            return Err("Epoch nonce reuse detected".to_string());
        }
        self.seen_nonces.insert(nonce);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ctx_core_deterministic() {
        let vk_hash = [1u8; 32];
        let x_hash = [2u8; 32];
        let y_cols = [3u8; 32];
        let nonce = [4u8; 32];

        let ctx1 = PvugcContextBuilder::new(vk_hash, x_hash, y_cols, nonce).build_ctx_core();
        let ctx2 = PvugcContextBuilder::new(vk_hash, x_hash, y_cols, nonce).build_ctx_core();

        assert_eq!(ctx1, ctx2, "ctx_core must be deterministic");
    }

    #[test]
    fn test_ctx_core_differs_on_nonce() {
        let vk_hash = [1u8; 32];
        let x_hash = [2u8; 32];
        let y_cols = [3u8; 32];
        let nonce1 = [4u8; 32];
        let nonce2 = [5u8; 32];

        let ctx1 = PvugcContextBuilder::new(vk_hash, x_hash, y_cols, nonce1).build_ctx_core();
        let ctx2 = PvugcContextBuilder::new(vk_hash, x_hash, y_cols, nonce2).build_ctx_core();

        assert_ne!(
            ctx1, ctx2,
            "Different nonces must produce different ctx_core"
        );
    }

    #[test]
    fn test_nums_challenge_generation() {
        let vk_hash = [1u8; 32];
        let x_hash = [2u8; 32];
        let nonce = [3u8; 32];

        let nums = NumsKeyDerivation::new(vk_hash, x_hash, nonce);
        let challenge = nums.compute_nums_challenge();

        // Verify it starts with domain tag
        assert!(challenge.starts_with(b"PVUGC/NUMS"));

        // Verify determinism
        let nums2 = NumsKeyDerivation::new(vk_hash, x_hash, nonce);
        let challenge2 = nums2.compute_nums_challenge();
        assert_eq!(challenge, challenge2);
    }

    #[test]
    fn test_epoch_nonce_registry() {
        let mut registry = EpochNonceRegistry::new();
        let nonce1 = [1u8; 32];
        let nonce2 = [2u8; 32];

        assert!(registry.register(nonce1).is_ok());
        assert!(registry.register(nonce2).is_ok());
        assert!(
            registry.register(nonce1).is_err(),
            "Duplicate nonce should be rejected"
        );
    }
}
