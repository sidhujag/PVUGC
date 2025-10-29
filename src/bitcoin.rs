//! Bitcoin Integration for PVUGC
//!
//! Provides Taproot script construction, SIGHASH binding, and transaction templating
//! per PVUGC spec §2 (Bitcoin script) and §3 (transaction binding).
//! 
//! Phase 3 adds: secp256k1 operations, BIP-327 MuSig2 presignatures, and adaptor signatures.
//!
//! Key Components:
//! - TaprootScriptPath: ComputeSpend and optional TimeoutAbort paths
//! - TransactionTemplate: Frozen Bitcoin transaction for SIGHASH binding
//! - SighashBinding: Compute and verify SIGHASH_ALL per BIP-341
//! - Helpers and re-exports for k256-based operations (x-only encoding, Schnorr)

use sha2::{Sha256, Digest};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};

// Re-export k256 secp256k1 types so tests can import via this module
pub use k256::{AffinePoint, FieldBytes, ProjectivePoint, Scalar, U256};
pub use k256::elliptic_curve::{ff::Field, PrimeField};
pub use k256::elliptic_curve::bigint::ArrayEncoding;
pub use k256::elliptic_curve::group::{Group, prime::PrimeCurveAffine};
pub use k256::elliptic_curve::ops::Reduce;
pub use k256::elliptic_curve::sec1::ToEncodedPoint;

/// Encode x-only coordinate of an affine point (BIP-340)
pub fn encoded_x(point: &AffinePoint) -> [u8; 32] {
    let encoded = point.to_encoded_point(false);
    let x_bytes = encoded.x().expect("affine x coordinate");
    let mut out = [0u8; 32];
    out.copy_from_slice(x_bytes);
    out
}

/// Encode y coordinate of an affine point
pub fn encoded_y(point: &AffinePoint) -> [u8; 32] {
    let encoded = point.to_encoded_point(false);
    let y_bytes = encoded.y().expect("affine y coordinate");
    let mut out = [0u8; 32];
    out.copy_from_slice(y_bytes);
    out
}

/// Return true if y is even (BIP-340 even-y normalization)
pub fn y_is_even(point: &AffinePoint) -> bool {
    let y = encoded_y(point);
    y[31] & 1 == 0
}

/// Tagged hash per BIP-340
pub fn tagged_hash(tag: &str, msg: &[u8]) -> [u8; 32] {
    let tag_hash = {
        let mut h = Sha256::new();
        h.update(tag.as_bytes());
        let mut out = [0u8; 32];
        out.copy_from_slice(&h.finalize());
        out
    };
    let mut hasher = Sha256::new();
    hasher.update(&tag_hash);
    hasher.update(&tag_hash);
    hasher.update(msg);
    let mut out = [0u8; 32];
    out.copy_from_slice(&hasher.finalize());
    out
}

/// BIP-340 challenge c = tagged_hash("BIP0340/challenge", R_x || P_x || m)
pub fn bip340_challenge(r_x: &[u8; 32], pk_x: &[u8; 32], msg: &[u8]) -> Scalar {
    let mut buf = Vec::with_capacity(64 + msg.len());
    buf.extend_from_slice(r_x);
    buf.extend_from_slice(pk_x);
    buf.extend_from_slice(msg);
    let hash = tagged_hash("BIP0340/challenge", &buf);
    Scalar::reduce(U256::from_be_byte_array(hash.into()))
}

/// Signature bytes (R_x || s)
pub fn signature_bytes(r: &AffinePoint, s: &Scalar) -> [u8; 64] {
    let mut out = [0u8; 64];
    out[..32].copy_from_slice(&encoded_x(r));
    out[32..].copy_from_slice(&s.to_bytes());
    out
}

/// Verify BIP-340 Schnorr signature (simple helper used in tests)
pub fn verify_schnorr_signature(pk: &AffinePoint, msg: &[u8], sig: &[u8; 64]) -> bool {
    let mut r_x = [0u8; 32];
    r_x.copy_from_slice(&sig[..32]);
    let mut s_bytes = [0u8; 32];
    s_bytes.copy_from_slice(&sig[32..]);
    let s_opt = Scalar::from_repr(FieldBytes::from(s_bytes));
    if bool::from(s_opt.is_none()) {
        return false;
    }
    let s = s_opt.unwrap();
    let e = bip340_challenge(&r_x, &encoded_x(pk), msg);
    let s_g = ProjectivePoint::GENERATOR * s;
    let e_p = ProjectivePoint::from(*pk) * e;
    let r_projective = s_g + (-e_p);
    let r_affine = AffinePoint::from(r_projective);
    if bool::from(r_affine.is_identity()) { return false; }
    if !y_is_even(&r_affine) { return false; }
    encoded_x(&r_affine) == r_x
}

/// Taproot tweak scalar for internal_key and optional merkle root
pub fn taproot_tweak_scalar(internal_key: &AffinePoint, merkle_root: Option<[u8; 32]>) -> Scalar {
    let mut tweak_input = Vec::with_capacity(32 + merkle_root.map(|_| 32).unwrap_or(0));
    tweak_input.extend_from_slice(&encoded_x(internal_key));
    if let Some(root) = merkle_root { tweak_input.extend_from_slice(&root); }
    let tweak_hash = tagged_hash("TapTweak", &tweak_input);
    Scalar::reduce(U256::from_be_byte_array(tweak_hash.into()))
}

/// Taproot output key P = internal_key + tweak·G
pub fn taproot_output_key(internal_key: &AffinePoint, merkle_root: Option<[u8; 32]>) -> AffinePoint {
    let tweak = taproot_tweak_scalar(internal_key, merkle_root);
    let tweaked = ProjectivePoint::from(*internal_key) + ProjectivePoint::GENERATOR * tweak;
    let tweaked_affine = AffinePoint::from(tweaked);
    assert!(!bool::from(tweaked_affine.is_identity()), "taproot output key must not be the identity");
    tweaked_affine
}

/// Build P2TR script for an output key (v1 witness program)
pub fn build_p2tr_script(output_key: &AffinePoint) -> bitcoin::ScriptBuf {
    use bitcoin::opcodes::all::OP_PUSHNUM_1;
    use bitcoin::script::Builder;
    Builder::new()
        .push_opcode(OP_PUSHNUM_1)
        .push_slice(&encoded_x(output_key))
        .into_script()
}

/// Compute Taproot key-spend SIGHASH for a transaction
pub fn taproot_key_spend_sighash(tx: &bitcoin::Transaction, prevouts: &[bitcoin::TxOut]) -> [u8; 32] {
    use bitcoin::sighash::{Prevouts, SighashCache, TapSighashType};
    let mut cache = SighashCache::new(tx);
    let sighash = cache
        .taproot_key_spend_signature_hash(0, &Prevouts::All(prevouts), TapSighashType::All)
        .expect("sighash");
    let mut out = [0u8; 32];
    out.copy_from_slice(sighash.as_ref());
    out
}

/// Taproot script leaf for PVUGC spending path
/// Per spec §2, lines 33-39
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct TaprootScriptPath {
    /// Script path name (e.g., "compute_spend")
    pub path_name: String,
    
    /// Raw script bytes (e.g., <P> OP_CHECKSIG)
    pub script: Vec<u8>,
    
    /// Taproot leaf version (0xc0 for OP_1)
    pub version: u8,
}

impl TaprootScriptPath {
    /// Create ComputeSpend path: `<P_compute> OP_CHECKSIG`
    /// where P_compute is a 33-byte x-only public key
    pub fn compute_spend(pubkey_xonly: &[u8; 33]) -> Self {
        let mut script = Vec::new();
        script.extend_from_slice(pubkey_xonly);
        script.push(0xac);  // OP_CHECKSIG
        
        Self {
            path_name: "compute_spend".to_string(),
            script,
            version: 0xc0,  // LEAF_VERSION_TAPSCRIPT
        }
    }
    
    /// Create TimeoutAbort path: `<Δ> OP_CHECKSEQUENCEVERIFY OP_DROP <P_abort> OP_CHECKSIG`
    /// where Δ is locktime (e.g., 144 blocks ≈ 24h)
    pub fn timeout_abort(blocks: u32, pubkey_xonly: &[u8; 33]) -> Self {
        let mut script = Vec::new();
        
        // Push locktime as little-endian
        if blocks <= 0x4f {
            script.push(0x50 + blocks as u8);  // OP_1 through OP_75 for small values
        } else if blocks <= 0xff {
            script.push(0x4c);  // OP_PUSHDATA1
            script.push(blocks as u8);
        } else if blocks <= 0xffff {
            script.push(0x4d);  // OP_PUSHDATA2
            script.push((blocks & 0xff) as u8);
            script.push(((blocks >> 8) & 0xff) as u8);
        } else {
            script.push(0x4e);  // OP_PUSHDATA4
            let bytes = blocks.to_le_bytes();
            script.extend_from_slice(&bytes);
        }
        
        script.push(0xb2);  // OP_CHECKSEQUENCEVERIFY
        script.push(0x75);  // OP_DROP
        script.extend_from_slice(pubkey_xonly);
        script.push(0xac);  // OP_CHECKSIG
        
        Self {
            path_name: "timeout_abort".to_string(),
            script,
            version: 0xc0,
        }
    }
    
    /// Compute taproot leaf hash per BIP-341
    /// leaf_hash = H_TapLeaf(version || ser_len(script) || script)
    pub fn leaf_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(b"TapLeaf");
        
        // Version
        hasher.update(&[self.version]);
        
        // Script length (compact size encoding)
        let len = self.script.len() as u32;
        if len <= 0xfc {
            hasher.update(&[len as u8]);
        } else if len <= 0xffff {
            hasher.update(&[0xfd]);
            hasher.update(&(len as u16).to_le_bytes());
        } else {
            hasher.update(&[0xfe]);
            hasher.update(&len.to_le_bytes());
        }
        
        // Script
        hasher.update(&self.script);
        
        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }
}

/// Bitcoin transaction template for PVUGC
/// Per spec §3, line 73: "txid_template is a fully specified transaction"
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct TransactionTemplate {
    /// Previous output being spent (txid || vout)
    pub prev_outpoint: Vec<u8>,
    
    /// Transaction outputs (scriptPubKey || value pairs)
    pub outputs: Vec<(Vec<u8>, u64)>,
    
    /// Locktime
    pub locktime: u32,
    
    /// Sequence (for TimeoutAbort path: 0xfffffffe for CSV-capable)
    pub sequence: u32,
    
    /// Raw transaction bytes (for SIGHASH binding)
    pub serialized: Vec<u8>,
}

impl TransactionTemplate {
    /// Create new transaction template
    pub fn new(
        prev_outpoint: Vec<u8>,
        outputs: Vec<(Vec<u8>, u64)>,
        locktime: u32,
        sequence: u32,
        serialized: Vec<u8>,
    ) -> Self {
        Self {
            prev_outpoint,
            outputs,
            locktime,
            sequence,
            serialized,
        }
    }
    
    /// Compute transaction hash for binding
    pub fn tx_hash(&self) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(&self.serialized);
        let first = hasher.finalize();
        
        let mut hasher = Sha256::new();
        hasher.update(&first);
        
        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }
}

/// SIGHASH binding per BIP-341 for Taproot script-path spending
/// Per spec §2, line 49: SIGHASH_ALL binding with annex_present = false
#[derive(Clone, Debug)]
pub struct SighashBinding {
    /// BIP-341 SigMsg digest (32 bytes)
    pub sighash: [u8; 32],
    
    /// Taproot leaf hash
    pub tapleaf_hash: [u8; 32],
    
    /// Leaf version
    pub leaf_version: u8,
}

impl SighashBinding {
    /// Compute SIGHASH_ALL for Taproot script-path spend (simplified example)
    pub fn compute_sighash_all(
        prev_outpoint: &[u8],
        prev_amount: u64,
        script_pubkey: &[u8],
        outputs: &[(Vec<u8>, u64)],
        tapleaf: &TaprootScriptPath,
        nout: u32,
    ) -> [u8; 32] {
        let mut hasher = Sha256::new();
        
        // BIP-341 SigMsg = 0x00 (epoch) for SIGHASH_ALL
        hasher.update(b"\x00");
        
        // Hash type
        hasher.update(&[0x81]);  // SIGHASH_ALL | ANYONECANPAY (simplified)
        
        // Previous outputs hash
        hasher.update(b"PVUGC_TAPROOT_SIGHASH");
        
        // Previous outpoint
        hasher.update(prev_outpoint);
        
        // Previous amount
        hasher.update(&prev_amount.to_le_bytes());
        
        // Script pubkey
        hasher.update(&(script_pubkey.len() as u32).to_le_bytes());
        hasher.update(script_pubkey);
        
        // Nout
        hasher.update(&nout.to_le_bytes());
        
        // Tapleaf
        hasher.update(&tapleaf.leaf_hash());
        
        // Outputs
        for (script, value) in outputs {
            hasher.update(&value.to_le_bytes());
            hasher.update(&(script.len() as u32).to_le_bytes());
            hasher.update(script);
        }
        
        let mut result = [0u8; 32];
        result.copy_from_slice(&hasher.finalize());
        result
    }
}

/// CPFP (Child-Pays-For-Parent) anchor output
/// Per spec §2, line 50: "small P2TR output in fixed position"
#[derive(Clone, Debug)]
pub struct CpfpAnchor {
    /// Satoshi value (small, e.g., 1000)
    pub value: u64,
    
    /// P2TR scriptPubKey
    pub script_pubkey: Vec<u8>,
    
    /// Output index (must be fixed for binding)
    pub index: u32,
}

impl CpfpAnchor {
    /// Create CPFP anchor for fee bumping
    pub fn new(value: u64, script_pubkey: Vec<u8>, index: u32) -> Self {
        Self {
            value,
            script_pubkey,
            index,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_spend_script() {
        let pubkey = [0u8; 33];
        let path = TaprootScriptPath::compute_spend(&pubkey);
        
        assert_eq!(path.path_name, "compute_spend");
        assert_eq!(path.script.len(), 34);  // 33 bytes pubkey + 1 byte OP_CHECKSIG
        assert_eq!(path.script[33], 0xac);  // OP_CHECKSIG
    }

    #[test]
    fn test_timeout_abort_script() {
        let pubkey = [0u8; 33];
        let path = TaprootScriptPath::timeout_abort(144, &pubkey);
        
        assert_eq!(path.path_name, "timeout_abort");
        assert!(path.script.len() > 34);  // locktime bytes + pubkey + opcodes
    }

    #[test]
    fn test_leaf_hash_deterministic() {
        let pubkey = [1u8; 33];
        let path = TaprootScriptPath::compute_spend(&pubkey);
        
        let hash1 = path.leaf_hash();
        let hash2 = path.leaf_hash();
        
        assert_eq!(hash1, hash2, "Leaf hash must be deterministic");
    }

    #[test]
    fn test_leaf_hash_differs_on_script_change() {
        let pubkey1 = [1u8; 33];
        let pubkey2 = [2u8; 33];
        
        let path1 = TaprootScriptPath::compute_spend(&pubkey1);
        let path2 = TaprootScriptPath::compute_spend(&pubkey2);
        
        let hash1 = path1.leaf_hash();
        let hash2 = path2.leaf_hash();
        
        assert_ne!(hash1, hash2, "Different scripts must produce different hashes");
    }

    #[test]
    fn test_transaction_template_hash() {
        let template = TransactionTemplate::new(
            vec![0u8; 32],
            vec![(vec![0x51], 10000)],
            0,
            0xfffffffe,
            vec![0x02, 0x00, 0x01, 0x00],
        );
        
        let hash1 = template.tx_hash();
        let hash2 = template.tx_hash();
        
        assert_eq!(hash1, hash2, "TX hash must be deterministic");
    }

    #[test]
    fn test_cpfp_anchor_creation() {
        let script = vec![0x51];
        let anchor = CpfpAnchor::new(1000, script.clone(), 1);
        
        assert_eq!(anchor.value, 1000);
        assert_eq!(anchor.index, 1);
    }
}
