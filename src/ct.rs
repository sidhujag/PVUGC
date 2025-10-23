//! Ciphertext helpers (HKDF + AEAD with context-bound associated data)

use chacha20poly1305::{aead::Aead, aead::KeyInit, ChaCha20Poly1305, Nonce, aead::Payload};
use hkdf::Hkdf;
use rand_core::{OsRng, RngCore};
use sha2::{Sha256};

/// Derive a 32-byte AEAD key and 32-byte associated-data tag from GT bytes + context digest.
fn derive_key_and_ad(k_bytes: &[u8], ctx_digest: &[u8]) -> ([u8; 32], [u8; 32]) {
    let mut ikm = Vec::with_capacity(16 + k_bytes.len() + ctx_digest.len());
    ikm.extend_from_slice(b"PVUGC/AEAD/v1");
    ikm.extend_from_slice(k_bytes);
    ikm.extend_from_slice(ctx_digest);
    let hk = Hkdf::<Sha256>::new(None, &ikm);
    let mut key = [0u8; 32];
    let mut ad = [0u8; 32];
    hk.expand(b"key", &mut key).expect("HKDF expand");
    hk.expand(b"ad", &mut ad).expect("HKDF expand");
    (key, ad)
}

/// Seal `plaintext` using `k_bytes` (serialized GT) and `ctx_digest` (transcript digest).
pub fn seal_with_k_bytes(
    k_bytes: &[u8],
    ctx_digest: &[u8],
    plaintext: &[u8],
) -> Result<(Vec<u8>, Vec<u8>), String> {
    let (key, ad) = derive_key_and_ad(k_bytes, ctx_digest);
    let cipher = ChaCha20Poly1305::new_from_slice(&key).map_err(|e| e.to_string())?;
    let mut nonce = [0u8; 12];
    OsRng.fill_bytes(&mut nonce);
    let ct = cipher
        .encrypt(Nonce::from_slice(&nonce), Payload { msg: plaintext, aad: &ad })
        .map_err(|e| e.to_string())?;
    Ok((nonce.to_vec(), ct))
}

/// Open `ciphertext` using `k_bytes` (serialized GT) and `ctx_digest`.
pub fn open_with_k_bytes(
    k_bytes: &[u8],
    ctx_digest: &[u8],
    nonce: &[u8],
    ciphertext: &[u8],
) -> Result<Vec<u8>, String> {
    if nonce.len() != 12 { return Err("invalid nonce length (expected 12 bytes)".into()); }
    let (key, ad) = derive_key_and_ad(k_bytes, ctx_digest);
    let cipher = ChaCha20Poly1305::new_from_slice(&key).map_err(|e| e.to_string())?;
    cipher
        .decrypt(Nonce::from_slice(nonce), Payload { msg: ciphertext, aad: &ad })
        .map_err(|e| e.to_string())
}

/// Helper to serialize a pairing output to canonical bytes.
pub fn serialize_gt<E: ark_ec::pairing::Pairing>(k: &E::TargetField) -> Vec<u8> {
    use ark_serialize::CanonicalSerialize;
    let mut out = Vec::new();
    k.serialize_compressed(&mut out).expect("serialize");
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::Digest;

    #[test]
    fn aead_roundtrip_with_k_bytes() {
        let k_bytes = b"dummy-pairing-output"; // In production, pass canonical GT bytes.
        let ctx = Sha256::digest(b"ctx-digest-example");
        let pt = b"hello world";
        let (nonce, ct) = seal_with_k_bytes(k_bytes, &ctx, pt).expect("seal");
        let out = open_with_k_bytes(k_bytes, &ctx, &nonce, &ct).expect("open");
        assert_eq!(out, pt);

        // Different context must fail to open
        let bad_ctx = Sha256::digest(b"another-context");
        assert!(open_with_k_bytes(k_bytes, &bad_ctx, &nonce, &ct).is_err());
    }
}


