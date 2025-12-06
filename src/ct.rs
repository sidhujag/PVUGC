//! Ciphertext helpers with Poseidon-based DEM (Key-Committing Deterministic Encryption Mode)
//!
//! Implements the Poseidon-based DEM used by PVUGC:
//! - KDF inputs are unchanged (ser_GT(M), ctx_hash, GS digest).
//! - Keystream blocks are derived from Poseidon with the transcript binding
//!   digest and a counter: `KS_i = Poseidon("PVUGC/DEM/keystream" || K_i ||
//!   ad_digest || counter_le)`.
//! - Tags are `τ_i = Poseidon("PVUGC/DEM/tag" || K_i || ad_digest || ct_i)[..32]`.
//!
//! AD_core binds 15 components per spec §8:293:
//! "PVUGC/WE/v1" || vk_hash || H_bytes(x) || ctx_hash || tapleaf_hash ||
//! tapleaf_version || txid_template || path_tag || share_index || T_i || T ||
//! {D_j} || D_δ || GS_instance_digest

use crate::{
    error::{Error, Result},
    poseidon_fr381_t3::{absorb_bytes_native_fr, POSEIDON381_PARAMS_T3_V1},
};
use ark_bls12_381::Fr;
use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
use ark_ec::pairing::{Pairing, PairingOutput};
use core::convert::TryInto;
use subtle::ConstantTimeEq;

pub const DEM_PROFILE_ID: &[u8] = b"PVUGC/DEM-Poseidon-v1";
const AD_CORE_HASH_DOMAIN: &[u8] = b"PVUGC/AD_CORE";
const DEM_KEYSTREAM_DOMAIN: &[u8] = b"PVUGC/DEM/keystream";
const DEM_TAG_DOMAIN: &[u8] = b"PVUGC/DEM/tag";

/// Complete AD_core binding per spec §8:293
/// Binds all 15 components to ensure ciphertext integrity
#[derive(Clone, Debug)]
pub struct AdCore {
    /// "PVUGC/WE/v1" domain tag
    pub profile: Vec<u8>,
    /// SHA-256(verifying key)
    pub vk_hash: [u8; 32],
    /// SHA-256(public inputs x)
    pub x_hash: [u8; 32],
    /// Layered context hash
    pub ctx_hash: [u8; 32],
    /// Taproot leaf hash
    pub tapleaf_hash: [u8; 32],
    /// Taproot leaf version (0xc0)
    pub tapleaf_version: u8,
    /// Transaction template serialization
    pub txid_template: Vec<u8>,
    /// Path tag ("compute" or "abort")
    pub path_tag: Vec<u8>,
    /// Share index i (for multi-armer scenarios)
    pub share_index: u32,
    /// T_i = s_i · G (adaptor share point)
    pub t_i: Vec<u8>,
    /// T = Σ T_i (aggregate adaptor)
    pub t_aggregate: Vec<u8>,
    /// Armed bases {D_j} serialization
    pub armed_bases: Vec<u8>,
    /// Armed delta D_δ
    pub armed_delta: Vec<u8>,
    /// GS instance digest
    pub gs_instance_digest: [u8; 32],
}

impl AdCore {
    /// Create AD_core with all binding components
    pub fn new(
        vk_hash: [u8; 32],
        x_hash: [u8; 32],
        ctx_hash: [u8; 32],
        tapleaf_hash: [u8; 32],
        tapleaf_version: u8,
        txid_template: Vec<u8>,
        path_tag: &str,
        share_index: u32,
        t_i: Vec<u8>,
        t_aggregate: Vec<u8>,
        armed_bases: Vec<u8>,
        armed_delta: Vec<u8>,
        gs_instance_digest: [u8; 32],
    ) -> Self {
        Self {
            // DEM profile identifier bound into AD_core
            profile: DEM_PROFILE_ID.to_vec(),
            vk_hash,
            x_hash,
            ctx_hash,
            tapleaf_hash,
            tapleaf_version,
            txid_template,
            path_tag: path_tag.as_bytes().to_vec(),
            share_index,
            t_i,
            t_aggregate,
            armed_bases,
            armed_delta,
            gs_instance_digest,
        }
    }

    /// Serialize AD_core for hash input
    /// Strictly ordered per spec §8:293
    pub fn serialize(&self) -> Vec<u8> {
        let mut result = Vec::new();
        result.extend_from_slice(&self.profile);
        result.extend_from_slice(&self.vk_hash);
        result.extend_from_slice(&self.x_hash);
        result.extend_from_slice(&self.ctx_hash);
        result.extend_from_slice(&self.tapleaf_hash);
        result.push(self.tapleaf_version);

        // Length-prefixed fields
        result.extend_from_slice(&(self.txid_template.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.txid_template);

        result.extend_from_slice(&(self.path_tag.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.path_tag);

        result.extend_from_slice(&self.share_index.to_le_bytes());

        result.extend_from_slice(&(self.t_i.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.t_i);

        result.extend_from_slice(&(self.t_aggregate.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.t_aggregate);

        result.extend_from_slice(&(self.armed_bases.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.armed_bases);

        result.extend_from_slice(&(self.armed_delta.len() as u32).to_le_bytes());
        result.extend_from_slice(&self.armed_delta);

        result.extend_from_slice(&self.gs_instance_digest);
        result
    }
}

/// DEM-Poseidon: hash-only deterministic encryption mode.
/// Per spec §8: keystream and tag are derived from Poseidon2 with domain separation.
#[derive(Clone, Debug)]
pub struct DemP2 {
    /// Key derived from R^ρ
    key: Vec<u8>,
    /// Poseidon digest of AD_core (fixed-size binding)
    ad_digest: [u8; 32],
}

impl DemP2 {
    /// Create DEM-Poseidon instance
    pub fn new(k_bytes: &[u8], ad_core: &[u8]) -> Self {
        let ad_digest = ad_core_digest(ad_core);
        Self {
            key: k_bytes.to_vec(),
            ad_digest,
        }
    }

    /// Encrypt plaintext with DEM-Poseidon
    /// ct = pt ⊕ keystream
    pub fn encrypt(&self, plaintext: &[u8]) -> Vec<u8> {
        let keystream = self.derive_keystream(plaintext.len());
        plaintext
            .iter()
            .zip(keystream.iter())
            .map(|(p, k)| p ^ k)
            .collect()
    }

    /// Decrypt ciphertext with DEM-Poseidon
    /// pt = ct ⊕ keystream
    pub fn decrypt(&self, ciphertext: &[u8]) -> Vec<u8> {
        // XOR is symmetric
        self.encrypt(ciphertext)
    }

    /// Derive keystream via domain-separated Poseidon2 sponge
    fn derive_keystream(&self, len: usize) -> Vec<u8> {
        let mut keystream = Vec::with_capacity(len);
        let mut counter: u32 = 0;

        while keystream.len() < len {
            let mut sponge = PoseidonSponge::<Fr>::new(&POSEIDON381_PARAMS_T3_V1);
            absorb_bytes_native_fr(&mut sponge, DEM_KEYSTREAM_DOMAIN);
            absorb_bytes_native_fr(&mut sponge, &self.key);
            absorb_bytes_native_fr(&mut sponge, &self.ad_digest);
            let counter_bytes = counter.to_le_bytes();
            absorb_bytes_native_fr(&mut sponge, &counter_bytes);
            let block = sponge.squeeze_bytes(len - keystream.len());
            keystream.extend_from_slice(&block);
            counter = counter
                .checked_add(1)
                .expect("DEM keystream counter overflowed");
        }

        keystream
    }
}

/// Compute key-commitment tag τ_i per spec §8:286 (DEM-Poseidon)
pub fn compute_key_commitment_tag(k_bytes: &[u8], ad_core: &[u8], ciphertext: &[u8]) -> [u8; 32] {
    let ad_digest = ad_core_digest(ad_core);
    let mut sponge = PoseidonSponge::<Fr>::new(&POSEIDON381_PARAMS_T3_V1);
    absorb_bytes_native_fr(&mut sponge, DEM_TAG_DOMAIN);
    absorb_bytes_native_fr(&mut sponge, k_bytes);
    absorb_bytes_native_fr(&mut sponge, &ad_digest);
    absorb_bytes_native_fr(&mut sponge, ciphertext);
    bytes32_from_sponge(&mut sponge)
}

/// Verify DEM tag (key-commitment binding)
/// Returns true if τ_i matches computed tag
pub fn verify_key_commitment(
    k_bytes: &[u8],
    ad_core: &[u8],
    ciphertext: &[u8],
    tau_i: &[u8; 32],
) -> bool {
    let computed = compute_key_commitment_tag(k_bytes, ad_core, ciphertext);
    computed.ct_eq(tau_i).into()
}

/// Domain-separated digest of `ad_core`.
///
/// ad_digest = Poseidon2("PVUGC/AD_CORE" || len(ad_core)_le || ad_core)
pub fn ad_core_digest(ad_core: &[u8]) -> [u8; 32] {
    let mut sponge = PoseidonSponge::<Fr>::new(&POSEIDON381_PARAMS_T3_V1);
    absorb_bytes_native_fr(&mut sponge, AD_CORE_HASH_DOMAIN);
    let len_bytes = (ad_core.len() as u64).to_le_bytes();
    absorb_bytes_native_fr(&mut sponge, &len_bytes);
    absorb_bytes_native_fr(&mut sponge, ad_core);
    bytes32_from_sponge(&mut sponge)
}

fn bytes32_from_sponge(sponge: &mut PoseidonSponge<Fr>) -> [u8; 32] {
    let bytes = sponge.squeeze_bytes(32);
    bytes.try_into().expect("poseidon squeeze length")
}

/// GS attestation size bounds per spec §6:185
/// MUST reject if m_1 + m_2 > 96 pairings
pub fn validate_gs_size_bounds(num_g1_commitments: usize, num_g2_commitments: usize) -> Result<()> {
    const MAX_PAIRINGS: usize = 96;
    let total = num_g1_commitments + num_g2_commitments;

    if total > MAX_PAIRINGS {
        return Err(Error::Crypto(format!(
            "GS attestation too large: {} pairings (max {})",
            total, MAX_PAIRINGS
        )));
    }

    Ok(())
}

/// Helper to serialize a pairing output to canonical bytes.
pub fn serialize_gt<E: ark_ec::pairing::Pairing>(k: &E::TargetField) -> Vec<u8> {
    use ark_serialize::CanonicalSerialize;
    let mut out = Vec::new();
    k.serialize_compressed(&mut out).expect("serialize");
    out
}

/// Constant-time equality for GT elements via canonical compressed bytes
pub fn gt_eq_ct<E: Pairing>(a: &PairingOutput<E>, b: &PairingOutput<E>) -> bool {
    use ark_serialize::CanonicalSerialize;
    let mut ab = Vec::new();
    let mut bb = Vec::new();
    a.0.serialize_compressed(&mut ab).expect("serialize");
    b.0.serialize_compressed(&mut bb).expect("serialize");
    if ab.len() != bb.len() {
        return false;
    }
    ab.ct_eq(&bb).into()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dem_p2_roundtrip() {
        let k_bytes = b"test-key-bytes";
        let ad_core = b"test-ad-core-binding";
        let plaintext = b"hello world";

        let dem = DemP2::new(k_bytes, ad_core);
        let ciphertext = dem.encrypt(plaintext);
        let decrypted = dem.decrypt(&ciphertext);

        assert_eq!(decrypted, plaintext);
    }

    #[test]
    fn dem_p2_different_keys_different_ct() {
        let plaintext = b"hello world";

        let dem1 = DemP2::new(b"key1", b"ad-core");
        let dem2 = DemP2::new(b"key2", b"ad-core");

        let ct1 = dem1.encrypt(plaintext);
        let ct2 = dem2.encrypt(plaintext);

        assert_ne!(
            ct1, ct2,
            "Different keys must produce different ciphertexts"
        );
    }

    #[test]
    fn ad_core_serialization() {
        let ad_core = AdCore::new(
            [1u8; 32],
            [2u8; 32],
            [3u8; 32],
            [4u8; 32],
            0xc0,
            vec![5u8; 10],
            "compute",
            0,
            vec![6u8; 33],
            vec![7u8; 33],
            vec![8u8; 64],
            vec![9u8; 64],
            [10u8; 32],
        );

        let ser1 = ad_core.serialize();
        let ser2 = ad_core.serialize();

        assert_eq!(ser1, ser2, "AD_core serialization must be deterministic");
    }

    #[test]
    fn key_commitment_tag_verification() {
        let k_bytes = b"test-key";
        let ad_core = b"test-ad-core";
        let ciphertext = b"test-ciphertext";

        let tau = compute_key_commitment_tag(k_bytes, ad_core, ciphertext);
        assert!(verify_key_commitment(k_bytes, ad_core, ciphertext, &tau));

        // Different ciphertext must fail verification
        let wrong_ct = b"wrong-ciphertext";
        assert!(!verify_key_commitment(k_bytes, ad_core, wrong_ct, &tau));
    }

    #[test]
    fn gs_size_bounds() {
        assert!(validate_gs_size_bounds(50, 40).is_ok());
        assert!(validate_gs_size_bounds(96, 0).is_ok());
        assert!(
            validate_gs_size_bounds(50, 46).is_ok(),
            "96 pairings should be OK"
        );
        assert!(
            validate_gs_size_bounds(50, 47).is_err(),
            "97 pairings exceeds limit"
        );
    }
}
