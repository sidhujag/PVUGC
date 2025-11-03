//! Helpers to assemble Fiat–Shamir transcript bytes in a stable, library-agnostic way.
//!
//! Use these on the host to avoid hand-crafting byte layouts. Prefer serializing
//! your proof object with its canonical serializer and pass the resulting bytes
//! as the tail.
use ark_ff::{PrimeField, BigInteger};

/// Assemble the FS transcript bytes as:
///   tag || u32_le(num_oracles) || GL_roots (32B each) || P2_roots (32B each) || tail
pub fn assemble_transcript_bytes(
    tag: &str,
    num_oracles: u32,
    gl_roots_le_32: &[[u8; 32]],
    p2_roots_le_32: &[[u8; 32]],
    tail: &[u8],
) -> Vec<u8> {
    let mut out = Vec::with_capacity(
        tag.len() + 4 + gl_roots_le_32.len() * 32 + p2_roots_le_32.len() * 32 + tail.len(),
    );
    out.extend_from_slice(tag.as_bytes());
    out.extend_from_slice(&num_oracles.to_le_bytes());
    for r in gl_roots_le_32 { out.extend_from_slice(r); }
    for r in p2_roots_le_32 { out.extend_from_slice(r); }
    out.extend_from_slice(tail);
    out
}

/// Incremental builder to reduce footguns when constructing transcript bytes.
pub struct TranscriptBuilder {
    bytes: Vec<u8>,
}

impl TranscriptBuilder {
    pub fn new(tag: &str, num_oracles: u32) -> Self {
        let mut bytes = Vec::with_capacity(tag.len() + 4);
        bytes.extend_from_slice(tag.as_bytes());
        bytes.extend_from_slice(&num_oracles.to_le_bytes());
        Self { bytes }
    }

    pub fn push_gl_root(mut self, root_le_32: [u8; 32]) -> Self {
        self.bytes.extend_from_slice(&root_le_32);
        self
    }

    pub fn push_poseidon_root(mut self, root_le_32: [u8; 32]) -> Self {
        self.bytes.extend_from_slice(&root_le_32);
        self
    }

    pub fn push_bytes(mut self, tail: &[u8]) -> Self {
        self.bytes.extend_from_slice(tail);
        self
    }

    pub fn finalize(self) -> Vec<u8> { self.bytes }
}


/// Canonical 48-byte little-endian for Fr(BLS12-377)
pub fn fr377_to_le48(x: &ark_bls12_377::Fr) -> [u8; 48] {
    let mut out = [0u8; 48];
    let v = x.into_bigint().to_bytes_le();
    let len = core::cmp::min(48, v.len());
    out[..len].copy_from_slice(&v[..len]);
    out
}

/// Flatten fixed-size roots into a contiguous Vec<u8>
pub fn flatten_roots<const N: usize>(le_roots: &[[u8; N]]) -> Vec<u8> {
    let mut out = Vec::with_capacity(le_roots.len() * N);
    for r in le_roots { out.extend_from_slice(r); }
    out
}

/// Flatten an array of 32-byte roots into a contiguous Vec<u8>
pub fn flatten_roots_32(le_roots: &[[u8; 32]]) -> Vec<u8> {
    let mut out = Vec::with_capacity(le_roots.len() * 32);
    for r in le_roots { out.extend_from_slice(r); }
    out
}

// -------- Generic tail builder utilities (library-agnostic) --------

/// A minimal, chainable byte builder for transcript tails.
pub struct TailBuilder { bytes: Vec<u8> }

impl TailBuilder {
    pub fn new() -> Self { Self { bytes: Vec::new() } }
    pub fn with_capacity(cap: usize) -> Self { Self { bytes: Vec::with_capacity(cap) } }
    pub fn push_u8(mut self, v: u8) -> Self { self.bytes.push(v); self }
    pub fn push_u32_le(mut self, v: u32) -> Self { self.bytes.extend_from_slice(&v.to_le_bytes()); self }
    pub fn push_u64_le(mut self, v: u64) -> Self { self.bytes.extend_from_slice(&v.to_le_bytes()); self }
    pub fn push_bytes(mut self, data: &[u8]) -> Self { self.bytes.extend_from_slice(data); self }
    pub fn push_many_32(mut self, arrs: &[[u8;32]]) -> Self { for a in arrs { self.bytes.extend_from_slice(a); } self }
    pub fn finalize(self) -> Vec<u8> { self.bytes }
}

/// Typical Winterfell proof metadata you can pass to construct a canonical tail.
/// Populate from your proof (options, commitments, query seeds/positions, ood frame, etc.).
pub struct WinterfellTailMeta<'a> {
    pub domain_log2: u32,
    pub blowup_log2: u32,
    pub num_queries: u32,
    pub commitment_roots_le_32: &'a [[u8;32]],
    pub query_positions_le: &'a [u8],
    pub ood_frame_le: &'a [u8],
    pub extra: &'a [u8], // any additional bytes your transcript absorbs
}

/// Build a conservative transcript tail from common Winterfell fields.
pub fn build_winterfell_tail(meta: &WinterfellTailMeta) -> Vec<u8> {
    TailBuilder::new()
        .push_u32_le(meta.domain_log2)
        .push_u32_le(meta.blowup_log2)
        .push_u32_le(meta.num_queries)
        .push_many_32(meta.commitment_roots_le_32)
        .push_bytes(meta.query_positions_le)
        .push_bytes(meta.ood_frame_le)
        .push_bytes(meta.extra)
        .finalize()
}

/// If you already have a canonical proof serialization, you can just use it as tail.
pub fn build_tail_from_proof_bytes(proof_bytes: &[u8]) -> Vec<u8> {
    proof_bytes.to_vec()
}

/// Helper to derive the number of FRI layers (L) from domain/final sizes.
/// L = log2(domain_size) - log2(final_bound)
pub fn derive_fri_layers(domain_log2: u32, final_bound_log2: u32) -> u8 {
    domain_log2.saturating_sub(final_bound_log2) as u8
}

#[cfg(feature = "serde")]
/// Serialize a proof object (or any transcript-carrying struct) to bytes using bincode as tail.
pub fn build_tail_from_proof_serde<T: serde::Serialize>(obj: &T) -> Vec<u8> {
    bincode::serialize(obj).unwrap_or_default()
}


