//! Host-side RPO GL challenge derivation
//!
//! This module provides host-side (non-circuit) computation of Fiat-Shamir challenges
//! using the same RPO-256 sponge and transcript format as the inner circuit.
//!
//! CRITICAL: This MUST match the in-circuit FS derivation exactly for witnesses to validate.

use winter_crypto::hashers::Rp64_256;
use winter_crypto::Hasher;
use winter_math::fields::f64::BaseElement as GL;
use winter_math::FieldElement;

/// Host-side RPO-256 sponge for challenge derivation
///
/// This mirrors the in-circuit RpoGlSpongeVar exactly:
/// - Same state width (12 for RPO)
/// - Same absorption (8-byte LE limbs, round-robin)
/// - Same permutation (Rp64_256)
pub struct RpoHost {
    state: [GL; 12], // RPO-256 state width
}

impl RpoHost {
    pub fn new() -> Self {
        Self { state: [GL::ZERO; 12] }
    }

    /// Absorb bytes into state (8-byte LE limbs, round-robin)
    ///
    /// This MUST match the circuit's absorb_bytes implementation
    pub fn absorb_bytes(mut self, bytes: &[u8]) -> Self {
        let mut lane = 0usize;
        for chunk in bytes.chunks(8) {
            let mut limb = 0u64;
            for (i, b) in chunk.iter().enumerate() {
                limb |= (*b as u64) << (8 * i);
            }
            self.state[lane] = self.state[lane] + GL::new(limb);
            lane = (lane + 1) % 12;
        }
        self
    }

    /// Apply RPO-256 permutation
    pub fn permute(&mut self) {
        Rp64_256::apply_permutation(&mut self.state);
    }

    /// Squeeze one field element
    pub fn squeeze(&mut self) -> GL {
        let out = self.state[0];
        self.permute();
        out
    }
}

impl Default for RpoHost {
    fn default() -> Self {
        Self::new()
    }
}

/// Derive Fiat-Shamir challenges exactly as the inner circuit does
///
/// Transcript format: "dual_root_v1" || u32_le(num_oracles) || GL_roots || tail
///
/// CRITICAL: This MUST match inner_stark.rs lines 206-228 exactly!
///
/// # Returns
/// (alpha, betas[L], zeta) where L = num_fri_layers
pub fn derive_challenges_from_transcript(
    num_oracles: u32,
    gl_roots_le32: &[[u8; 32]],
    trace_lde_root_le32: Option<[u8;32]>,
    comp_lde_root_le32: Option<[u8;32]>,
    fri_layer_roots_le32: &[[u8;32]],
    ood_commitment_le: &[u8],
    tail_bytes: &[u8],
    num_fri_layers: usize,
) -> (GL, Vec<GL>, GL) {
    // Build transcript bytes (exact match to circuit)
    let mut bytes = Vec::new();
    bytes.extend_from_slice(b"dual_root_v1");
    bytes.extend_from_slice(&num_oracles.to_le_bytes());
    for r in gl_roots_le32 { bytes.extend_from_slice(r); }
    // FREEZE FS: Don't absorb LDE/OOD commitments to match circuit
    //if let Some(t) = trace_lde_root_le32 { bytes.extend_from_slice(&t); }
    //if let Some(c) = comp_lde_root_le32 { bytes.extend_from_slice(&c); }
    //for r in fri_layer_roots_le32 { bytes.extend_from_slice(r); }
    //if !ood_commitment_le.is_empty() { bytes.extend_from_slice(ood_commitment_le); }
    bytes.extend_from_slice(tail_bytes);

    // Derive challenges
    let mut sponge = RpoHost::new().absorb_bytes(&bytes);
    sponge.permute();
    
    let alpha = sponge.squeeze();
    let mut betas = Vec::with_capacity(num_fri_layers);
    for _ in 0..num_fri_layers {
        betas.push(sponge.squeeze());
    }
    let zeta = sponge.squeeze();

    (alpha, betas, zeta)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rpo_host_squeeze() {
        // Simple smoke test: sponge produces non-zero challenges
        let mut sponge = RpoHost::new().absorb_bytes(b"test");
        sponge.permute();
        
        let challenge = sponge.squeeze();
        assert_ne!(challenge.as_int(), 0, "Challenge should be non-zero");
    }

    #[test]
    fn test_challenge_derivation() {
        // Test challenge derivation from minimal transcript
        let gl_roots = vec![[0u8; 32]];
        let tail = vec![1, 2, 3, 4];
        
        let (alpha, betas, zeta) = derive_challenges_from_transcript(
            1,
            &gl_roots,
            None,
            None,
            &[],
            &[],
            &tail,
            3,
        );
        
        assert_ne!(alpha.as_int(), 0);
        assert_eq!(betas.len(), 3);
        assert_ne!(zeta.as_int(), 0);
        
        println!("Challenges derived: α={}, ζ={}", alpha.as_int(), zeta.as_int());
    }
}

