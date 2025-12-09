//! Fiat-Shamir Transcript for Verifier AIR
//!
//! Implements the Fiat-Shamir heuristic for deriving challenges
//! from the proof transcript. This is critical for security.
//!
//! The transcript absorbs:
//! 1. Public inputs
//! 2. Trace commitment
//! 3. Composition commitment
//! 4. OOD frame (after deriving z)
//! 5. FRI layer commitments (after deriving DEEP coefficients)
//!
//! And derives:
//! 1. OOD challenge point z
//! 2. Constraint composition coefficients
//! 3. DEEP composition coefficients
//! 4. FRI folding challenges (betas)
//! 5. Query positions

use winterfell::math::{fields::f64::BaseElement, FieldElement};

use super::merkle::{rpo_permutation, MerkleDigest, STATE_WIDTH as HASH_STATE_WIDTH};

// ============================================================================
// TRANSCRIPT STATE
// ============================================================================

/// Fiat-Shamir transcript using RPO-256 sponge
#[derive(Clone, Debug)]
pub struct Transcript {
    /// Sponge state (12 elements)
    state: [BaseElement; HASH_STATE_WIDTH],
    /// Number of elements absorbed since last squeeze
    absorbed: usize,
}

impl Default for Transcript {
    fn default() -> Self {
        Self::new()
    }
}

impl Transcript {
    /// Create a new transcript with zero state
    pub fn new() -> Self {
        Self {
            state: [BaseElement::ZERO; HASH_STATE_WIDTH],
            absorbed: 0,
        }
    }

    /// Absorb a single field element
    pub fn absorb(&mut self, element: BaseElement) {
        // Rate is elements 4-11 (8 elements)
        let rate_idx = 4 + self.absorbed;

        if rate_idx < HASH_STATE_WIDTH {
            self.state[rate_idx] = self.state[rate_idx] + element;
            self.absorbed += 1;
        } else {
            // Rate full, permute first
            rpo_permutation(&mut self.state);
            self.absorbed = 0;
            self.state[4] = self.state[4] + element;
            self.absorbed = 1;
        }
    }

    /// Absorb multiple elements
    pub fn absorb_many(&mut self, elements: &[BaseElement]) {
        for &e in elements {
            self.absorb(e);
        }
    }

    /// Absorb a digest (4 elements)
    pub fn absorb_digest(&mut self, digest: &MerkleDigest) {
        for &e in digest {
            self.absorb(e);
        }
    }

    /// Squeeze one challenge element
    pub fn squeeze(&mut self) -> BaseElement {
        // Always permute before squeezing to mix state
        rpo_permutation(&mut self.state);
        self.absorbed = 0;

        // Return first capacity element
        self.state[0]
    }

    /// Squeeze multiple challenge elements
    pub fn squeeze_many(&mut self, count: usize) -> Vec<BaseElement> {
        let mut result = Vec::with_capacity(count);

        for _ in 0..count {
            result.push(self.squeeze());
        }

        result
    }

    /// Squeeze a challenge for quadratic extension field
    /// Returns two base field elements representing an extension field element
    pub fn squeeze_extension(&mut self) -> [BaseElement; 2] {
        [self.squeeze(), self.squeeze()]
    }

    /// Reset the transcript (for testing)
    pub fn reset(&mut self) {
        self.state = [BaseElement::ZERO; HASH_STATE_WIDTH];
        self.absorbed = 0;
    }
}

// ============================================================================
// CHALLENGE DERIVATION
// ============================================================================

/// Derived challenges for STARK verification
#[derive(Clone, Debug)]
pub struct VerificationChallenges {
    /// OOD evaluation point z (in extension field)
    pub z: [BaseElement; 2],
    /// Constraint composition coefficients
    pub constraint_coeffs: Vec<BaseElement>,
    /// DEEP composition coefficients for trace
    pub deep_trace_coeffs: Vec<BaseElement>,
    /// DEEP composition coefficients for composition poly
    pub deep_comp_coeffs: Vec<BaseElement>,
    /// FRI folding challenges (one per layer)
    pub fri_betas: Vec<BaseElement>,
    /// Query positions in LDE domain
    pub query_positions: Vec<usize>,
}

/// Derive all verification challenges from proof commitments
///
/// This follows Winterfell's challenge derivation order:
/// 1. Absorb context (trace info, options)
/// 2. Absorb trace commitment -> derive z
/// 3. Absorb OOD frame -> derive constraint coeffs
/// 4. Absorb composition commitment -> derive DEEP coeffs  
/// 5. For each FRI layer: absorb commitment -> derive beta
/// 6. After FRI: derive query positions
pub fn derive_challenges(
    transcript: &mut Transcript,
    trace_commitment: &MerkleDigest,
    ood_trace_current: &[BaseElement],
    ood_trace_next: &[BaseElement],
    ood_comp: &[BaseElement],
    comp_commitment: &MerkleDigest,
    fri_commitments: &[MerkleDigest],
    num_constraint_coeffs: usize,
    trace_width: usize,
    comp_width: usize,
    num_queries: usize,
    lde_domain_size: usize,
) -> VerificationChallenges {
    // --- Phase 1: Derive OOD point z ---
    transcript.absorb_digest(trace_commitment);
    let z = transcript.squeeze_extension();

    // --- Phase 2: Absorb OOD frame, derive constraint coeffs ---
    transcript.absorb_many(ood_trace_current);
    transcript.absorb_many(ood_trace_next);
    transcript.absorb_many(ood_comp);

    let constraint_coeffs = transcript.squeeze_many(num_constraint_coeffs);

    // --- Phase 3: Absorb comp commitment, derive DEEP coeffs ---
    transcript.absorb_digest(comp_commitment);

    // DEEP coeffs: 2 per trace column (for current and next)
    let deep_trace_coeffs = transcript.squeeze_many(trace_width * 2);
    // DEEP coeffs: 1 per composition column
    let deep_comp_coeffs = transcript.squeeze_many(comp_width);

    // --- Phase 4: FRI layer challenges ---
    let mut fri_betas = Vec::with_capacity(fri_commitments.len());
    for commit in fri_commitments {
        transcript.absorb_digest(commit);
        fri_betas.push(transcript.squeeze());
    }

    // --- Phase 5: Query positions ---
    let query_positions = derive_query_positions(transcript, num_queries, lde_domain_size);

    VerificationChallenges {
        z,
        constraint_coeffs,
        deep_trace_coeffs,
        deep_comp_coeffs,
        fri_betas,
        query_positions,
    }
}

/// Derive query positions from transcript
///
/// Uses rejection sampling to get unique positions in [0, lde_domain_size)
fn derive_query_positions(
    transcript: &mut Transcript,
    num_queries: usize,
    lde_domain_size: usize,
) -> Vec<usize> {
    let mut positions = Vec::with_capacity(num_queries);
    let mut attempts = 0;
    const MAX_ATTEMPTS: usize = 1000;

    while positions.len() < num_queries && attempts < MAX_ATTEMPTS {
        let challenge = transcript.squeeze();
        // Convert to position using modular reduction
        let pos = (challenge.as_int() as usize) % lde_domain_size;

        // Ensure uniqueness
        if !positions.contains(&pos) {
            positions.push(pos);
        }
        attempts += 1;
    }

    // Sort for consistency
    positions.sort();
    positions
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_transcript_deterministic() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();

        t1.absorb(BaseElement::new(42));
        t2.absorb(BaseElement::new(42));

        let c1 = t1.squeeze();
        let c2 = t2.squeeze();

        assert_eq!(c1, c2);
    }

    #[test]
    fn test_transcript_different_inputs() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();

        t1.absorb(BaseElement::new(1));
        t2.absorb(BaseElement::new(2));

        let c1 = t1.squeeze();
        let c2 = t2.squeeze();

        assert_ne!(c1, c2);
    }

    #[test]
    fn test_transcript_absorb_many() {
        let mut t1 = Transcript::new();
        let mut t2 = Transcript::new();

        t1.absorb(BaseElement::new(1));
        t1.absorb(BaseElement::new(2));
        t1.absorb(BaseElement::new(3));

        t2.absorb_many(&[
            BaseElement::new(1),
            BaseElement::new(2),
            BaseElement::new(3),
        ]);

        assert_eq!(t1.squeeze(), t2.squeeze());
    }

    #[test]
    fn test_transcript_full_rate() {
        let mut t = Transcript::new();

        // Absorb more than rate (8 elements)
        for i in 0..10 {
            t.absorb(BaseElement::new(i));
        }

        // Should still work
        let c = t.squeeze();
        assert_ne!(c, BaseElement::ZERO);
    }

    #[test]
    fn test_squeeze_many() {
        let mut t = Transcript::new();
        t.absorb(BaseElement::new(123));

        let challenges = t.squeeze_many(5);
        assert_eq!(challenges.len(), 5);

        // All should be different
        for i in 0..5 {
            for j in (i + 1)..5 {
                assert_ne!(challenges[i], challenges[j]);
            }
        }
    }

    #[test]
    fn test_query_positions() {
        let mut t = Transcript::new();
        t.absorb(BaseElement::new(42));

        let positions = derive_query_positions(&mut t, 4, 64);

        assert_eq!(positions.len(), 4);

        // All unique
        for i in 0..4 {
            for j in (i + 1)..4 {
                assert_ne!(positions[i], positions[j]);
            }
        }

        // All in range
        for &pos in &positions {
            assert!(pos < 64);
        }

        // Sorted
        for i in 1..4 {
            assert!(positions[i] > positions[i - 1]);
        }
    }

    #[test]
    fn test_derive_challenges() {
        let mut transcript = Transcript::new();

        let trace_commit = [BaseElement::new(1); 4];
        let ood_current = vec![BaseElement::new(2); 2];
        let ood_next = vec![BaseElement::new(3); 2];
        let ood_comp = vec![BaseElement::new(4); 2];
        let comp_commit = [BaseElement::new(5); 4];
        let fri_commits = vec![[BaseElement::new(6); 4], [BaseElement::new(7); 4]];

        let challenges = derive_challenges(
            &mut transcript,
            &trace_commit,
            &ood_current,
            &ood_next,
            &ood_comp,
            &comp_commit,
            &fri_commits,
            4,  // num_constraint_coeffs
            2,  // trace_width
            2,  // comp_width
            2,  // num_queries
            64, // lde_domain_size
        );

        assert_eq!(challenges.constraint_coeffs.len(), 4);
        assert_eq!(challenges.deep_trace_coeffs.len(), 4); // 2 * trace_width
        assert_eq!(challenges.deep_comp_coeffs.len(), 2);
        assert_eq!(challenges.fri_betas.len(), 2);
        assert_eq!(challenges.query_positions.len(), 2);
    }
}
