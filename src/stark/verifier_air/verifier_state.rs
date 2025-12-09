//! Verifier State Machine
//!
//! Defines the state machine that drives STARK verification.
//! The verifier executes in phases, each producing intermediate results
//! that feed into the next phase.

use winterfell::math::{fields::f64::BaseElement, FieldElement};

// ============================================================================
// VERIFIER STATE
// ============================================================================

/// Current state of the verifier
#[derive(Clone, Debug)]
pub struct VerifierState {
    /// Current phase
    pub phase: VerificationPhase,
    /// Fiat-Shamir transcript state (sponge capacity)
    pub fs_state: [BaseElement; 4],
    /// Derived challenges
    pub challenges: VerifierChallenges,
    /// Current query index
    pub query_idx: usize,
    /// Current FRI layer
    pub fri_layer: usize,
    /// Accumulated verification results
    pub results: VerificationResults,
}

impl Default for VerifierState {
    fn default() -> Self {
        Self::new()
    }
}

impl VerifierState {
    pub fn new() -> Self {
        Self {
            phase: VerificationPhase::Initialize,
            fs_state: [BaseElement::ZERO; 4],
            challenges: VerifierChallenges::default(),
            query_idx: 0,
            fri_layer: 0,
            results: VerificationResults::default(),
        }
    }
}

// ============================================================================
// VERIFICATION PHASES
// ============================================================================

/// Phases of STARK verification
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerificationPhase {
    /// Initialize transcript with proof context
    Initialize,
    /// Derive OOD challenge point z
    DeriveOodChallenge,
    /// Verify OOD frame consistency
    VerifyOodFrame,
    /// Derive constraint coefficients
    DeriveConstraintCoeffs,
    /// Derive DEEP coefficients
    DeriveDeepCoeffs,
    /// Derive FRI folding challenges
    DeriveFriChallenges,
    /// Derive query positions
    DeriveQueryPositions,
    /// Verify trace Merkle commitments
    VerifyTraceCommitments,
    /// Verify composition Merkle commitments
    VerifyCompCommitments,
    /// Compute DEEP evaluations
    ComputeDeepEvals,
    /// Verify FRI layers
    VerifyFriLayers,
    /// Check FRI remainder
    CheckFriRemainder,
    /// Final acceptance
    Accept,
}

impl VerificationPhase {
    /// Get the next phase in sequence
    pub fn next(self) -> Option<Self> {
        match self {
            Self::Initialize => Some(Self::DeriveOodChallenge),
            Self::DeriveOodChallenge => Some(Self::VerifyOodFrame),
            Self::VerifyOodFrame => Some(Self::DeriveConstraintCoeffs),
            Self::DeriveConstraintCoeffs => Some(Self::DeriveDeepCoeffs),
            Self::DeriveDeepCoeffs => Some(Self::DeriveFriChallenges),
            Self::DeriveFriChallenges => Some(Self::DeriveQueryPositions),
            Self::DeriveQueryPositions => Some(Self::VerifyTraceCommitments),
            Self::VerifyTraceCommitments => Some(Self::VerifyCompCommitments),
            Self::VerifyCompCommitments => Some(Self::ComputeDeepEvals),
            Self::ComputeDeepEvals => Some(Self::VerifyFriLayers),
            Self::VerifyFriLayers => Some(Self::CheckFriRemainder),
            Self::CheckFriRemainder => Some(Self::Accept),
            Self::Accept => None,
        }
    }
}

// ============================================================================
// VERIFIER CHALLENGES
// ============================================================================

/// All Fiat-Shamir derived challenges
#[derive(Clone, Debug, Default)]
pub struct VerifierChallenges {
    /// OOD evaluation point
    pub z: [BaseElement; 2],
    /// Constraint composition coefficients
    pub constraint_coeffs: Vec<BaseElement>,
    /// DEEP composition coefficients
    pub deep_coeffs: DeepCoeffs,
    /// FRI folding challenges (one per layer)
    pub fri_betas: Vec<BaseElement>,
    /// Query positions in LDE domain
    pub query_positions: Vec<usize>,
}

/// DEEP composition coefficients
#[derive(Clone, Debug, Default)]
pub struct DeepCoeffs {
    /// Trace polynomial coefficients
    pub trace: Vec<BaseElement>,
    /// Composition polynomial coefficients
    pub comp: Vec<BaseElement>,
}

// ============================================================================
// VERIFICATION RESULTS
// ============================================================================

/// Accumulated verification results
#[derive(Clone, Debug, Default)]
pub struct VerificationResults {
    /// OOD frame verified successfully
    pub ood_verified: bool,
    /// All trace Merkle paths verified
    pub trace_merkle_verified: bool,
    /// All composition Merkle paths verified
    pub comp_merkle_verified: bool,
    /// All FRI layers verified
    pub fri_verified: bool,
    /// FRI remainder check passed
    pub remainder_verified: bool,
    /// Final verification status
    pub accepted: bool,
}

impl VerificationResults {
    /// Check if all intermediate results are valid
    pub fn all_passed(&self) -> bool {
        self.ood_verified
            && self.trace_merkle_verified
            && self.comp_merkle_verified
            && self.fri_verified
            && self.remainder_verified
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_phase_sequence() {
        let mut phase = VerificationPhase::Initialize;
        let mut count = 0;

        while let Some(next) = phase.next() {
            phase = next;
            count += 1;
        }

        assert_eq!(phase, VerificationPhase::Accept);
        assert_eq!(count, 12); // 12 phases after Initialize
    }

    #[test]
    fn test_results_all_passed() {
        let mut results = VerificationResults::default();
        assert!(!results.all_passed());

        results.ood_verified = true;
        results.trace_merkle_verified = true;
        results.comp_merkle_verified = true;
        results.fri_verified = true;
        results.remainder_verified = true;

        assert!(results.all_passed());
    }
}
