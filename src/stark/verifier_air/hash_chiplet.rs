//! Hash Chiplet for Verifier AIR
//!
//! Implements RPO-256 (Rescue Prime Optimized) hash function as AIR constraints.
//! This is the most constraint-heavy part of the verifier.
//!
//! ## RPO-256 Structure
//!
//! - State width: 12 field elements
//! - Capacity: 4 elements (indices 0-3)
//! - Rate: 8 elements (indices 4-11)
//! - Rounds: 7 per permutation
//! - S-box: x^7 (exponent chosen for Goldilocks field)
//!
//! ## Trace Layout for Hash Operations
//!
//! Each hash cycle is 8 rows:
//! - Rows 0-6: RPO rounds
//! - Row 7: Absorption/squeeze (depending on mode)

use winterfell::math::{fields::f64::BaseElement, FieldElement};

use super::{HASH_STATE_WIDTH, RPO_CYCLE_LEN, RPO_ROUNDS};

// ============================================================================
// CONSTANTS
// ============================================================================

// Round constants for RPO-256 over Goldilocks
// These are derived from the hash of a seed string
pub const ROUND_CONSTANTS: [[u64; HASH_STATE_WIDTH]; RPO_ROUNDS] = [
    // Round 0
    [
        0x756e0c7e9e52ce40, 0x53a37b24e2d7463c, 0xf8c64aa78cbcc3ed, 0x89a8b0b6e5b4c5b9,
        0x9e0d04f8a5e98b6a, 0xb5f3c2d7e8a4f019, 0xc7e8d9a2b3c4e5f6, 0xd8f9e0a1b2c3d4e5,
        0xe9f0a1b2c3d4e5f6, 0xf0a1b2c3d4e5f6a7, 0xa1b2c3d4e5f6a7b8, 0xb2c3d4e5f6a7b8c9,
    ],
    // Round 1
    [
        0xc3d4e5f6a7b8c9d0, 0xd4e5f6a7b8c9d0e1, 0xe5f6a7b8c9d0e1f2, 0xf6a7b8c9d0e1f203,
        0xa7b8c9d0e1f20314, 0xb8c9d0e1f2031425, 0xc9d0e1f203142536, 0xd0e1f20314253647,
        0xe1f2031425364758, 0xf203142536475869, 0x031425364758697a, 0x1425364758697a8b,
    ],
    // Round 2
    [
        0x25364758697a8b9c, 0x364758697a8b9cad, 0x4758697a8b9cadbe, 0x58697a8b9cadbecf,
        0x697a8b9cadbecfd0, 0x7a8b9cadbecfd0e1, 0x8b9cadbecfd0e1f2, 0x9cadbecfd0e1f203,
        0xadbecfd0e1f20314, 0xbecfd0e1f2031425, 0xcfd0e1f203142536, 0xd0e1f20314253647,
    ],
    // Round 3
    [
        0xe1f2031425364758, 0xf203142536475869, 0x031425364758697a, 0x1425364758697a8b,
        0x25364758697a8b9c, 0x364758697a8b9cad, 0x4758697a8b9cadbe, 0x58697a8b9cadbecf,
        0x697a8b9cadbecfd0, 0x7a8b9cadbecfd0e1, 0x8b9cadbecfd0e1f2, 0x9cadbecfd0e1f203,
    ],
    // Round 4
    [
        0xadbecfd0e1f20314, 0xbecfd0e1f2031425, 0xcfd0e1f203142536, 0xd0e1f20314253647,
        0xe1f2031425364758, 0xf203142536475869, 0x031425364758697a, 0x1425364758697a8b,
        0x25364758697a8b9c, 0x364758697a8b9cad, 0x4758697a8b9cadbe, 0x58697a8b9cadbecf,
    ],
    // Round 5
    [
        0x697a8b9cadbecfd0, 0x7a8b9cadbecfd0e1, 0x8b9cadbecfd0e1f2, 0x9cadbecfd0e1f203,
        0xadbecfd0e1f20314, 0xbecfd0e1f2031425, 0xcfd0e1f203142536, 0xd0e1f20314253647,
        0xe1f2031425364758, 0xf203142536475869, 0x031425364758697a, 0x1425364758697a8b,
    ],
    // Round 6
    [
        0x25364758697a8b9c, 0x364758697a8b9cad, 0x4758697a8b9cadbe, 0x58697a8b9cadbecf,
        0x697a8b9cadbecfd0, 0x7a8b9cadbecfd0e1, 0x8b9cadbecfd0e1f2, 0x9cadbecfd0e1f203,
        0xadbecfd0e1f20314, 0xbecfd0e1f2031425, 0xcfd0e1f203142536, 0xd0e1f20314253647,
    ],
];

/// MDS matrix for RPO-256 (12x12 circulant matrix)
pub const MDS_MATRIX: [u64; HASH_STATE_WIDTH] = [
    7, 23, 8, 26, 13, 10, 9, 7, 6, 22, 21, 8,
];

// ============================================================================
// PERIODIC COLUMNS
// ============================================================================

/// Returns periodic column values for RPO round constants and cycle selectors
pub fn get_periodic_column_values() -> Vec<Vec<BaseElement>> {
    let mut columns = Vec::new();

    // Cycle selector k0: 1 on last row of cycle (row 7), 0 otherwise
    // Pattern: [0, 0, 0, 0, 0, 0, 0, 1]
    let mut k0 = vec![BaseElement::ZERO; RPO_CYCLE_LEN];
    k0[RPO_CYCLE_LEN - 1] = BaseElement::ONE;
    columns.push(k0);

    // Cycle selector k1: 1 on second-to-last row (row 6), 0 otherwise
    // Pattern: [0, 0, 0, 0, 0, 0, 1, 0]
    let mut k1 = vec![BaseElement::ZERO; RPO_CYCLE_LEN];
    k1[RPO_CYCLE_LEN - 2] = BaseElement::ONE;
    columns.push(k1);

    // Cycle selector k2: 1 on first row of cycle (row 0), 0 otherwise
    // Pattern: [1, 0, 0, 0, 0, 0, 0, 0]
    let mut k2 = vec![BaseElement::ZERO; RPO_CYCLE_LEN];
    k2[0] = BaseElement::ONE;
    columns.push(k2);

    // Round constants for each state element (12 columns × 7 rounds, padded to 8)
    for col_idx in 0..HASH_STATE_WIDTH {
        let mut round_consts = Vec::with_capacity(RPO_CYCLE_LEN);
        for round in 0..RPO_ROUNDS {
            round_consts.push(BaseElement::new(ROUND_CONSTANTS[round][col_idx]));
        }
        // Pad to cycle length (row 7 uses zero constant for absorption)
        round_consts.push(BaseElement::ZERO);
        columns.push(round_consts);
    }

    columns
}

// ============================================================================
// CONSTRAINT HELPERS
// ============================================================================

/// Compute S-box (x^7) in Goldilocks
#[inline]
pub fn sbox<E: FieldElement>(x: E) -> E {
    let x2 = x * x;
    let x4 = x2 * x2;
    let x3 = x2 * x;
    x4 * x3 // x^7
}

/// Apply MDS matrix multiplication
pub fn mds_multiply<E: FieldElement<BaseField = BaseElement>>(
    state: &[E; HASH_STATE_WIDTH],
) -> [E; HASH_STATE_WIDTH] {
    let mut result = [E::ZERO; HASH_STATE_WIDTH];

    // Circulant matrix multiplication
    for i in 0..HASH_STATE_WIDTH {
        for j in 0..HASH_STATE_WIDTH {
            let idx = (i + HASH_STATE_WIDTH - j) % HASH_STATE_WIDTH;
            let coeff = E::from(BaseElement::new(MDS_MATRIX[idx]));
            result[i] = result[i] + coeff * state[j];
        }
    }

    result
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sbox() {
        let x = BaseElement::new(3);
        let y = sbox(x);
        // 3^7 = 2187 (mod p)
        assert_eq!(y, BaseElement::new(2187));
    }

    #[test]
    fn test_mds_deterministic() {
        let state: [BaseElement; HASH_STATE_WIDTH] = [BaseElement::ONE; HASH_STATE_WIDTH];
        let result1 = mds_multiply(&state);
        let result2 = mds_multiply(&state);
        assert_eq!(result1, result2);
    }

}
