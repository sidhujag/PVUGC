//! Merkle Tree Verification for Verifier AIR
//!
//! Implements Merkle path verification using RPO-256 compression.
//! This is used to verify:
//! - Trace commitments
//! - Composition commitments  
//! - FRI layer commitments

use winterfell::math::{fields::f64::BaseElement, FieldElement};

use super::hash_chiplet::{mds_multiply, sbox, ROUND_CONSTANTS};
use super::{HASH_STATE_WIDTH, RPO_ROUNDS};

pub const STATE_WIDTH: usize = HASH_STATE_WIDTH;

// ============================================================================
// MERKLE NODE
// ============================================================================

/// A Merkle node is a 4-element digest
pub type MerkleDigest = [BaseElement; 4];

/// Direction in Merkle path (left = 0, right = 1)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MerkleDirection {
    Left,
    Right,
}

impl From<bool> for MerkleDirection {
    fn from(bit: bool) -> Self {
        if bit {
            MerkleDirection::Right
        } else {
            MerkleDirection::Left
        }
    }
}

impl From<MerkleDirection> for BaseElement {
    fn from(dir: MerkleDirection) -> Self {
        match dir {
            MerkleDirection::Left => BaseElement::ZERO,
            MerkleDirection::Right => BaseElement::ONE,
        }
    }
}

// ============================================================================
// RPO COMPRESSION FUNCTION
// ============================================================================

/// RPO-256 compression function for Merkle trees
///
/// Compresses two 4-element nodes into one 4-element digest.
/// Uses the sponge construction with capacity in elements 0-3.
///
/// Input: left (4 elements) || right (4 elements)
/// Output: digest (4 elements from capacity after permutation)
pub fn rpo_compress(left: &MerkleDigest, right: &MerkleDigest) -> MerkleDigest {
    // Initialize state: capacity = 0, rate = left || right
    let mut state = [BaseElement::ZERO; STATE_WIDTH];

    // Absorb left into rate (positions 4-7)
    for i in 0..4 {
        state[4 + i] = left[i];
    }

    // Absorb right into rate (positions 8-11)
    for i in 0..4 {
        state[8 + i] = right[i];
    }

    // Apply RPO permutation
    rpo_permutation(&mut state);

    // Extract digest from capacity (positions 0-3)
    [state[0], state[1], state[2], state[3]]
}

/// Full RPO permutation (7 rounds)
pub fn rpo_permutation(state: &mut [BaseElement; STATE_WIDTH]) {
    for round in 0..RPO_ROUNDS {
        rpo_round(state, round);
    }
}

/// Single RPO round
fn rpo_round(state: &mut [BaseElement; STATE_WIDTH], round: usize) {
    // Add round constants
    for i in 0..STATE_WIDTH {
        state[i] = state[i] + BaseElement::new(ROUND_CONSTANTS[round][i]);
    }

    // Apply S-box
    // First half: forward S-box (x^7)
    for i in 0..STATE_WIDTH / 2 {
        state[i] = sbox(state[i]);
    }
    // Second half: inverse S-box (x^{1/7})
    // For trace building we compute this; for constraints we verify y^7 = x
    for i in STATE_WIDTH / 2..STATE_WIDTH {
        state[i] = inv_sbox(state[i]);
    }

    // Apply MDS matrix
    let new_state = mds_multiply(state);
    *state = new_state;
}

/// Inverse S-box: x^{1/7} mod p
/// Uses the fact that (1/7) mod (p-1) = INV_ALPHA
/// 
/// This must match Winterfell's inverse S-box exactly.
pub fn inv_sbox(x: BaseElement) -> BaseElement {
    // For Goldilocks: INV_ALPHA = 10540996611094048183
    const INV_ALPHA: u64 = 10540996611094048183;
    x.exp(INV_ALPHA.into())
}

// ============================================================================
// MERKLE PATH VERIFICATION
// ============================================================================

/// A single step in a Merkle authentication path
#[derive(Clone, Debug)]
pub struct MerklePathStep {
    /// Sibling node
    pub sibling: MerkleDigest,
    /// Direction: current node is left (false) or right (true)
    pub direction: MerkleDirection,
}

/// Complete Merkle authentication path
#[derive(Clone, Debug)]
pub struct MerklePath {
    /// Steps from leaf to root
    pub steps: Vec<MerklePathStep>,
}

impl MerklePath {
    /// Create a new empty path
    pub fn new() -> Self {
        Self { steps: Vec::new() }
    }

    /// Add a step to the path
    pub fn push(&mut self, sibling: MerkleDigest, direction: MerkleDirection) {
        self.steps.push(MerklePathStep { sibling, direction });
    }

    /// Verify the path from leaf to root
    ///
    /// Returns the computed root digest
    pub fn verify(&self, leaf: &MerkleDigest) -> MerkleDigest {
        let mut current = *leaf;

        for step in &self.steps {
            current = match step.direction {
                MerkleDirection::Left => {
                    // Current is left child
                    rpo_compress(&current, &step.sibling)
                }
                MerkleDirection::Right => {
                    // Current is right child
                    rpo_compress(&step.sibling, &current)
                }
            };
        }

        current
    }

    /// Depth of the path (number of steps)
    pub fn depth(&self) -> usize {
        self.steps.len()
    }
}

impl Default for MerklePath {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// MERKLE TREE BUILDER (for testing)
// ============================================================================

/// Build a Merkle tree from leaves and return root + paths
pub struct MerkleTree {
    /// All nodes in the tree (level 0 = leaves, last = root)
    levels: Vec<Vec<MerkleDigest>>,
}

impl MerkleTree {
    /// Build tree from leaves (must be power of 2)
    pub fn new(leaves: Vec<MerkleDigest>) -> Self {
        assert!(leaves.len().is_power_of_two(), "leaves must be power of 2");

        let mut levels = vec![leaves];

        // Build each level from bottom up
        while levels.last().unwrap().len() > 1 {
            let current_level = levels.last().unwrap();
            let mut next_level = Vec::with_capacity(current_level.len() / 2);

            for i in (0..current_level.len()).step_by(2) {
                let parent = rpo_compress(&current_level[i], &current_level[i + 1]);
                next_level.push(parent);
            }

            levels.push(next_level);
        }

        Self { levels }
    }

    /// Get the root digest
    pub fn root(&self) -> MerkleDigest {
        self.levels.last().unwrap()[0]
    }

    /// Get authentication path for leaf at given index
    pub fn get_path(&self, mut index: usize) -> MerklePath {
        let mut path = MerklePath::new();

        for level in 0..self.levels.len() - 1 {
            let sibling_index = if index % 2 == 0 { index + 1 } else { index - 1 };
            let direction = if index % 2 == 0 {
                MerkleDirection::Left
            } else {
                MerkleDirection::Right
            };

            path.push(self.levels[level][sibling_index], direction);
            index /= 2;
        }

        path
    }

    /// Number of leaves
    pub fn num_leaves(&self) -> usize {
        self.levels[0].len()
    }

    /// Depth of tree (number of levels - 1)
    pub fn depth(&self) -> usize {
        self.levels.len() - 1
    }
}

// ============================================================================
// BATCH MERKLE VERIFICATION
// ============================================================================

/// Batch verify multiple leaves against the same root
///
/// This is more efficient than verifying each path separately
/// when multiple queries hit the same tree.
pub struct BatchMerkleVerifier {
    /// Expected root
    pub root: MerkleDigest,
    /// Tree depth
    pub depth: usize,
}

impl BatchMerkleVerifier {
    pub fn new(root: MerkleDigest, depth: usize) -> Self {
        Self { root, depth }
    }

    /// Verify a single leaf with its path
    pub fn verify_leaf(&self, leaf: &MerkleDigest, path: &MerklePath) -> bool {
        if path.depth() != self.depth {
            return false;
        }

        let computed_root = path.verify(leaf);
        computed_root == self.root
    }

    /// Verify multiple leaves with their paths
    pub fn verify_batch(&self, leaves: &[MerkleDigest], paths: &[MerklePath]) -> bool {
        if leaves.len() != paths.len() {
            return false;
        }

        for (leaf, path) in leaves.iter().zip(paths.iter()) {
            if !self.verify_leaf(leaf, path) {
                return false;
            }
        }

        true
    }
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn make_leaf(value: u64) -> MerkleDigest {
        [
            BaseElement::new(value),
            BaseElement::new(value + 1),
            BaseElement::new(value + 2),
            BaseElement::new(value + 3),
        ]
    }

    #[test]
    fn test_rpo_compress_deterministic() {
        let left = make_leaf(1);
        let right = make_leaf(5);

        let result1 = rpo_compress(&left, &right);
        let result2 = rpo_compress(&left, &right);

        assert_eq!(result1, result2);
    }

    #[test]
    fn test_rpo_compress_order_matters() {
        let a = make_leaf(1);
        let b = make_leaf(5);

        let ab = rpo_compress(&a, &b);
        let ba = rpo_compress(&b, &a);

        assert_ne!(ab, ba);
    }

    #[test]
    fn test_merkle_tree_basic() {
        let leaves: Vec<MerkleDigest> = (0..4).map(|i| make_leaf(i * 10)).collect();
        let tree = MerkleTree::new(leaves.clone());

        assert_eq!(tree.num_leaves(), 4);
        assert_eq!(tree.depth(), 2);

        // Verify all paths
        for i in 0..4 {
            let path = tree.get_path(i);
            let computed_root = path.verify(&leaves[i]);
            assert_eq!(computed_root, tree.root());
        }
    }

    #[test]
    fn test_merkle_tree_larger() {
        let leaves: Vec<MerkleDigest> = (0..16).map(|i| make_leaf(i * 7)).collect();
        let tree = MerkleTree::new(leaves.clone());

        assert_eq!(tree.num_leaves(), 16);
        assert_eq!(tree.depth(), 4);

        // Verify random paths
        for i in [0, 5, 10, 15] {
            let path = tree.get_path(i);
            assert_eq!(path.depth(), 4);
            let computed_root = path.verify(&leaves[i]);
            assert_eq!(computed_root, tree.root());
        }
    }

    #[test]
    fn test_batch_verifier() {
        let leaves: Vec<MerkleDigest> = (0..8).map(|i| make_leaf(i * 3)).collect();
        let tree = MerkleTree::new(leaves.clone());

        let verifier = BatchMerkleVerifier::new(tree.root(), tree.depth());

        // Verify individual leaves
        for i in 0..8 {
            let path = tree.get_path(i);
            assert!(verifier.verify_leaf(&leaves[i], &path));
        }

        // Verify wrong leaf fails
        let wrong_leaf = make_leaf(999);
        let path = tree.get_path(0);
        assert!(!verifier.verify_leaf(&wrong_leaf, &path));
    }

    #[test]
    fn test_merkle_path_direction() {
        let leaves: Vec<MerkleDigest> = (0..4).map(|i| make_leaf(i)).collect();
        let tree = MerkleTree::new(leaves);

        // Index 0: left child at both levels
        let path0 = tree.get_path(0);
        assert_eq!(path0.steps[0].direction, MerkleDirection::Left);
        assert_eq!(path0.steps[1].direction, MerkleDirection::Left);

        // Index 3: right child at both levels
        let path3 = tree.get_path(3);
        assert_eq!(path3.steps[0].direction, MerkleDirection::Right);
        assert_eq!(path3.steps[1].direction, MerkleDirection::Right);
    }
}
