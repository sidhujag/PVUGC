use ark_bls12_377::Fr as Fr377;
use ark_ff::PrimeField;
use ark_std::rand::{SeedableRng, rngs::StdRng, Rng};

use crate::stark::crypto::poseidon_merkle_helpers::{
    poseidon2_merkle_root, poseidon2_merkle_path, verify_path_default,
};
use crate::stark::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;

fn leaves_from_u64s(vals: &[u64]) -> Vec<Fr377> {
    vals.iter().map(|&v| Fr377::from(v)).collect()
}

fn is_right(idx: usize) -> bool { (idx & 1) == 1 }

#[test]
fn poseidon_merkle_convention_and_odd_duplication() {
    let sizes = [1usize, 2, 3, 4, 5, 7, 8, 15, 16, 17, 31, 32, 33];
    let cfg = &*POSEIDON377_PARAMS_T3_V1;

    for &n in &sizes {
        let leaves = leaves_from_u64s(&(1..=n as u64).collect::<Vec<_>>());
        let root = poseidon2_merkle_root(cfg, leaves.clone());
        for idx in 0..n {
            let (r2, path, pos) = poseidon2_merkle_path(cfg, &leaves, idx);
            assert_eq!(r2, root, "root mismatch for n={}, idx={}", n, idx);
            assert!(
                verify_path_default(leaves[idx], &path, &pos, root),
                "verify failed for n={}, idx={}, path_len={}, pos={:?}",
                n, idx, path.len(), pos
            );
            if !pos.is_empty() {
                assert_eq!(
                    pos[0], is_right(idx),
                    "first pos bit mismatch: n={}, idx={}, pos[0]={}",
                    n, idx, pos[0]
                );
            }
        }
    }
}

#[test]
fn poseidon_merkle_randomized_roundtrip() {
    let mut rng = StdRng::seed_from_u64(0xC0FFEE);
    let cfg = &*POSEIDON377_PARAMS_T3_V1;

    for n in [3usize, 5, 9, 13, 21] {
        let mut leaves = Vec::with_capacity(n);
        for _ in 0..n {
            let lo: u64 = rng.gen();
            let hi: u64 = rng.gen();
            let mut bytes = [0u8; 48];
            bytes[0..8].copy_from_slice(&lo.to_le_bytes());
            bytes[8..16].copy_from_slice(&hi.to_le_bytes());
            leaves.push(Fr377::from_le_bytes_mod_order(&bytes));
        }

        let root = poseidon2_merkle_root(cfg, leaves.clone());
        for idx in 0..n {
            let (r2, path, pos) = poseidon2_merkle_path(cfg, &leaves, idx);
            assert_eq!(r2, root, "root mismatch in randomized, n={}, idx={}", n, idx);
            assert!(
                verify_path_default(leaves[idx], &path, &pos, root),
                "verify failed (randomized) for n={}, idx={}, depth= {}",
                n, idx, path.len()
            );
        }
    }
}


