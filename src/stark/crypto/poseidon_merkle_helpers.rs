use ark_bls12_377::Fr as Fr377;
use ark_crypto_primitives::sponge::poseidon::{PoseidonConfig, PoseidonSponge};
use ark_crypto_primitives::sponge::CryptographicSponge;

use super::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;

#[inline]
pub fn poseidon2_hash2(cfg: &PoseidonConfig<Fr377>, a: Fr377, b: Fr377) -> Fr377 {
    let mut s = PoseidonSponge::<Fr377>::new(cfg);
    s.absorb(&a);
    s.absorb(&b);
    s.squeeze_field_elements(1)[0]
}

#[inline]
pub fn poseidon2_merkle_parent(cfg: &PoseidonConfig<Fr377>, left: Fr377, right: Fr377) -> Fr377 {
    poseidon2_hash2(cfg, left, right)
}

pub fn poseidon2_merkle_root(cfg: &PoseidonConfig<Fr377>, mut leaves: Vec<Fr377>) -> Fr377 {
    assert!(!leaves.is_empty(), "empty tree not allowed");
    if leaves.len() == 1 {
        return leaves[0];
    }
    while leaves.len() > 1 {
        let mut next = Vec::with_capacity((leaves.len() + 1) / 2);
        let mut i = 0usize;
        while i + 1 < leaves.len() {
            next.push(poseidon2_merkle_parent(cfg, leaves[i], leaves[i + 1]));
            i += 2;
        }
        if i < leaves.len() {
            next.push(poseidon2_merkle_parent(cfg, leaves[i], leaves[i]));
        }
        leaves = next;
    }
    leaves[0]
}

pub fn poseidon2_merkle_path(
    cfg: &PoseidonConfig<Fr377>,
    leaves: &[Fr377],
    mut idx: usize,
) -> (Fr377, Vec<Fr377>, Vec<bool>) {
    assert!(!leaves.is_empty(), "empty tree not allowed");
    if leaves.len() == 1 {
        return (leaves[0], vec![], vec![]);
    }
    let mut levels: Vec<Vec<Fr377>> = Vec::new();
    levels.push(leaves.to_vec());
    while levels.last().unwrap().len() > 1 {
        let cur = levels.last().unwrap();
        let mut next = Vec::with_capacity((cur.len() + 1) / 2);
        let mut i = 0usize;
        while i + 1 < cur.len() {
            next.push(poseidon2_merkle_parent(cfg, cur[i], cur[i + 1]));
            i += 2;
        }
        if i < cur.len() {
            next.push(poseidon2_merkle_parent(cfg, cur[i], cur[i]));
        }
        levels.push(next);
    }
    let root = *levels.last().unwrap().first().unwrap();

    let mut path = Vec::new();
    let mut pos = Vec::new();
    for lvl in 0..(levels.len() - 1) {
        let cur = &levels[lvl];
        // Convention: pos[k] == true means current node is the RIGHT child at level k
        let cur_is_right = (idx & 1) == 1;
        let sib_idx = if cur_is_right {
            idx.saturating_sub(1)
        } else {
            idx + 1
        };
        if sib_idx < cur.len() {
            path.push(cur[sib_idx]);
            pos.push(cur_is_right);
        } else {
            // duplicate-last case
            path.push(cur[idx]);
            pos.push(cur_is_right);
        }
        idx /= 2;
    }
    (root, path, pos)
}

pub fn poseidon2_verify_merkle_path(
    cfg: &PoseidonConfig<Fr377>,
    mut leaf: Fr377,
    path: &[Fr377],
    pos: &[bool],
    root: Fr377,
) -> bool {
    assert_eq!(path.len(), pos.len());
    for (sib, is_right) in path.iter().zip(pos.iter().copied()) {
        // Convention: is_right == true means current node is RIGHT child → parent(left=sib, right=leaf)
        leaf = if is_right {
            poseidon2_merkle_parent(cfg, *sib, leaf)
        } else {
            poseidon2_merkle_parent(cfg, leaf, *sib)
        };
    }
    leaf == root
}

#[inline]
pub fn merkle_root_default(leaves: Vec<Fr377>) -> Fr377 {
    poseidon2_merkle_root(&POSEIDON377_PARAMS_T3_V1, leaves)
}

#[inline]
pub fn merkle_path_default(leaves: &[Fr377], idx: usize) -> (Fr377, Vec<Fr377>, Vec<bool>) {
    poseidon2_merkle_path(&POSEIDON377_PARAMS_T3_V1, leaves, idx)
}

#[inline]
pub fn verify_path_default(leaf: Fr377, path: &[Fr377], pos: &[bool], root: Fr377) -> bool {
    poseidon2_verify_merkle_path(&POSEIDON377_PARAMS_T3_V1, leaf, path, pos, root)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merkle_path_round_trip() {
        let leaves = vec![
            Fr377::from(1u64),
            Fr377::from(2u64),
            Fr377::from(3u64),
            Fr377::from(4u64),
            Fr377::from(5u64),
        ];
        let (root, path, pos) = merkle_path_default(&leaves, 3);
        assert!(verify_path_default(leaves[3], &path, &pos, root));
    }
}
