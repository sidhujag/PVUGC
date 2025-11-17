use super::gl_fast::GlVar;
use super::rpo_gl_light::{rpo_merge_light, RpoParamsGLLight};
use super::utils::digest32_to_gl4;
use crate::outer_compressed::InnerFr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};
use std::collections::{BTreeMap, BTreeSet, HashMap};

pub type FpGLVar = FpVar<InnerFr>;

/// Verify a batch Merkle proof (Winterfell get_root algorithm) in-circuit.
/// Inputs:
/// - leaves: digest per leaf (each digest is 4 GL elements)
/// - indexes: positions of leaves in the tree
/// - nodes_bytes: proof nodes per normalized index (Vec of sibling vectors), each digest is 32 bytes
/// - depth: tree depth
/// - expected_root_bytes: 32-byte expected root
pub fn verify_batch_merkle_root_gl(
    cs: ConstraintSystemRef<InnerFr>,
    params: &RpoParamsGLLight,
    leaves: Vec<[GlVar; 4]>,
    indexes: &[usize],
    nodes_bytes: &[Vec<[u8; 32]>],
    depth: usize,
    expected_root_bytes: &[UInt8<InnerFr>],
) -> Result<(), SynthesisError> {
    // Cache byte→digest conversions so shared nodes are only constrained once
    let mut digest_cache: HashMap<[u8; 32], [GlVar; 4]> = HashMap::new();
    let mut digest_from_bytes = |arr: [u8; 32]| -> Result<[GlVar; 4], SynthesisError> {
        if let Some(d) = digest_cache.get(&arr) {
            return Ok(d.clone());
        }
        if arr.iter().all(|b| *b == 0u8) {
            let zero = GlVar(FpVar::constant(InnerFr::from(0u64)));
            let digest = [zero.clone(), zero.clone(), zero.clone(), zero];
            digest_cache.insert(arr, digest.clone());
            return Ok(digest);
        }
        let sib_bytes: Vec<UInt8<InnerFr>> = arr
            .iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let sib_fp = digest32_to_gl4(&sib_bytes)?;
        let dig = [
            GlVar(sib_fp[0].clone()),
            GlVar(sib_fp[1].clone()),
            GlVar(sib_fp[2].clone()),
            GlVar(sib_fp[3].clone()),
        ];
        digest_cache.insert(arr, dig.clone());
        Ok(dig)
    };

    // Replace odd indexes with even and dedup in ascending order
    let mut set = BTreeSet::new();
    for &index in indexes {
        set.insert(index - (index & 1));
    }
    let normalized: Vec<usize> = set.into_iter().collect();
    // Each normalized index should have a corresponding sibling path.
    if nodes_bytes.len() < normalized.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    // Build map index -> position in leaves
    let mut index_map = BTreeMap::new();
    for (i, &index) in indexes.iter().enumerate() {
        index_map.insert(index, i);
    }
    // Buffers and structures mirroring Winterfell get_root
    let mut v: BTreeMap<usize, [GlVar; 4]> = BTreeMap::new();
    let offset = 1usize << depth;
    let mut next_indexes: Vec<usize> = Vec::new();
    let mut proof_pointers: Vec<usize> = Vec::with_capacity(normalized.len());

    // First layer above leaves
    for (i, index) in normalized.iter().cloned().enumerate() {
        let buf: [[GlVar; 4]; 2];
        let left: [GlVar; 4];
        let right: [GlVar; 4];
        if let Some(&i1) = index_map.get(&index) {
            // left from leaves
            left = leaves[i1].clone();
            if let Some(&i2) = index_map.get(&(index + 1)) {
                right = leaves[i2].clone();
                proof_pointers.push(0);
            } else {
                let node_vec = nodes_bytes.get(i).ok_or(SynthesisError::Unsatisfiable)?;
                if node_vec.is_empty() {
                    return Err(SynthesisError::Unsatisfiable);
                }
                right = digest_from_bytes(node_vec[0])?;
                proof_pointers.push(1);
            }
        } else {
            // left from nodes[i][0]
            let node_vec = nodes_bytes.get(i).ok_or(SynthesisError::Unsatisfiable)?;
            if node_vec.is_empty() {
                return Err(SynthesisError::Unsatisfiable);
            }
            left = digest_from_bytes(node_vec[0])?;
            if let Some(&i2) = index_map.get(&(index + 1)) {
                right = leaves[i2].clone();
            } else {
                return Err(SynthesisError::Unsatisfiable);
            }
            proof_pointers.push(1);
        }
        buf = [left, right];
        let parent = rpo_merge_light(cs.clone(), &buf[0], &buf[1], params)?;
        let parent_index = (offset + index) >> 1;
        v.insert(
            parent_index,
            [
                parent[0].clone(),
                parent[1].clone(),
                parent[2].clone(),
                parent[3].clone(),
            ],
        );
        next_indexes.push(parent_index);
    }

    // Move up the tree
    for _depth_level in 1..depth {
        let indexes = next_indexes.clone();
        next_indexes.clear();

        let mut i = 0usize;
        while i < indexes.len() {
            let node_index = indexes[i];
            let sibling_index = node_index ^ 1;
            // determine sibling
            let sibling: [GlVar; 4];
            if i + 1 < indexes.len() && indexes[i + 1] == sibling_index {
                let s = v.get(&sibling_index).ok_or(SynthesisError::Unsatisfiable)?;
                sibling = [s[0].clone(), s[1].clone(), s[2].clone(), s[3].clone()];
                i += 1;
            } else {
                let ptr = *proof_pointers.get(i).ok_or(SynthesisError::Unsatisfiable)?;
                let node_vec = nodes_bytes.get(i).ok_or(SynthesisError::Unsatisfiable)?;
                let sib_arr = *node_vec.get(ptr).ok_or(SynthesisError::Unsatisfiable)?;
                sibling = digest_from_bytes(sib_arr)?;
                if i < proof_pointers.len() {
                    proof_pointers[i] += 1;
                }
            }
            // node
            let node = v.get(&node_index).ok_or(SynthesisError::Unsatisfiable)?;
            // parent order based on node_index parity
            let parent = if (node_index & 1) != 0 {
                rpo_merge_light(cs.clone(), &sibling, node, params)?
            } else {
                rpo_merge_light(cs.clone(), node, &sibling, params)?
            };
            let parent_index = node_index >> 1;
            v.insert(
                parent_index,
                [
                    parent[0].clone(),
                    parent[1].clone(),
                    parent[2].clone(),
                    parent[3].clone(),
                ],
            );
            next_indexes.push(parent_index);
            i += 1;
        }
    }
    // Extract root at index 1
    let root = v.get(&1).ok_or(SynthesisError::Unsatisfiable)?;
    // Compare to expected bytes
    let root_bytes = super::rpo_gl_light::canonicalize_to_bytes(cs.clone(), root)?;
    for (a, b) in root_bytes.iter().zip(expected_root_bytes.iter()) {
        let eq = a.is_eq(b)?;
        eq.enforce_equal(&Boolean::constant(true))?;
    }
    Ok(())
}
