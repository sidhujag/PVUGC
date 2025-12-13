use super::gl_fast::GlVar;
use super::rpo_gl_light::{rpo_merge_light, RpoParamsGLLight};
use super::gl_range::UInt64Var;
use super::utils::digest32_to_gl4;
use crate::stark::StarkInnerFr as InnerFr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::prelude::*;
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

pub type FpGLVar = FpVar<InnerFr>;

/// Verify Merkle commitments for multiple openings in-circuit.
///
/// IMPORTANT (universality / fixed R1CS shape):
/// We intentionally do **not** implement Winterfell's `get_root` batch-sharing algorithm here,
/// because its control flow depends on which openings collide / become siblings at each level.
/// That would make the Groth16 constraint system depend on Fiat–Shamir query positions.
///
/// Instead, we verify each opening against the expected root using a per-opening sibling path
/// of fixed length (= `depth`). The parser must supply `nodes_bytes[i][layer]` as the sibling
/// digest for opening `i` at level `layer`, as produced by Winterfell
/// `BatchMerkleProof::into_openings`.
/// Inputs:
/// - leaves: digest per leaf (each digest is 4 GL elements)
/// - indexes: positions of leaves in the tree
/// - nodes_bytes: per-opening siblings (Vec of per-level sibling digests), each digest is 32 bytes
/// - depth: tree depth
/// - expected_root_bytes: 32-byte expected root
pub fn verify_batch_merkle_root_gl(
    cs: ConstraintSystemRef<InnerFr>,
    params: &RpoParamsGLLight,
    leaves: Vec<[GlVar; 4]>,
    indexes: &[UInt64Var],
    nodes_bytes: &[Vec<[u8; 32]>],
    depth: usize,
    expected_root_bytes: &[UInt8<InnerFr>],
) -> Result<(), SynthesisError> {
    if expected_root_bytes.len() != 32 {
        return Err(SynthesisError::Unsatisfiable);
    }
    if leaves.len() != indexes.len() {
        return Err(SynthesisError::Unsatisfiable);
    }
    if nodes_bytes.len() < leaves.len() {
        return Err(SynthesisError::Unsatisfiable);
    }

    // Convert expected root bytes to 4 GL limbs once.
    let expected_fp = digest32_to_gl4(expected_root_bytes)?;
    let expected = [
        GlVar(expected_fp[0].clone()),
        GlVar(expected_fp[1].clone()),
        GlVar(expected_fp[2].clone()),
        GlVar(expected_fp[3].clone()),
    ];

    // Convert sibling digest bytes to 4 GL limbs.
    // IMPORTANT: no caching / no "all-zero shortcut" (bytes are witness-dependent).
    let digest_from_bytes = |arr: [u8; 32]| -> Result<[GlVar; 4], SynthesisError> {
        let sib_bytes: Vec<UInt8<InnerFr>> = arr
            .iter()
            .map(|b| UInt8::new_witness(cs.clone(), || Ok(*b)))
            .collect::<Result<_, _>>()?;
        let sib_fp = digest32_to_gl4(&sib_bytes)?;
        Ok([
            GlVar(sib_fp[0].clone()),
            GlVar(sib_fp[1].clone()),
            GlVar(sib_fp[2].clone()),
            GlVar(sib_fp[3].clone()),
        ])
    };

    // Verify each opening with a fixed-depth authentication path.
    for (i, leaf) in leaves.iter().enumerate() {
        let node_vec = nodes_bytes.get(i).ok_or(SynthesisError::Unsatisfiable)?;
        if node_vec.len() < depth {
            return Err(SynthesisError::Unsatisfiable);
        }
        let idx_u64 = indexes.get(i).ok_or(SynthesisError::Unsatisfiable)?;
        let idx_bits = idx_u64.to_bits_le()?;

        let mut acc = leaf.clone();
        for layer in 0..depth {
            let sibling = digest_from_bytes(node_vec[layer])?;
            let bit = idx_bits.get(layer).ok_or(SynthesisError::Unsatisfiable)?;

            // left = bit ? sibling : acc; right = bit ? acc : sibling
            let mut left = [acc[0].clone(), acc[1].clone(), acc[2].clone(), acc[3].clone()];
            let mut right = [sibling[0].clone(), sibling[1].clone(), sibling[2].clone(), sibling[3].clone()];
            for j in 0..4 {
                let left_fp = FpVar::<InnerFr>::conditionally_select(bit, &sibling[j].0, &acc[j].0)?;
                let right_fp = FpVar::<InnerFr>::conditionally_select(bit, &acc[j].0, &sibling[j].0)?;
                left[j] = GlVar(left_fp);
                right[j] = GlVar(right_fp);
            }
            let parent = rpo_merge_light(cs.clone(), &left, &right, params)?;
            acc = [
                parent[0].clone(),
                parent[1].clone(),
                parent[2].clone(),
                parent[3].clone(),
            ];
        }

        // Root must match expected commitment.
        for j in 0..4 {
            acc[j].0.enforce_equal(&expected[j].0)?;
        }
    }

    Ok(())
}
