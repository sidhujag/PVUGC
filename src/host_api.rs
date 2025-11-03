use ark_std::rand::{RngCore, CryptoRng};

use crate::outer_compressed as oc;
use crate::outer_compressed::{InnerFr, InnerVkDefault as InnerVk, OuterPkDefault as OuterPk, OuterProofDefault as OuterProof, OuterVkDefault as OuterVk};
use crate::{HybridQueryWitness, WinterfellTailMeta};
use crate::{prove_inner_stark, compute_inner_public_inputs};

/// Prove outer recursion end-to-end using inner STARK inputs.
/// Returns (outer_proof, outer_vk, inner_vk, inner_proof, compressed_outer_public_inputs)
pub fn prove_outer_with_inner(
    pk_outer: &OuterPk,
    inner_vk: &InnerVk,
    poseidon_roots: &[InnerFr],
    gl_roots_le_32: &[[u8; 32]],
    tail_meta: &WinterfellTailMeta,
    queries: Vec<HybridQueryWitness>,
    fri_num_layers_public: u8,
    rng: &mut (impl RngCore + CryptoRng),
) -> (OuterProof, OuterVk, crate::outer_compressed::InnerVkDefault, ark_groth16::Proof<crate::outer_compressed::InnerE>, Vec<crate::outer_compressed::OuterFr>) {
    // Prove inner
    let mat = crate::setup_inner_stark(gl_roots_le_32.len(), &queries[0], fri_num_layers_public, queries.len());
    let (inner_proof, inner_vk_out) = prove_inner_stark(
        &mat,
        poseidon_roots,
        gl_roots_le_32,
        tail_meta,
        queries,
        fri_num_layers_public,
    );

    // Build inner public inputs for outer circuit
    use crate::fs::transcript::{fr377_to_le48, flatten_roots, flatten_roots_32, build_winterfell_tail};
    let p2_roots_le_48: Vec<[u8; 48]> = poseidon_roots.iter().map(fr377_to_le48).collect();
    let gl_roots_bytes = flatten_roots_32(gl_roots_le_32);
    let p2_roots_bytes = flatten_roots(&p2_roots_le_48);
    let tail = build_winterfell_tail(tail_meta);
    let x_inner = compute_inner_public_inputs(poseidon_roots, &gl_roots_bytes, &p2_roots_bytes, &tail, fri_num_layers_public);

    // Prove outer (returns compressed public inputs)
    let (outer_proof, outer_vk, compressed_public_inputs) = oc::prove_outer(pk_outer, inner_vk, &x_inner, &inner_proof, rng).unwrap();
    (outer_proof, outer_vk, inner_vk_out, inner_proof, compressed_public_inputs)
}
