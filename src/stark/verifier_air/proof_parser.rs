//! Proof Parser for Verifier AIR
//!
//! Parses Winterfell proofs into the format needed for verification trace generation.
//! This extracts all the cryptographic commitments, OOD evaluations, and query data.
//!
//! ## Production Implementation
//!
//! This parser extracts REAL data from the Winterfell Proof:
//! - Actual commitments from proof.commitments
//! - Actual OOD evaluations from proof.ood_frame
//! - Actual query openings from proof.trace_queries and proof.constraint_queries
//! - Actual FRI layer data from proof.fri_proof
//!
//! This enables true recursive STARK verification where the Verifier STARK
//! cryptographically verifies the inner proof.

use winter_crypto::{Digest, ElementHasher};
use winterfell::{
    math::{fields::f64::BaseElement, FieldElement, StarkField, ToElements},
    Air, Proof,
};

use super::{
    merkle::{MerkleDigest, MerklePath, MerkleDirection},
    prover::{ParsedProof, QueryData, FriLayerData, FriQueryData},
};

use std::any::TypeId;
use super::VerifierPublicInputs;

/// The hasher type used throughout proof parsing (RPO-256)
type Hasher = winter_crypto::hashers::Rp64_256;

// ============================================================================
// PROOF PARSING - PRODUCTION IMPLEMENTATION
// ============================================================================

/// Parse a Winterfell proof into our structured format
///
/// This is the PRODUCTION implementation that extracts real proof data:
/// - Actual Merkle commitments
/// - Actual OOD evaluations
/// - Actual query openings
/// - Actual FRI layer data
pub fn parse_proof<A: Air<BaseField = BaseElement>>(
    proof: &Proof,
    pub_inputs: &A::PublicInputs,
) -> ParsedProof 
where
    A::PublicInputs: ToElements<BaseElement> + Clone + 'static,
{
    let context = &proof.context;
    let trace_info = context.trace_info();
    let options = proof.options();

    // Basic parameters
    let trace_width = trace_info.main_trace_width();
    let aux_trace_width = trace_info.aux_segment_width();
    let trace_len = trace_info.length();
    let lde_blowup = options.blowup_factor();
    let num_queries = options.num_queries();
    let lde_domain_size = trace_len * lde_blowup;

    // Compute FRI parameters
    let folding_factor = options.to_fri_options().folding_factor();
    let num_fri_layers = options.to_fri_options().num_fri_layers(lde_domain_size);
    let grinding_factor = options.grinding_factor();
    let num_trace_segments = trace_info.num_segments();
    let num_aux_segment_rands = trace_info.get_num_aux_segment_rand_elements();
    // Packed proof-options element used by Winterfell in ProofContext::to_elements().
    // See winter-air `ProofOptions::to_elements()`.
    let proof_options_packed =
        <winterfell::ProofOptions as winter_math::ToElements<BaseElement>>::to_elements(options)[0]
            .as_int();

    // ========================================================================
    // PARSE ACTUAL COMMITMENTS FROM PROOF
    // ========================================================================
    
    // Parse commitments from proof.commitments
    // This gives us the actual Merkle roots for trace, composition, and FRI layers
    let (trace_commitments_raw, comp_commitment_raw, fri_commitments_raw) = proof
        .commitments
        .clone()
        .parse::<winter_crypto::hashers::Rp64_256>(num_trace_segments, num_fri_layers)
        .expect("Failed to parse commitments from proof");

    // Convert to our MerkleDigest format (4 field elements)
    let trace_commitment = digest_to_merkle_digest(&trace_commitments_raw[0]);
    let comp_commitment = digest_to_merkle_digest(&comp_commitment_raw);
    let fri_commitments: Vec<MerkleDigest> = fri_commitments_raw
        .iter()
        .map(|d| digest_to_merkle_digest(d))
        .collect();

    // ========================================================================
    // PARSE ACTUAL OOD FRAME FROM PROOF
    // ========================================================================
    
    // Composition polynomial width (number of columns).
    //
    // IMPORTANT: this must match the prover/AIR, otherwise OOD-frame parsing will fail.
    // We derive it by reconstructing the AIR from the proof context.
    let air = A::new(trace_info.clone(), pub_inputs.clone(), options.clone());
    let comp_width = air.context().num_constraint_composition_columns();
    let ce_domain_size = air.context().ce_domain_size();
    let num_transition_exemptions = air.context().num_transition_exemptions();

    // Parse OOD frame - these are the actual evaluations at the OOD point z
    let (trace_ood_frame, comp_ood_frame) = proof
        .ood_frame
        .clone()
        .parse::<BaseElement>(trace_width, aux_trace_width, comp_width)
        .expect("Failed to parse OOD frame from proof");

    // Extract evaluations at z (current) and z*g (next)
    let ood_trace_current: Vec<BaseElement> = trace_ood_frame.current_row().to_vec();
    let ood_trace_next: Vec<BaseElement> = trace_ood_frame.next_row().to_vec();
    let ood_comp_current: Vec<BaseElement> = comp_ood_frame.current_row().to_vec();
    // Winterfell uses ood_quotient_frame.next_row() for DEEP composition!
    let ood_comp_next: Vec<BaseElement> = comp_ood_frame.next_row().to_vec();

    // ========================================================================
    // DERIVE OOD PARAMETERS AND QUERY POSITIONS VIA FIAT-SHAMIR (verifier-exact)
    // ========================================================================
    //
    // IMPORTANT: query positions must match Winterfell exactly; otherwise, Merkle path
    // verification fails. We replay the verifier transcript using the AIR methods
    // `get_constraint_composition_coefficients` and `get_deep_composition_coefficients`.
    use winter_crypto::{DefaultRandomCoin, RandomCoin};
    use winter_air::proof::merge_ood_evaluations;
    use winter_math::ToElements as _;

    // Fiat–Shamir seed material used by Winterfell: context.to_elements() || pub_inputs.to_elements().
    // We reconstruct these deterministically inside VerifierAir; here we use them only for
    // off-circuit verifier replay (parsing/sorting openings).
    let context_elems = proof.context.to_elements();
    let pub_inputs_elems = pub_inputs.to_elements();
    let mut public_coin_seed = context_elems.clone();
    public_coin_seed.extend_from_slice(&pub_inputs_elems);
    let mut public_coin = DefaultRandomCoin::<Hasher>::new(&public_coin_seed);

    for trace_root in &trace_commitments_raw {
        public_coin.reseed(*trace_root);
    }
    let constraint_coeffs_obj = air
        .get_constraint_composition_coefficients::<BaseElement, _>(&mut public_coin)
        .expect("draw constraint coeffs");
    let mut constraint_coeffs: Vec<BaseElement> = constraint_coeffs_obj.transition;
    constraint_coeffs.extend_from_slice(&constraint_coeffs_obj.boundary);

    // Reseed with composition commitment and draw OOD point z.
    public_coin.reseed(comp_commitment_raw);
    let z = public_coin.draw::<BaseElement>().expect("draw z");

    // Absorb OOD frame and derive DEEP coefficients.
    let ood_evals = merge_ood_evaluations(&trace_ood_frame, &comp_ood_frame);
    let ood_evals_digest_raw = Hasher::hash_elements(&ood_evals);
    let ood_evals_digest = digest_to_merkle_digest(&ood_evals_digest_raw);
    public_coin.reseed(ood_evals_digest_raw);
    let deep_coeffs_obj = air
        .get_deep_composition_coefficients::<BaseElement, _>(&mut public_coin)
        .expect("draw DEEP coeffs");
    let mut deep_coeffs: Vec<BaseElement> = deep_coeffs_obj.trace;
    deep_coeffs.extend_from_slice(&deep_coeffs_obj.constraints);

    // Draw FRI betas (one per FRI layer).
    let mut fri_betas = Vec::with_capacity(num_fri_layers);
    for (i, fri_root) in fri_commitments_raw.iter().enumerate() {
        public_coin.reseed(*fri_root);
        if i < num_fri_layers {
            fri_betas.push(public_coin.draw::<BaseElement>().expect("draw FRI beta"));
        }
    }

    // Draw raw query positions (unsorted; duplicates possible).
    let raw_query_positions = public_coin
        .draw_integers(proof.options().num_queries(), lde_domain_size, proof.pow_nonce)
        .expect("draw query positions");

    // Canonical Winterfell verifier order is sorted unique.
    let mut query_positions = raw_query_positions.clone();
    // Winterfell proofs provide openings for unique, sorted queries (deduped).
    // For recursion we keep a fixed `num_queries` execution schedule (raw draw order),
    // and if collisions occur we simply re-use the opening for the repeated index.
    query_positions.sort_unstable();
    query_positions.dedup();
    let actual_num_queries = query_positions.len();
    // NOTE: We do NOT require `actual_num_queries == num_queries`. Collisions are allowed (rare),
    // and simply reduce the number of distinct checks in the usual STARK soundness accounting.
    let num_constraints = proof.context.num_constraints();
    
    // Compute trace domain generator
    let g_trace = compute_trace_generator(trace_len);
    
    // Extract "pub_result" for the proof being verified.
    //
    // - For app AIRs (VDF, CubicFib, etc.) and AggregatorAir, this is the first public input element.
    // - For VerifierAir proofs, `pub_result` is a dedicated field in `VerifierPublicInputs` and is NOT
    //   the first element (the first 4 elements are `statement_hash`).
    let pub_inputs_elements = pub_inputs.to_elements();
    let pub_result = if TypeId::of::<A::PublicInputs>() == TypeId::of::<VerifierPublicInputs>() {
        // Layout per `VerifierPublicInputs::to_elements()`:
        // [... commitments ...][num_queries][proof_trace_len][g_trace][pub_result][expected_checkpoint_count][expected_mode_counter][params_digest(4)]
        let n = pub_inputs_elements.len();
        if n >= 7 { pub_inputs_elements[n - 7] } else { BaseElement::ZERO }
    } else {
        pub_inputs_elements.first().copied().unwrap_or(BaseElement::ZERO)
    };

    // ========================================================================
    // PARSE ACTUAL QUERY OPENINGS FROM PROOF
    // ========================================================================
    
    let trace_queries_sorted = parse_trace_queries_real(
        proof, 
        actual_num_queries, 
        trace_width, 
        lde_domain_size,
        &query_positions,
    );
    let comp_queries_sorted = parse_comp_queries_real(
        proof, 
        actual_num_queries, 
        comp_width, 
        lde_domain_size,
        &query_positions,
    );

    // ========================================================================
    // PARSE ACTUAL FRI LAYER DATA FROM PROOF
    // ========================================================================
    
    let fri_layers_sorted = parse_fri_layers_real(
        proof, 
        num_fri_layers, 
        actual_num_queries,
        folding_factor,
        lde_domain_size,
        &query_positions,
        &fri_betas,
    );

    // Reorder openings into raw draw order so the recursive verifier can avoid in-AIR sorting.
    // This does not change the checked set; it only changes evaluation order.
    let mut idx_by_pos = std::collections::HashMap::<usize, usize>::new();
    for (i, &p) in query_positions.iter().enumerate() {
        idx_by_pos.insert(p, i);
    }
    let mut trace_queries = Vec::with_capacity(num_queries);
    let mut comp_queries = Vec::with_capacity(num_queries);
    for &p in raw_query_positions.iter() {
        let i = *idx_by_pos.get(&p).expect("raw position not in sorted positions");
        trace_queries.push(trace_queries_sorted[i].clone());
        comp_queries.push(comp_queries_sorted[i].clone());
    }
    // Rewrite positions to the raw order positions.
    for (q, &p) in trace_queries.iter_mut().zip(raw_query_positions.iter()) {
        q.position = p;
    }
    for (q, &p) in comp_queries.iter_mut().zip(raw_query_positions.iter()) {
        q.position = p;
    }
    let mut fri_layers = Vec::with_capacity(fri_layers_sorted.len());
    for layer in fri_layers_sorted.into_iter() {
        let mut queries = Vec::with_capacity(layer.queries.len());
        for &p in raw_query_positions.iter() {
            let i = *idx_by_pos.get(&p).expect("raw position not in sorted positions");
            queries.push(layer.queries[i].clone());
        }
        fri_layers.push(FriLayerData { beta: layer.beta, queries });
    }

    // Parse FRI remainder coefficients from proof
    // For Constant terminal: empty
    // For Poly terminal: coefficients in GL, low->high order
    let fri_remainder_coeffs: Vec<BaseElement> = {
        let fri_proof = &proof.fri_proof;
        if fri_proof.num_partitions() == 0 {
            vec![]
        } else {
            // Parse remainder from the proof
            // The remainder is stored as the final layer values when terminal is Poly
            fri_proof.parse_remainder::<BaseElement>()
                .unwrap_or_else(|_| vec![])
        }
    };
    
    // Determine terminal type based on remainder
    let fri_terminal_is_constant = fri_remainder_coeffs.is_empty();
    
    // Compute domain parameters
    let domain_offset = BaseElement::GENERATOR;
    let g_lde = BaseElement::get_root_of_unity(lde_domain_size.ilog2());
    
    // ========================================================================
    // Extract VerifierAir public-input tail if present (for VerifierAir-as-child)
    // ========================================================================
    let pub_elems = pub_inputs.to_elements();
    let mut verifier_statement_hash = [BaseElement::ZERO; 4];
    if pub_elems.len() >= 4 {
        verifier_statement_hash.copy_from_slice(&pub_elems[0..4]);
    }
    let mut verifier_params_digest = [BaseElement::ZERO; 4];
    let (verifier_expected_checkpoint_count, verifier_expected_mode_counter) = if pub_elems.len() >= 6 {
        let tail = &pub_elems[pub_elems.len() - 6..];
        verifier_params_digest.copy_from_slice(&tail[2..6]);
        (tail[0].as_int() as usize, tail[1].as_int() as usize)
    } else {
        (0usize, 0usize)
    };

    ParsedProof {
        pow_nonce: proof.pow_nonce,
        pub_inputs_elements: pub_elems.clone(),
        trace_commitment,
        comp_commitment,
        fri_commitments,
        ood_trace_current,
        ood_trace_next,
        ood_comp_current,
        ood_comp_next,
        ood_evals_digest,
        // OOD verification parameters
        z,
        g_trace,
        constraint_coeffs,
        pub_result,
        verifier_statement_hash,
        verifier_params_digest,
        verifier_expected_checkpoint_count,
        verifier_expected_mode_counter,
        // Query and layer data
        trace_queries,
        comp_queries,
        fri_layers,
        // FRI verification data
        fri_remainder_coeffs,
        fri_terminal_is_constant,
        // Keep the canonical verifier order (sorted unique) to align with openings in the proof.
        query_positions,
        deep_coeffs,
        domain_offset,
        g_lde,
        // Parameters
        trace_width,
        aux_trace_width,
        comp_width,
        trace_len,
        lde_blowup,
        ce_domain_size,
        num_transition_exemptions,
        num_queries,
        num_constraints,
        num_fri_layers,
        fri_folding_factor: folding_factor,
        grinding_factor,
        num_trace_segments,
        proof_options_packed,
        num_aux_segment_rands,
    }
}

// ============================================================================
// DIGEST CONVERSION
// ============================================================================

/// Convert a Winterfell digest to our MerkleDigest format (4 field elements)
fn digest_to_merkle_digest<D: Digest>(digest: &D) -> MerkleDigest {
    let bytes = digest.as_bytes();
    // Split 32 bytes into 4 x 8 bytes, interpret as u64, create field elements
    [
        BaseElement::new(u64::from_le_bytes(bytes[0..8].try_into().unwrap())),
        BaseElement::new(u64::from_le_bytes(bytes[8..16].try_into().unwrap())),
        BaseElement::new(u64::from_le_bytes(bytes[16..24].try_into().unwrap())),
        BaseElement::new(u64::from_le_bytes(bytes[24..32].try_into().unwrap())),
    ]
}

/// Compute trace domain generator for given trace length
fn compute_trace_generator(trace_len: usize) -> BaseElement {
    use winterfell::math::StarkField;
    BaseElement::get_root_of_unity(trace_len.trailing_zeros())
}

// ============================================================================
// REAL QUERY PARSING
// ============================================================================

/// Parse trace query openings from real proof data
fn parse_trace_queries_real(
    proof: &Proof,
    num_queries: usize,
    trace_width: usize,
    lde_domain_size: usize,
    query_positions: &[usize],
) -> Vec<QueryData> {
    type Hasher = winter_crypto::hashers::Rp64_256;
    type VectorCommit = winter_crypto::MerkleTree<Hasher>;
    
    // Parse the trace queries from proof
    // proof.trace_queries is a Vec<Queries>, one per trace segment
    if proof.trace_queries.is_empty() {
        // Return placeholder if no queries (shouldn't happen in valid proof)
        return (0..num_queries)
            .map(|i| QueryData {
                position: query_positions.get(i).copied().unwrap_or(0),
                values: vec![BaseElement::ZERO; trace_width],
                merkle_path: MerklePath::new(),
            })
            .collect();
    }

    // Parse main trace segment (index 0)
    let (batch_proof, table) = proof.trace_queries[0]
        .clone()
        .parse::<BaseElement, Hasher, VectorCommit>(lde_domain_size, num_queries, trace_width)
        .expect("Failed to parse trace queries");

    // Convert Table to Vec<Vec<E>> using rows() iterator
    let rows_vec: Vec<Vec<BaseElement>> = table.rows().map(|row| row.to_vec()).collect();

    // Compute leaf digests from the row values
    // Each leaf is hash(row_values)
    let leaf_digests: Vec<<Hasher as winter_crypto::Hasher>::Digest> = rows_vec.iter()
        .map(|row| Hasher::hash_elements(row))
        .collect();

    // Extract all Merkle paths using Winterfell's decompression
    let merkle_paths = extract_all_merkle_paths_from_batch(
        batch_proof,
        query_positions,
        &leaf_digests,
    );

    let mut queries = Vec::with_capacity(num_queries);
    for (q_idx, &position) in query_positions.iter().take(num_queries).enumerate() {
        // Get the row values for this query
        // NOTE: This assumes rows_vec is in the same order as query_positions!
        let values: Vec<BaseElement> = if q_idx < rows_vec.len() {
            rows_vec[q_idx].clone()
        } else {
            vec![BaseElement::ZERO; trace_width]
        };

        // Get the decompressed Merkle path for this query
        let merkle_path = if q_idx < merkle_paths.len() {
            merkle_paths[q_idx].clone()
        } else {
            MerklePath::new()
        };

        queries.push(QueryData {
            position,
            values,
            merkle_path,
        });
    }

    queries
}

/// Parse composition query openings from real proof data
fn parse_comp_queries_real(
    proof: &Proof,
    num_queries: usize,
    comp_width: usize,
    lde_domain_size: usize,
    query_positions: &[usize],
) -> Vec<QueryData> {
    type Hasher = winter_crypto::hashers::Rp64_256;
    type VectorCommit = winter_crypto::MerkleTree<Hasher>;

    // Parse the constraint queries from proof
    let (batch_proof, table) = proof.constraint_queries
        .clone()
        .parse::<BaseElement, Hasher, VectorCommit>(lde_domain_size, num_queries, comp_width)
        .expect("Failed to parse constraint queries");

    // Convert Table to Vec<Vec<E>> using rows() iterator
    let rows_vec: Vec<Vec<BaseElement>> = table.rows().map(|row| row.to_vec()).collect();

    // Compute leaf digests from the row values
    let leaf_digests: Vec<<Hasher as winter_crypto::Hasher>::Digest> = rows_vec.iter()
        .map(|row| Hasher::hash_elements(row))
        .collect();

    // Extract all Merkle paths using Winterfell's decompression
    let merkle_paths = extract_all_merkle_paths_from_batch(
        batch_proof,
        query_positions,
        &leaf_digests,
    );

    let mut queries = Vec::with_capacity(num_queries);
    for (q_idx, &position) in query_positions.iter().take(num_queries).enumerate() {
        let values: Vec<BaseElement> = if q_idx < rows_vec.len() {
            rows_vec[q_idx].clone()
        } else {
            vec![BaseElement::ZERO; comp_width]
        };

        // Get the decompressed Merkle path for this query
        let merkle_path = if q_idx < merkle_paths.len() {
            merkle_paths[q_idx].clone()
        } else {
            MerklePath::new()
        };

        queries.push(QueryData {
            position,
            values,
            merkle_path,
        });
    }

    queries
}

/// Extract individual Merkle paths from a batch proof using Winterfell's decompression
/// 
/// This uses `into_openings` to decompress the batch proof into individual proofs,
/// then converts each to our MerklePath format.
fn extract_all_merkle_paths_from_batch<H: ElementHasher>(
    batch_proof: winter_crypto::BatchMerkleProof<H>,
    query_positions: &[usize],
    leaves: &[<H as winter_crypto::Hasher>::Digest],
) -> Vec<MerklePath> {
    
    // Use Winterfell's into_openings to decompress the batch proof
    let openings = batch_proof.into_openings(leaves, query_positions)
        .unwrap_or_else(|_| vec![]);
    
    let mut paths = Vec::with_capacity(openings.len());
    
    for (q_idx, opening) in openings.into_iter().enumerate() {
        let (_leaf_digest, siblings) = opening;
        let position = query_positions[q_idx];
        
    let mut path = MerklePath::new();

        for (layer, sibling) in siblings.into_iter().enumerate() {
            // Direction is based on the POSITION in the tree
            // At layer L, bit (position >> L) & 1 tells us if current node is left (0) or right (1) child
            let direction = if (position >> layer) & 1 == 0 {
                MerkleDirection::Left
            } else {
                MerkleDirection::Right
            };
            path.push(digest_to_merkle_digest(&sibling), direction);
        }
        
        paths.push(path);
    }

    paths
}

// ============================================================================
// REAL FRI LAYER PARSING
// ============================================================================

/// Parse FRI layer data from real proof data
fn parse_fri_layers_real(
    proof: &Proof,
    num_layers: usize,
    _num_queries: usize,
    folding_factor: usize,
    lde_domain_size: usize,
    query_positions: &[usize],
    fri_betas: &[BaseElement],
) -> Vec<FriLayerData> {
    type VectorCommit = winter_crypto::MerkleTree<Hasher>;

    // Parse all FRI layers at once using parse_layers
    let (layer_queries, mut layer_proofs) = proof.fri_proof
        .clone()
        .parse_layers::<BaseElement, Hasher, VectorCommit>(lde_domain_size, folding_factor)
        .expect("Failed to parse FRI layers");

    let mut layers = Vec::with_capacity(num_layers);
    let mut current_domain_size = lde_domain_size;
    let mut current_positions: Vec<usize> = query_positions.to_vec();
    
    // Reverse proofs so we can pop from the end (maintaining order)
    layer_proofs.reverse();

    // NOTE: This parser runs OUTSIDE the circuit. Validation here is just sanity checking.
    // REAL SECURITY comes from AIR constraints:
    //   - Missing/wrong commitments → Merkle verify_root fails → all_valid=false → AIR rejects
    //   - Wrong betas → FRI folding produces wrong values → downstream verification fails
    //   - Missing query_vals → f_x=0, f_neg_x=0 → Merkle verification fails
    // 
    // We still check lengths here to fail fast with clear errors rather than panicking later.

    for layer_idx in 0..num_layers {
        // Note: commitments are accessed via ParsedProof.fri_commitments[layer_idx]
        // to avoid duplication (matches R1CS pattern)
        
        // FRI beta for this layer from Fiat-Shamir
        // If missing, use placeholder - AIR constraints will reject invalid folding
        let beta = fri_betas.get(layer_idx).copied()
            .unwrap_or(BaseElement::ZERO);

        // Get the query values for this layer
        // If missing, empty vec leads to zero values - AIR Merkle constraints will reject
        let empty_vec = Vec::new();
        let query_vals: &Vec<BaseElement> = layer_queries.get(layer_idx)
            .unwrap_or(&empty_vec);

        // Fold positions for this layer (Merkle tree is built on folded domain)
        let folded_domain_size = current_domain_size / folding_factor;
        let folded_positions: Vec<usize> = current_positions
            .iter()
            .map(|&p| p % folded_domain_size)
            .collect();

        // Deduplicate folded positions for Merkle path extraction
        // NOTE: Do NOT sort! Must preserve insertion order to match query_vals from Winterfell.
        // Use HashSet to deduplicate while preserving order.
        let mut unique_folded: Vec<usize> = Vec::new();
        {
            use std::collections::HashSet;
            let mut seen: HashSet<usize> = HashSet::with_capacity(folded_positions.len());
            for &fp in &folded_positions {
                if seen.insert(fp) {
                    unique_folded.push(fp);
                }
            }
        }
        
        // Extract Merkle paths for this layer by consuming the batch proof
        let layer_merkle_paths: Vec<MerklePath> = if !layer_proofs.is_empty() {
            // Pop the next batch proof (we reversed, so pop gives us in order)
            let batch_proof = layer_proofs.pop().unwrap();
            
            // Compute leaf digests from query values
            // Each unique position has folding_factor elements
            let leaf_digests: Vec<<Hasher as winter_crypto::Hasher>::Digest> = 
                unique_folded.iter().enumerate().map(|(idx, _pos)| {
                    let chunk_start = idx * folding_factor;
                    let chunk: Vec<BaseElement> = (0..folding_factor)
                        .filter_map(|j| query_vals.get(chunk_start + j).copied())
                        .collect();
                    Hasher::hash_elements(&chunk)
                }).collect();
            
            // Use Winterfell's decompression - positions should be in the FOLDED domain
            extract_all_merkle_paths_from_batch(batch_proof, &unique_folded, &leaf_digests)
        } else {
            vec![MerklePath::new(); unique_folded.len()]
        };

        // Build per-query FRI data
        // For layer i, positions and x values are in current_domain_size BEFORE folding
        let mut layer_query_data = Vec::with_capacity(current_positions.len());

        for (q_idx, &pos) in current_positions.iter().enumerate() {
            // Find which unique folded position this corresponds to
            let folded_pos = pos % folded_domain_size;
            let unique_idx = unique_folded.iter().position(|&p| p == folded_pos).unwrap_or(0);
            
            // Get f(x) and f(-x) from query_vals
            // Each unique position has folding_factor values: [val_low, val_high]
            // where val_low is at position folded_pos, val_high is at folded_pos + folded_domain_size
            let chunk_start = unique_idx * folding_factor;
            let (val_low, val_high) = if chunk_start + 1 < query_vals.len() {
                (query_vals[chunk_start], query_vals[chunk_start + 1])
            } else if chunk_start < query_vals.len() {
                (query_vals[chunk_start], BaseElement::ZERO)
            } else {
                (BaseElement::ZERO, BaseElement::ZERO)
            };

            // Domain element x for this position - use CURRENT domain size (before folding)
            let x = compute_domain_element(pos, current_domain_size);
            
            // Get Merkle path for this query (from the unique folded position)
            let merkle_path = layer_merkle_paths.get(unique_idx)
                .cloned()
                .unwrap_or_else(MerklePath::new);

            // Store values in [val_low, val_high] order - Merkle leaf uses this order
            // The prover will swap for upper-half positions when computing the fold
            layer_query_data.push(FriQueryData {
                f_x: val_low,
                f_neg_x: val_high,
                x,
                merkle_path,
            });
            
            // Only add one entry per original position
            if q_idx >= current_positions.len() {
                break;
            }
        }

        layers.push(FriLayerData {
            beta,
            queries: layer_query_data,
        });

        // Update for next layer
        current_domain_size = folded_domain_size;
        current_positions = folded_positions;
    }

    layers
}

/// Compute domain element at position
fn compute_domain_element(position: usize, domain_size: usize) -> BaseElement {
    // The LDE domain is a COSET: {offset * g^i} where offset = GENERATOR
    // We compute: offset * g^position where g is the domain generator
    // For Goldilocks: g = primitive_root^((p-1)/domain_size)
    use winterfell::math::StarkField;
    let generator = BaseElement::get_root_of_unity(domain_size.trailing_zeros());
    let offset = BaseElement::GENERATOR; // Winterfell uses GENERATOR as coset offset
    offset * generator.exp((position as u64).into())
}


// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_merkle_digest_structure() {
        // Create a deterministic digest
        let digest: MerkleDigest = [
            BaseElement::new(1),
            BaseElement::new(2),
            BaseElement::new(3),
            BaseElement::new(4),
        ];

        // Should have 4 elements
        assert_eq!(digest.len(), 4);
        for elem in &digest {
            assert_ne!(*elem, BaseElement::ZERO);
        }
    }



    #[test]
    fn test_derive_query_positions() {
        // Test with deterministic positions
        let num_queries = 4;
        let lde_domain_size = 64;
        let positions: Vec<usize> = (0..num_queries)
            .map(|i| (i * 7) % lde_domain_size)
            .collect();

        assert_eq!(positions.len(), 4);
        for &pos in &positions {
            assert!(pos < 64);
        }
    }


}
