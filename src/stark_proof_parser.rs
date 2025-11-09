//! Parse Winterfell STARK Proof into Circuit-Ready Format
//!
//! This module extracts data from a standard Winterfell Proof struct
//! without requiring any hooks or modifications to Winterfell.
//!
//! The Proof struct already contains everything we need:
//! - Commitments (trace, composition, FRI)
//! - Query openings with Merkle batch proofs
//! - OOD frame
//! - FRI layer proofs

use winterfell::Proof;
use winter_math::FieldElement;
use winter_math::fields::f64::BaseElement as GL;  // Goldilocks field
use winter_crypto::{ElementHasher, Digest};
use crate::inner_stark_full::{
    FullStarkVerifierCircuit, AirParams, TraceQuery, CompQuery,
    FriLayerQueries, FriQuery,
};
use crate::gadgets::fri::FriTerminalKind;
use crate::outer_compressed::InnerFr;

extern crate alloc;  // For BTreeMap and Vec

pub fn parse_proof_for_circuit_with_query_positions<H, V>(
    proof: &Proof,
    pub_inputs_u64: Vec<u64>,
    air_params: AirParams,
    query_positions: Vec<usize>,
) -> FullStarkVerifierCircuit
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    parse_proof_impl::<H, V>(proof, pub_inputs_u64, air_params, query_positions)
}

/// Internal implementation
fn parse_proof_impl<H, V>(
    proof: &Proof,
    pub_inputs_u64: Vec<u64>,
    air_params: AirParams,
    query_positions: Vec<usize>,
) -> FullStarkVerifierCircuit
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    // Use GL (Goldilocks BaseElement) as E
    type E = GL;
    // Extract parameters from proof (don't assume!)
    let num_trace_segments = proof.context.trace_info().num_segments();
    let num_fri_layers = air_params.fri_num_layers;
    let lde_domain_size = air_params.trace_len * air_params.lde_blowup;
    // Use actual number of unique queries from proof (after deduplication)
    let num_queries = proof.num_unique_queries as usize;
    
    
    // Extract FS context seed for transcript alignment (Winterfell 0.13.x)
    // Per Winterfell verifier/lib.rs:100-101: seed with context + public inputs!
    use winter_math::ToElements;
    let mut fs_context_seed_gl: Vec<u64> = proof.context
        .to_elements()
        .into_iter()
        .map(|e: GL| e.as_int())
        .collect();
    
    // CRITICAL: Append public inputs to match Winterfell's initialization
    fs_context_seed_gl.extend(pub_inputs_u64.iter().copied());
    
    let (trace_commitments, comp_commitment, fri_commitments) = proof.commitments
        .clone()
        .parse::<H>(num_trace_segments, num_fri_layers)
        .map_err(|e| {
            
            e
        })
        .expect("parse commitments");
    
    
    // Convert to 32-byte arrays
    use winter_crypto::Digest;
    
    let trace_commitment_le32: [u8; 32] = trace_commitments[0].as_bytes();
    let comp_commitment_le32: [u8; 32] = comp_commitment.as_bytes();
    let fri_commitments_le32: Vec<[u8; 32]> = fri_commitments.iter()
        .map(|c| c.as_bytes())
        .collect();
    
    // Infer composition width by trying to parse with width=1, then width=2, etc.
    // The correct width will parse without errors
    let mut comp_width = 1;
    for width in 1..=8 {
        let test_parse = proof.constraint_queries.clone()
            .parse::<E, H, V>(lde_domain_size, num_queries, width);
        if test_parse.is_ok() {
            comp_width = width;
            break;
        }
    }
    
    
    // Use provided query positions
    
    // Parse query openings
    // Use proof.num_unique_queries as the authoritative count (what's actually in the proof)
    // Truncate query_positions to match if we derived too many
    let actual_num_queries = proof.num_unique_queries as usize;
    let positions_for_parsing = if query_positions.len() > actual_num_queries {
        
        &query_positions[..actual_num_queries]
    } else {
        &query_positions[..]
    };
    
    let trace_queries = parse_trace_queries::<H, V>(
        &proof.trace_queries,
        lde_domain_size,
        actual_num_queries,
        air_params.trace_width,
        positions_for_parsing,
    );
    // Also capture trace batch multiproof for circuit batch verification
    let (trace_batch_proof, _trace_table) = proof.trace_queries[0].clone()
        .parse::<E, H, V>(lde_domain_size, actual_num_queries, air_params.trace_width)
        .expect("parse trace batch");
    let trace_batch_nodes: Vec<Vec<[u8;32]>> = trace_batch_proof.nodes.iter()
        .map(|v| v.iter().map(|d| d.as_bytes()).collect())
        .collect();
    let trace_batch_depth: u8 = trace_batch_proof.depth;
    let trace_batch_indexes: Vec<usize> = positions_for_parsing.to_vec();
    let comp_queries = parse_comp_queries::<H, V>(
        &proof.constraint_queries,
        lde_domain_size,
        actual_num_queries,
        comp_width,  // Use inferred width!
        positions_for_parsing,
        comp_commitment,
    );
    // Capture composition batch multiproof
    let (comp_batch_proof, _comp_table) = proof.constraint_queries.clone()
        .parse::<E, H, V>(lde_domain_size, actual_num_queries, comp_width)
        .expect("parse comp batch");
    let comp_batch_nodes: Vec<Vec<[u8;32]>> = comp_batch_proof.nodes.iter()
        .map(|v| v.iter().map(|d| d.as_bytes()).collect())
        .collect();
    let comp_batch_depth: u8 = comp_batch_proof.depth;
    let comp_batch_indexes: Vec<usize> = positions_for_parsing.to_vec();
    
    // Parse OOD frame
    let main_trace_width = air_params.trace_width;
    let aux_trace_width = proof.context.trace_info().aux_segment_width();
    let num_quotients = comp_width;  // Use inferred comp_width!
    
    let (trace_ood, quotient_ood) = proof.ood_frame.clone()
        .parse::<E>(main_trace_width, aux_trace_width, num_quotients)
        .expect("parse OOD frame");
    
    let ood_trace_current: Vec<u64> = trace_ood.current_row()
        .iter()
        .map(|e| e.as_int())
        .collect();
    let ood_trace_next: Vec<u64> = trace_ood.next_row()
        .iter()
        .map(|e| e.as_int())
        .collect();
    
    // OOD composition values (at both z and z*g for LINEAR batching!)
    let ood_comp: Vec<u64> = quotient_ood.current_row()
        .iter()
        .map(|e| e.as_int())
        .collect();
    let ood_comp_next: Vec<u64> = quotient_ood.next_row()
        .iter()
        .map(|e| e.as_int())
        .collect();
    
    // Compute OOD commitment (hash of OOD frame - includes both current and next!)
    let ood_commitment_le32 = compute_ood_commitment::<H>(&ood_trace_current, &ood_trace_next, &ood_comp, &ood_comp_next);
    
    // Parse FRI proof (with positions that fold layer-by-layer)
    // NOTE: Pass full LDE domain size - folding happens INSIDE parse_fri_layers
    let fri_layers = parse_fri_layers::<H, V>(
        &proof.fri_proof,
        num_fri_layers,
        air_params.fri_folding_factor,
        lde_domain_size,  // Full LDE domain, NOT pre-divided
        &query_positions,  // Pass main query positions
    );
    
    // Parse FRI remainder coefficients depending on terminal kind
    let fri_remainder_coeffs: Vec<u64> = match air_params.fri_terminal {
        FriTerminalKind::Poly { .. } => {
            // Parse remainder from FriProof (coefficients in GL), low->high order
            let coeffs_gl: Vec<E> = proof.fri_proof.clone()
                .parse_remainder::<E>()
                .unwrap_or_else(|_| Vec::new());
            coeffs_gl.iter().map(|e| e.as_int()).collect()
        }
        FriTerminalKind::Constant => Vec::new(),
    };
    
    // Compute statement hash (including position commitment!)
    let statement_hash = compute_statement_hash(
        &trace_commitment_le32,
        &comp_commitment_le32,
        &fri_commitments_le32,
        &ood_commitment_le32,
        &pub_inputs_u64,
        &query_positions,  // Bind positions to prevent adversarial selection!
    );
    
    FullStarkVerifierCircuit {
        statement_hash,
        stark_pub_inputs: pub_inputs_u64,
        fs_context_seed_gl,
        trace_commitment_le32,
        comp_commitment_le32,
        fri_commitments_le32,
        ood_commitment_le32,
        query_positions,
        trace_queries,
        comp_queries,
        trace_batch_nodes,
        trace_batch_depth,
        trace_batch_indexes,
        comp_batch_nodes,
        comp_batch_depth,
        comp_batch_indexes,
        ood_trace_current,
        ood_trace_next,
        ood_comp,
        ood_comp_next,
        fri_layers,
        fri_remainder_coeffs,
        air_params,
    }
}

/// Parse trace queries from Winterfell format
fn parse_trace_queries<H, V>(
    queries: &[winter_air::proof::Queries],
    lde_domain_size: usize,
    num_queries: usize,
    values_per_query: usize,
    positions: &[usize],
) -> Vec<TraceQuery>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;
    if queries.is_empty() {
        return Vec::new();
    }
    
    // Parse the queries (returns batch proof + values table)
    
    let (_batch_proof, table) = queries[0].clone()
        .parse::<E, H, V>(lde_domain_size, num_queries, values_per_query)
        .expect("parse trace queries");
    
    
    // Snapshot rows once to avoid iterator-order surprises
    let rows_vec: Vec<Vec<E>> = table.rows()
        .map(|row| row.to_vec())
        .collect();
    
    // Compute leaf digests (needed for path extraction)
    let leaves: Vec<H::Digest> = rows_vec.iter()
        .map(|row| H::hash_elements(row))
        .collect();
    
    // Check normalization count
    let mut norm_test: Vec<usize> = Vec::new();
    for &p in positions {
        let even = p - (p & 1);
        if norm_test.last().copied() != Some(even) {
            norm_test.push(even);
        }
    }
    
    // Verify positions match leaves
    if positions.len() != leaves.len() {
        panic!(
            "Query position mismatch: provided {} positions but proof has {} leaves. \
             This indicates the query positions were not derived correctly from the AIR instance.",
            positions.len(), leaves.len()
        );
    }
    let _idxs: Vec<usize> = positions.iter().cloned().collect();
    
    // Skip per-path extraction; batch verification is enforced in-circuit

    // Align openings by row index
    let aligned_openings: Vec<(Vec<H::Digest>, usize)> = Vec::new();

    rows_vec
        .into_iter()
        .enumerate()
        .map(|(idx, row)| {
        let values: Vec<u64> = row.iter().map(|e| e.as_int()).collect();
        
            // Use aligned openings directly by row index
            let (sib_vec, pos_actual) = aligned_openings.get(idx).cloned().unwrap_or((Vec::new(), 0));

            // Bits: current-is-right, LSB-first
            let mut tmp = pos_actual;
            let mut path_positions: Vec<bool> = Vec::with_capacity(sib_vec.len());
            for _ in 0..sib_vec.len() { path_positions.push((tmp & 1) == 1); tmp >>= 1; }

            // Convert siblings to bytes for circuit
            let merkle_path: Vec<[u8; 32]> = Vec::new();
        
        TraceQuery {
            values,
            merkle_path,
            path_positions,
        }
        })
        .collect()
}

/// Parse composition queries
fn parse_comp_queries<H, V>(
    queries: &winter_air::proof::Queries,
    lde_domain_size: usize,
    num_queries: usize,
    values_per_query: usize,
    positions: &[usize],
    _comp_root: H::Digest,
) -> Vec<CompQuery>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;
    let (batch_proof, table) = queries.clone()
        .parse::<E, H, V>(lde_domain_size, num_queries, values_per_query)
        .map_err(|e| {
            
            e
        })
        .expect("parse comp queries");
    
    // Snapshot rows once to avoid iterator-order surprises
    let rows_vec: Vec<Vec<E>> = table.rows()
        .map(|row| row.to_vec())
        .collect();
    // Compute leaf digests
    let leaves: Vec<H::Digest> = rows_vec.iter()
        .map(|row| H::hash_elements(row))
        .collect();
    
    // Use sorted-unique positions modulo tree size, length = leaves.len()
    let tree_num_leaves: usize = 1usize << (batch_proof.depth as usize);
    let mut idxs_aligned: Vec<usize> = positions.iter().map(|&p| p % tree_num_leaves).collect();
    idxs_aligned.truncate(leaves.len());
    // Skip per-path extraction for comp as well; batch verification is enforced in-circuit

    // Align openings by row index
    let aligned_openings: Vec<(Vec<H::Digest>, usize)> = Vec::new();

    rows_vec
        .into_iter()
        .enumerate()
        .map(|(idx, row)| {
        let values: Vec<u64> = row.iter().map(|e| e.as_int()).collect();
        
            // Use aligned openings directly by row index
            let (sib_vec, pos_actual) = aligned_openings.get(idx).cloned().unwrap_or((Vec::new(), 0));

            // Bits: current-is-right, LSB-first
            let mut tmp = pos_actual;
            let mut path_positions: Vec<bool> = Vec::with_capacity(sib_vec.len());
            for _ in 0..sib_vec.len() { path_positions.push((tmp & 1) == 1); tmp >>= 1; }

            // Convert siblings to bytes for circuit
            let merkle_path: Vec<[u8; 32]> = Vec::new();
        
        CompQuery {
            values,
            merkle_path,
            path_positions,
        }
        })
        .collect()
}

/// Parse FRI layers from FRI proof
fn parse_fri_layers<H, V>(
    fri_proof: &winter_fri::FriProof,
    num_layers: usize,
    folding_factor: usize,
    initial_domain_size: usize,
    main_query_positions: &[usize],  // Query positions from main DEEP queries
) -> Vec<FriLayerQueries>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;
    
    // Get num_partitions from proof
    let _num_partitions = fri_proof.num_partitions();
    
    // Parse all FRI layers
    let (layer_queries, layer_proofs) = fri_proof.clone()
        .parse_layers::<E, H, V>(initial_domain_size, folding_factor)
        .unwrap_or_else(|_| (Vec::new(), Vec::new()));
    
    // Convert to our format
    let mut result = Vec::with_capacity(num_layers);
    
    // Positions fold layer-by-layer: pos_next = pos_current >> (log2(folding_factor))
    let _fold_shift = (folding_factor as f64).log2() as usize;  // For binary FRI, this is 1
    let mut layer_positions = main_query_positions.to_vec();
    let mut current_domain_size = initial_domain_size;
    
    
    for (_layer_idx, (query_vals, batch_proof)) in layer_queries.iter().zip(&layer_proofs).enumerate() {
        // Fold positions for this layer
        // NOTE: Fold using CURRENT domain, then divide (matches Winterfell line 256-257, 303-304)
        let folded_domain_size = current_domain_size / folding_factor;
        layer_positions = layer_positions.iter().map(|&p| p % folded_domain_size).collect();
        current_domain_size = folded_domain_size;
        
        // Deduplicate WITHOUT sorting - matches Winterfell's fold_positions
        // This preserves insertion order to match query_vals from proof
        let mut folded_positions = Vec::new();
        for &pos in &layer_positions {
            if !folded_positions.contains(&pos) {
                folded_positions.push(pos);
            }
        }
        
        // query_vals is Vec<E> with folding_factor elements per query
        let _num_queries_this_layer = query_vals.len() / folding_factor;
        
        
        
        // Build per-query FRI data (batch-only; no per-path Merkle data)
        // - query_vals has values for UNIQUE folded positions only
        // - We need to expand back to values for ALL original layer_positions
        // - Multiple original positions may map to the same folded position
        let mut folded_data: std::collections::HashMap<usize, Vec<u64>> = 
            std::collections::HashMap::new();
        
        for (unique_idx, &folded_pos) in folded_positions.iter().enumerate() {
            // Get values for this unique position
            let chunk_start = unique_idx * folding_factor;
            let chunk_end = (chunk_start + folding_factor).min(query_vals.len());
            let values: Vec<u64> = query_vals[chunk_start..chunk_end].iter().map(|e| e.as_int()).collect();
            folded_data.insert(folded_pos, values);
        }
        
        // Now create one FriQuery per original layer_position
        let mut queries = Vec::with_capacity(layer_positions.len());
        let row_length = current_domain_size;
        
        for (_pos_idx, &original_pos) in layer_positions.iter().enumerate() {
            // Find which folded position this original position maps to
            let folded_pos = original_pos % row_length;
            let values = folded_data.get(&folded_pos)
                .expect(&format!("folded_pos {} not found in folded_data", folded_pos));
            
            // For FRI, we need both v_lo and v_hi from the committed values
            // (these come from the folding_factor elements at the folded position)
            let v_lo = values.get(0).copied().unwrap_or(0);
            let v_hi = values.get(1).copied().unwrap_or(0);
            
            queries.push(FriQuery { v_lo, v_hi });
        }
        
        // Collect unique values and batch nodes metadata for batch verification
        let unique_values: Vec<(u64, u64)> = folded_positions.iter()
            .filter_map(|fp| {
                if let Some(vals) = folded_data.get(fp) {
                    Some((vals.get(0).copied().unwrap_or(0), vals.get(1).copied().unwrap_or(0)))
                } else {
                    None
                }
            })
            .collect();
        let unique_indexes: Vec<usize> = folded_positions.clone();
        let batch_nodes: Vec<Vec<[u8; 32]>> = batch_proof.nodes.iter()
            .map(|v| v.iter().map(|d| d.as_bytes()).collect())
            .collect();
        let batch_depth: u8 = batch_proof.depth;
        
        result.push(FriLayerQueries { 
            queries,
            unique_indexes,
            unique_values,
            batch_nodes,
            batch_depth,
        });
    }
    
    result
}

/// Compute OOD commitment (hash of OOD frame)
fn compute_ood_commitment<H: ElementHasher<BaseField = GL>>(
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
    ood_comp_next: &[u64],
) -> [u8; 32] {
    use winter_crypto::Digest;
    
    // Hash OOD frame values - MATCH Winterfell's merge_ood_evaluations order
    // Per Winterfell source: [trace_current, constraint_current, trace_next, constraint_next]
    let mut elements = Vec::new();
    for &v in ood_trace_current {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_comp {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_trace_next {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_comp_next {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    
    let digest = H::hash_elements(&elements);
    digest.as_bytes()
}

/// Poseidon commit to positions (off-chain, matches in-circuit)
fn poseidon_commit_positions_offchain(positions: &[usize]) -> InnerFr {
    use ark_crypto_primitives::sponge::{CryptographicSponge, poseidon::PoseidonSponge};
    use crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    
    let mut sponge = PoseidonSponge::new(&POSEIDON377_PARAMS_T3_V1);
    for &pos in positions {
        let b = (pos as u64).to_le_bytes();
        let mut val = 0u64;
        for (i, &byte) in b.iter().enumerate() {
            val |= (byte as u64) << (8 * i);
        }
        sponge.absorb(&InnerFr::from(val));
    }
    sponge.squeeze_field_elements::<InnerFr>(1)[0]
}

/// Compute statement hash binding all public data (including positions)
fn compute_statement_hash(
    trace_root: &[u8; 32],
    comp_root: &[u8; 32],
    fri_roots: &[[u8; 32]],
    ood_commit: &[u8; 32],
    pub_inputs: &[u64],
    query_positions: &[usize],
) -> InnerFr {
    use ark_crypto_primitives::sponge::{CryptographicSponge};
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use crate::crypto::poseidon_fr377_t3::POSEIDON377_PARAMS_T3_V1;
    
    let mut hasher = PoseidonSponge::new(&POSEIDON377_PARAMS_T3_V1);
    
    // Helper: Convert 8 LE bytes to field element
    let bytes_to_fe = |chunk: &[u8]| -> InnerFr {
        let mut val = 0u64;
        for (i, &b) in chunk.iter().enumerate().take(8) {
            val |= (b as u64) << (i * 8);
        }
        InnerFr::from(val)
    };
    
    // Absorb all commitments
    for chunk in trace_root.chunks(8) {
        hasher.absorb(&bytes_to_fe(chunk));
    }
    for chunk in comp_root.chunks(8) {
        hasher.absorb(&bytes_to_fe(chunk));
    }
    for fri_root in fri_roots {
        for chunk in fri_root.chunks(8) {
            hasher.absorb(&bytes_to_fe(chunk));
        }
    }
    for chunk in ood_commit.chunks(8) {
        hasher.absorb(&bytes_to_fe(chunk));
    }
    
    // Absorb public inputs
    for pub_in in pub_inputs {
        hasher.absorb(&InnerFr::from(*pub_in));
    }
    
    // Use the *same* positions commitment as the circuit
    let pos_commit = poseidon_commit_positions_offchain(query_positions);
    hasher.absorb(&pos_commit);
    
    let hash = hasher.squeeze_field_elements::<InnerFr>(1);
    hash[0]
}