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
use winter_crypto::{ElementHasher, Digest, RandomCoin};  // RandomCoin for DefaultRandomCoin::new
use crate::inner_stark_full::{
    FullStarkVerifierCircuit, AirParams, TraceQuery, CompQuery,
    FriLayerQueries, FriQuery,
};
use crate::gadgets::fri::FriTerminalKind;
use crate::outer_compressed::InnerFr;

extern crate alloc;  // For BTreeMap and Vec

/// Parse Winterfell proof into circuit-ready format
///
/// NO hooks needed - just parses the standard Proof struct!
/// 
/// Specifically for Goldilocks field (most common STARK configuration)
pub fn parse_proof_for_circuit<H, V>(
    proof: &Proof,
    pub_inputs_u64: Vec<u64>,
    air_params: AirParams,
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
    
    eprintln!("Parsing commitments: num_trace_segments={}, num_fri_layers={}", num_trace_segments, num_fri_layers);
    
    // Extract FS context seed for transcript alignment (Winterfell 0.13.x)
    use winter_math::ToElements;
    let fs_context_seed_gl: Vec<u64> = proof.context
        .to_elements()
        .into_iter()
        .map(|e: GL| e.as_int())
        .collect();
    
    let (trace_commitments, comp_commitment, fri_commitments) = proof.commitments
        .clone()
        .parse::<H>(num_trace_segments, num_fri_layers)
        .map_err(|e| {
            eprintln!("ERROR parsing commitments: {:?}", e);
            e
        })
        .expect("parse commitments");
    
    eprintln!("Parsed {} trace commitments, {} FRI commitments", 
        trace_commitments.len(), fri_commitments.len());
    
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
    
    eprintln!("Auto-detected comp_width={}", comp_width);
    
    // Compute query positions first (needed before parsing queries)
    let query_positions = derive_query_positions::<H>(
        &proof,
        &trace_commitments,
        &comp_commitment,
        &fri_commitments,
        lde_domain_size,
    );
    
    eprintln!("Derived {} query positions", query_positions.len());
    
    // Parse query openings with derived positions
    let trace_queries = parse_trace_queries::<H, V>(
        &proof.trace_queries,
        lde_domain_size,
        num_queries,
        air_params.trace_width,
        &query_positions,
    );
    let comp_queries = parse_comp_queries::<H, V>(
        &proof.constraint_queries,
        lde_domain_size,
        num_queries,
        comp_width,  // Use inferred width!
        &query_positions,
    );
    
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
    
    // OOD composition values
    let ood_comp: Vec<u64> = quotient_ood.current_row()
        .iter()
        .map(|e| e.as_int())
        .collect();
    
    // Compute OOD commitment (hash of OOD frame)
    let ood_commitment_le32 = compute_ood_commitment::<H>(&ood_trace_current, &ood_trace_next, &ood_comp);
    
    // Parse FRI proof (with positions that fold layer-by-layer)
    let fri_layers = parse_fri_layers::<H, V>(
        &proof.fri_proof,
        num_fri_layers,
        air_params.fri_folding_factor,
        lde_domain_size,
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
        ood_trace_current,
        ood_trace_next,
        ood_comp,
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
    let (batch_proof, table) = queries[0].clone()
        .parse::<E, H, V>(lde_domain_size, num_queries, values_per_query)
        .expect("parse trace queries");
    
    // Compute leaf digests (needed for path extraction)
    let leaves: Vec<H::Digest> = table.rows()
        .map(|row| H::hash_elements(row))
        .collect();
    
    // Extract individual Merkle paths from batch proof using actual positions
    let openings = extract_paths_from_batch(&batch_proof, &leaves, positions);
    
    table.rows().enumerate().map(|(idx, row)| {
        let values: Vec<u64> = row.iter().map(|e| e.as_int()).collect();
        
        // Get path for this query
        let (merkle_path, path_positions) = if idx < openings.len() {
            let (_leaf, siblings) = &openings[idx];
            let path_bytes: Vec<[u8; 32]> = siblings.iter().map(|d| {
                let bytes = d.as_bytes();
                bytes
            }).collect();
            
            // Compute position bits from index
            let mut pos_bits = Vec::with_capacity(siblings.len());
            let mut cur_idx = positions.get(idx).copied().unwrap_or(0);
            for _ in 0..siblings.len() {
                pos_bits.push((cur_idx & 1) == 1);
                cur_idx >>= 1;
            }
            
            (path_bytes, pos_bits)
        } else {
            (Vec::new(), Vec::new())
        };
        
        TraceQuery {
            values,
            merkle_path,
            path_positions,
        }
    }).collect()
}

/// Parse composition queries
fn parse_comp_queries<H, V>(
    queries: &winter_air::proof::Queries,
    lde_domain_size: usize,
    num_queries: usize,
    values_per_query: usize,
    positions: &[usize],
) -> Vec<CompQuery>
where
    H: ElementHasher<BaseField = GL>,
    V: winter_crypto::VectorCommitment<H, MultiProof = winter_crypto::BatchMerkleProof<H>>,
{
    type E = GL;
    let (batch_proof, table) = queries.clone()
        .parse::<E, H, V>(lde_domain_size, num_queries, values_per_query)
        .map_err(|e| {
            eprintln!("ERROR parsing comp queries: {:?}", e);
            eprintln!("  lde_domain_size={}, num_queries={}, values_per_query={}", 
                lde_domain_size, num_queries, values_per_query);
            e
        })
        .expect("parse comp queries");
    
    // Compute leaf digests
    let leaves: Vec<H::Digest> = table.rows()
        .map(|row| H::hash_elements(row))
        .collect();
    
    let openings = extract_paths_from_batch(&batch_proof, &leaves, positions);
    
    table.rows().enumerate().map(|(idx, row)| {
        let values: Vec<u64> = row.iter().map(|e| e.as_int()).collect();
        
        let (merkle_path, path_positions) = if idx < openings.len() {
            let (_leaf, siblings) = &openings[idx];
            let path_bytes: Vec<[u8; 32]> = siblings.iter().map(|d| d.as_bytes()).collect();
            
            let mut pos_bits = Vec::with_capacity(siblings.len());
            let mut cur_idx = positions.get(idx).copied().unwrap_or(0);
            for _ in 0..siblings.len() {
                pos_bits.push((cur_idx & 1) == 1);
                cur_idx >>= 1;
            }
            
            (path_bytes, pos_bits)
        } else {
            (Vec::new(), Vec::new())
        };
        
        CompQuery {
            values,
            merkle_path,
            path_positions,
        }
    }).collect()
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
    
    // Parse all FRI layers
    let (layer_queries, layer_proofs) = fri_proof.clone()
        .parse_layers::<E, H, V>(initial_domain_size, folding_factor)
        .unwrap_or_else(|_| (Vec::new(), Vec::new()));
    
    // Convert to our format
    let mut result = Vec::with_capacity(num_layers);
    
    // Positions fold layer-by-layer: pos_next = pos_current >> (log2(folding_factor))
    let fold_shift = (folding_factor as f64).log2() as usize;  // For binary FRI, this is 1
    let mut layer_positions = main_query_positions.to_vec();
    
    for (_layer_idx, (query_vals, batch_proof)) in layer_queries.iter().zip(&layer_proofs).enumerate() {
        // Fold positions for this layer
        layer_positions = layer_positions.iter().map(|&p| p >> fold_shift).collect();
        let mut folded_positions = layer_positions.clone();
        folded_positions.sort_unstable();
        folded_positions.dedup();
        
        // query_vals is Vec<E> with folding_factor elements per query
        let num_queries_this_layer = query_vals.len() / folding_factor;
        
        // Compute leaf digests for this layer
        let leaves: Vec<H::Digest> = query_vals.chunks(folding_factor)
            .map(|chunk| H::hash_elements(chunk))
            .collect();
        
        // Use folded positions
        let positions = &folded_positions;
        
        // Extract paths from batch proof
        let openings = extract_paths_from_batch(batch_proof, &leaves, &positions);
        
        // Build per-query FRI data
        let mut queries = Vec::with_capacity(num_queries_this_layer);
        for (q_idx, chunk) in query_vals.chunks(folding_factor).enumerate() {
            let v_lo = if chunk.len() > 0 { chunk[0].as_int() } else { 0 };
            let v_hi = if chunk.len() > 1 { chunk[1].as_int() } else { 0 };
            
            let (merkle_path, path_positions) = if q_idx < openings.len() {
                let (_leaf, siblings) = &openings[q_idx];
                let path_bytes: Vec<[u8; 32]> = siblings.iter().map(|d| d.as_bytes()).collect();
                
                // Compute position bits from ACTUAL folded position
                let mut pos_bits = Vec::with_capacity(siblings.len());
                let actual_pos = positions.get(q_idx).copied().unwrap_or(0);
                let mut cur_idx = actual_pos;
                for _ in 0..siblings.len() {
                    pos_bits.push((cur_idx & 1) == 1);
                    cur_idx >>= 1;
                }
                
                (path_bytes, pos_bits)
            } else {
                (Vec::new(), Vec::new())
            };
            
            queries.push(FriQuery {
                v_lo,
                v_hi,
                merkle_path,
                path_positions,
            });
        }
        
        result.push(FriLayerQueries { queries });
    }
    
    result
}

/// Compute OOD commitment (hash of OOD frame)
fn compute_ood_commitment<H: ElementHasher<BaseField = GL>>(
    ood_trace_current: &[u64],
    ood_trace_next: &[u64],
    ood_comp: &[u64],
) -> [u8; 32] {
    use winter_crypto::Digest;
    
    // Hash OOD frame values using RPO
    let mut elements = Vec::new();
    for &v in ood_trace_current {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_trace_next {
        elements.push(GL::try_from(v).unwrap_or(GL::ZERO));
    }
    for &v in ood_comp {
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

/// Derive query positions by replicating Winterfell's exact FS transcript
fn derive_query_positions<H: ElementHasher<BaseField = GL>>(
    proof: &Proof,
    trace_commitments: &[H::Digest],
    comp_commitment: &H::Digest,
    fri_commitments: &[H::Digest],
    lde_domain_size: usize,
) -> Vec<usize> {
    use winter_crypto::{DefaultRandomCoin};
    use winter_math::ToElements;
    
    // 1. Initialize coin with context elements
    let seed_elements: Vec<GL> = proof.context.to_elements();
    let mut public_coin = DefaultRandomCoin::<H>::new(&seed_elements);
    
    // 2. Reseed with trace commitment
    public_coin.reseed(trace_commitments[0]);
    
    // 3. Draw constraint coefficients
    for _ in 0..proof.context.num_constraints() {
        let _ = public_coin.draw::<GL>();
    }
    
    // 4. Reseed with composition commitment
    public_coin.reseed(*comp_commitment);
    
    // 5. Draw z (OOD point)
    let _ = public_coin.draw::<GL>();
    
    // 6. Reseed with FRI commitments and draw betas
    for fri_c in fri_commitments {
        public_coin.reseed(*fri_c);
        let _ = public_coin.draw::<GL>();
    }
    
    // 7. Draw query positions with PoW nonce
    let mut positions = public_coin.draw_integers(
        proof.options().num_queries(),
        lde_domain_size,
        proof.pow_nonce,
    ).unwrap_or_else(|_| Vec::new());
    
    // 8. Deduplicate
    positions.sort_unstable();
    positions.dedup();
    
    positions
}

/// Extract individual Merkle paths from batch proof
///
/// Adapted from winterfell-pvugc/verifier/src/channel.rs::compute_openings_from_batch
fn extract_paths_from_batch<H: ElementHasher<BaseField = GL>>(
    proof: &winter_crypto::BatchMerkleProof<H>,
    leaves: &[H::Digest],
    indexes: &[usize],
) -> Vec<(H::Digest, Vec<H::Digest>)> {
    use alloc::collections::BTreeMap;
    
    let depth = proof.depth as usize;
    let num_leaves = 1usize << depth;
    let offset = 1usize << depth;
    
    // Build partial tree map
    let mut partial_tree_map = BTreeMap::new();
    for (&i, leaf) in indexes.iter().zip(leaves.iter()) {
        partial_tree_map.insert(i + offset, *leaf);
    }
    
    // Build index map
    let mut map = BTreeMap::new();
    for (pos, &idx) in indexes.iter().enumerate() {
        if idx >= num_leaves { return Vec::new(); }
        map.insert(idx, pos);
    }
    
    // Normalize indexes (set even indices for sibling pairs)
    let mut norm: Vec<usize> = Vec::new();
    for &idx in indexes {
        let even = idx - (idx & 1);
        if norm.last().copied() != Some(even) { norm.push(even); }
    }
    if norm.len() != proof.nodes.len() { return Vec::new(); }
    
    // Compute parents layer by layer
    let mut next_indexes: Vec<usize> = Vec::new();
    let mut proof_pointers: Vec<usize> = vec![0; norm.len()];
    let mut buf = [H::Digest::default(); 2];
    
    for (i, index) in norm.iter().copied().enumerate() {
        match map.get(&index) {
            Some(&i1) => {
                if leaves.len() <= i1 { return Vec::new(); }
                buf[0] = leaves[i1];
                match map.get(&(index + 1)) {
                    Some(&i2) => {
                        if leaves.len() <= i2 { return Vec::new(); }
                        buf[1] = leaves[i2];
                        proof_pointers[i] = 0;
                    }
                    None => {
                        if proof.nodes[i].is_empty() { return Vec::new(); }
                        buf[1] = proof.nodes[i][0];
                        proof_pointers[i] = 1;
                    }
                }
            }
            None => {
                if proof.nodes[i].is_empty() { return Vec::new(); }
                buf[0] = proof.nodes[i][0];
                match map.get(&(index + 1)) {
                    Some(&i2) => {
                        if leaves.len() <= i2 { return Vec::new(); }
                        buf[1] = leaves[i2];
                    }
                    None => return Vec::new(),
                }
                proof_pointers[i] = 1;
            }
        }
        let parent = H::merge(&buf);
        partial_tree_map.insert(offset + index, buf[0]);
        partial_tree_map.insert((offset + index) ^ 1, buf[1]);
        let parent_index = (offset + index) >> 1;
        partial_tree_map.insert(parent_index, parent);
        next_indexes.push(parent_index);
    }
    
    // Iterate up the tree
    for _ in 1..depth {
        let cur = next_indexes.clone();
        next_indexes.clear();
        let mut i = 0;
        while i < cur.len() {
            let node_index = cur[i];
            let sibling_index = node_index ^ 1;
            let sibling = if i + 1 < cur.len() && cur[i + 1] == sibling_index {
                i += 1;
                partial_tree_map.get(&sibling_index).copied().unwrap_or_default()
            } else {
                let pointer = proof_pointers[i];
                if proof.nodes[i].len() <= pointer { return Vec::new(); }
                proof_pointers[i] += 1;
                proof.nodes[i][pointer]
            };
            partial_tree_map.insert(node_index ^ 1, sibling);
            let node = partial_tree_map.get(&node_index).copied().unwrap_or_default();
            let parent = if node_index & 1 != 0 {
                H::merge(&[sibling, node])
            } else {
                H::merge(&[node, sibling])
            };
            let parent_index = node_index >> 1;
            partial_tree_map.insert(parent_index, parent);
            next_indexes.push(parent_index);
            i += 1;
        }
    }
    
    // Extract per-index proofs from partial tree
    let mut result = Vec::with_capacity(indexes.len());
    for &idx in indexes {
        let mut cur = idx + offset;
        let leaf = partial_tree_map.get(&cur).copied().unwrap_or_default();
        let mut path = Vec::new();
        while cur > 1 {
            let sib_idx = cur ^ 1;
            let sib = partial_tree_map.get(&sib_idx).copied().unwrap_or_default();
            path.push(sib);
            cur >>= 1;
        }
        result.push((leaf, path));
    }
    
    result
}

