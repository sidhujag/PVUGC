//! PVUGC Operations on Outer Curve
//!
//! Thin wrappers that apply PVUGC column operations to the OUTER proof.
//! All PVUGC logic runs on BW6-761 (outer curve) which has constant-size right-legs.

use crate::arming::{ColumnArms, ColumnBases};
use crate::outer_compressed::{
    fr_inner_to_outer_for, DefaultCycle, InnerFr, InnerScalar, OuterCircuit, OuterE, OuterFr,
    OuterScalar, RecursionCycle, InnerVk, InnerProof,
};
use crate::ppe::PvugcVk;
use crate::prover_lean::{prove_lean_with_randomizers, LeanProvingKey};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, PrimeField, Zero, One};
use ark_groth16::{Groth16, ProvingKey as Groth16PK, VerifyingKey as Groth16VK};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::time::Instant;
use rayon::prelude::*;

/// Build PVUGC VK and Lean PK from the OUTER proving key.
/// 
/// IMPORTANT: `sample_inner_proof` must be a VALID inner Groth16 proof (for any statement).
/// This is needed because the q_const computation requires the same witness sparsity pattern
/// as real proofs. Using a dummy proof with zeros causes the H-term computation to have
/// a completely different sparsity pattern, leading to incorrect q_const values.
/// 
/// The sample proof can be for any valid inner statement - it doesn't need to match
/// the statements you'll actually prove later. It just needs to have non-zero curve points
/// so the witness structure matches real proofs.
pub fn build_pvugc_setup_from_pk_for<C: RecursionCycle>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    sample_inner_proof: &InnerProof<C>,
) -> (PvugcVk<C::OuterE>, LeanProvingKey<C::OuterE>) {
    let start = Instant::now();
    println!("[Setup] Starting PVUGC Setup from PK...");
    
    let n_inner_inputs = vk_inner.gamma_abc_g1.len() - 1;
    println!(
        "[Setup] Inner public inputs (packed outer instances): {}",
        n_inner_inputs
    );

    // Sanitize cycle name for filename
    let safe_name = C::name().replace("/", "_").replace(" ", "_");
    let cache_path = format!("pvugc_setup_{}.bin", safe_name);

    let (lean_pk, q_points) = if std::path::Path::new(&cache_path).exists() {
        println!("[Setup] Found cached setup at {}, loading...", cache_path);
        let file = File::open(&cache_path).expect("failed to open cached setup");
        let reader = BufReader::with_capacity(1024 * 1024 * 1024, file); // 1GB buffer
        let (pk, q_points): (LeanProvingKey<C::OuterE>, Vec<<C::OuterE as Pairing>::G1Affine>) = 
            CanonicalDeserialize::deserialize_uncompressed_unchecked(reader)
            .expect("failed to deserialize setup");
        println!("[Setup] Cached setup loaded in {:?}", start.elapsed());
        (pk, q_points)
    } else {
        println!("[Setup] No cache found. Computing witness bases...");
        let h_query_wit = compute_witness_bases::<C>(pk_outer, vk_inner, n_inner_inputs);
        println!("[Setup] Witness Bases Computed in {:?}", start.elapsed());

        let lean_pk = LeanProvingKey {
            vk: pk_outer.vk.clone(),
            beta_g1: pk_outer.beta_g1,
            delta_g1: pk_outer.delta_g1,
            a_query: pk_outer.a_query.clone(),
            b_g1_query: pk_outer.b_g1_query.clone(),
            b_g2_query: pk_outer.b_g2_query.clone(),
            h_query_wit,
            l_query: pk_outer.l_query.clone(),
        };

        println!(
            "[Setup] Computing q_points (running {} proofs)...",
            n_inner_inputs + 1
        );
        let q_points =
            compute_q_const_points_from_gap::<C>(pk_outer, &lean_pk, vk_inner, n_inner_inputs, sample_inner_proof);
        println!("[Setup] q_points computed in {:?}", start.elapsed());
        println!("[Setup] Serializing setup to {}...", cache_path);
        let file = File::create(&cache_path).expect("failed to create cache file");
        let mut writer = BufWriter::with_capacity(1024 * 1024 * 1024, file); // 1GB buffer
        // Serialize as tuple - need owned values for CanonicalSerialize
        (lean_pk.clone(), q_points.clone()).serialize_uncompressed(&mut writer).expect("failed to serialize setup");
        writer.flush().expect("failed to flush buffer");
        (lean_pk, q_points)
    };

    let pvugc_vk = PvugcVk::new_with_all_witnesses_isolated(
        pk_outer.vk.beta_g2,
        pk_outer.vk.delta_g2,
        pk_outer.b_g2_query.clone(),
        q_points,
    );
    
    println!("[Setup] Complete.");
    (pvugc_vk, lean_pk)
}

pub fn build_pvugc_vk_outer_from_pk_for<C: RecursionCycle>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    sample_inner_proof: &InnerProof<C>,
) -> PvugcVk<C::OuterE> {
    build_pvugc_setup_from_pk_for::<C>(pk_outer, vk_inner, sample_inner_proof).0
}

pub fn build_pvugc_vk_outer_from_pk(
    pk_outer: &Groth16PK<OuterE>,
    vk_inner: &InnerVk<DefaultCycle>,
    sample_inner_proof: &InnerProof<DefaultCycle>,
) -> PvugcVk<OuterE> {
    build_pvugc_vk_outer_from_pk_for::<DefaultCycle>(pk_outer, vk_inner, sample_inner_proof)
}

pub fn build_column_bases_outer_for<C: RecursionCycle>(
    pvugc_vk: &PvugcVk<C::OuterE>,
    vk_outer: &Groth16VK<C::OuterE>,
    public_inputs_outer: &[OuterScalar<C>],
) -> ColumnBases<C::OuterE> {
    crate::api::OneSidedPvugc::build_column_bases(pvugc_vk, vk_outer, public_inputs_outer)
        .expect("outer statement should satisfy PVUGC invariants")
}

pub fn build_column_bases_outer(
    pvugc_vk: &PvugcVk<OuterE>,
    vk_outer: &Groth16VK<OuterE>,
    public_inputs_outer: &[OuterFr],
) -> ColumnBases<OuterE> {
    build_column_bases_outer_for::<DefaultCycle>(pvugc_vk, vk_outer, public_inputs_outer)
}

fn compute_witness_bases<C: RecursionCycle>(
    pk: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    n_inner_inputs: usize,
) -> Vec<(u32, u32, <C::OuterE as Pairing>::G1Affine)> {
    let start = Instant::now();
    println!("[Quotient] Synthesizing Circuit...");

    let dummy_x = vec![InnerScalar::<C>::from(0u64); n_inner_inputs];
    let dummy_proof = crate::outer_compressed::InnerProof::<C> {
        a: Default::default(),
        b: Default::default(),
        c: Default::default(),
    };
    let circuit = OuterCircuit::<C>::new(vk_inner.clone(), dummy_x, dummy_proof);

    let cs = ConstraintSystem::<OuterScalar<C>>::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);
    circuit
        .generate_constraints(cs.clone())
        .expect("synthesis failed");
    cs.finalize();
    let matrices = cs.to_matrices().expect("matrix extraction failed");

    let domain = GeneralEvaluationDomain::<OuterScalar<C>>::new(cs.num_constraints())
        .or_else(|| GeneralEvaluationDomain::<OuterScalar<C>>::new(cs.num_constraints().next_power_of_two()))
        .expect("domain creation failed");
    let domain_size = domain.size();

    println!(
        "[Quotient] Matrix extracted ({} constraints). Domain size: {}. Time: {:?}",
        cs.num_constraints(),
        domain_size,
        start.elapsed()
    );

    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let mut col_a = vec![Vec::new(); num_vars];
    let mut col_b = vec![Vec::new(); num_vars];

    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_a[col].push((row, val));
            }
        }
    }
    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(val, col) in terms {
                col_b[col].push((row, val));
            }
        }
    }

    println!("[Quotient] Converting SRS to Lagrange Basis (Parallel Group IFFT)....");
    let fft_start = Instant::now();
    let mut h_query_proj: Vec<_> = pk.h_query.iter().map(|p| p.into_group()).collect();
    if h_query_proj.len() < domain_size {
        h_query_proj.resize(domain_size, <C::OuterE as Pairing>::G1::zero());
    } else {
        h_query_proj.truncate(domain_size);
    }
    let mut lagrange_srs = h_query_proj;
    parallel_ifft_g1(&mut lagrange_srs, &domain);
    let lagrange_srs: Vec<_> = lagrange_srs.into_par_iter().map(|p| p.into_affine()).collect();
    println!("[Quotient] Lagrange SRS computed in {:?}", fft_start.elapsed());

    let num_pub = cs.num_instance_variables();
    let mut vars_a = HashSet::new();
    let mut vars_b = HashSet::new();
    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms { vars_a.insert(col); }
        }
    }
    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms { vars_b.insert(col); }
        }
    }

    let mut active_pairs = HashSet::new();

    for &i in &vars_a {
        for &j in &vars_b {
            // Only consider pairs involving at least one witness
            if i >= num_pub || j >= num_pub {
                active_pairs.insert((i, j));
            }
        }
    }

    println!(
        "[Quotient] Found {} relevant pairs. Computing bases (Parallel)...",
        active_pairs.len()
    );

    // Diagnostic: Check column density
    let max_col_a = col_a.iter().map(|c| c.len()).max().unwrap_or(0);
    let max_col_b = col_b.iter().map(|c| c.len()).max().unwrap_or(0);
    println!("[Quotient] Max column density: A={}, B={}", max_col_a, max_col_b);
    
    // Estimate max capacity needed for buffers to avoid reallocation in hot loop
    // Most pairs are sparse-sparse, but dense-sparse pairs (involving one_var) need large buffers.
    // We assume max_sparse ~ 10 (typical R1CS). 
    // Safe upper bound: max(dense_A * 10, dense_B * 10).
    let buffer_capacity = std::cmp::max(max_col_a, max_col_b) * 20;
    println!("[Quotient] Pre-allocating buffers of size {} to avoid churn", buffer_capacity);

    let wit_start = Instant::now();
    let mut sorted_pairs: Vec<(usize, usize)> = active_pairs.into_iter().collect();
    sorted_pairs.sort();
    
    let n_scalar = domain.size_as_field_element();
    let domain_elements: Vec<_> = (0..domain.size()).map(|i| domain.element(i)).collect();
    let total_pairs = sorted_pairs.len();
    let progress_counter = std::sync::atomic::AtomicUsize::new(0);


    // Chunk size for batching to reduce overhead and allow buffer reuse
    const CHUNK_SIZE: usize = 256; 

    let h_wit: Vec<_> = sorted_pairs
        .par_chunks(CHUNK_SIZE)
        .flat_map(|chunk| {
            // Thread-local buffers to reuse across the chunk
            let mut denominators = Vec::with_capacity(buffer_capacity);
            let mut acc_u = Vec::with_capacity(max_col_a);
            let mut acc_v = Vec::with_capacity(max_col_b);
            
            // Collect all MSM tasks first, then process in parallel for better CPU utilization
            let mut msm_tasks: Vec<(Vec<<C::OuterE as Pairing>::G1Affine>, Vec<OuterScalar<C>>, (u32, u32))> = Vec::with_capacity(chunk.len());

            for &(i, j) in chunk {
                if (i as usize) < num_pub && (j as usize) < num_pub {
                    continue;
                }
                
                // Progress logging (approximate)
                let prog = progress_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if prog == 0 || prog % 100000 == 0 {
                     let elapsed = wit_start.elapsed().as_secs_f64();
                     let rate = prog as f64 / elapsed;
                     
                     // Read timers (convert micros to ms for readability)
                     
                     println!(
                        "[Quotient] {}/{} ({:.1}%) | {:.0} pair/s",
                        prog, total_pairs, (prog as f64 / total_pairs as f64) * 100.0, rate
                    );
                }

                let i_idx = i as usize;
                let j_idx = j as usize;
                let rows_u: &Vec<(usize, OuterScalar<C>)> = &col_a[i_idx];
                let rows_v: &Vec<(usize, OuterScalar<C>)> = &col_b[j_idx];
                
                if rows_u.is_empty() || rows_v.is_empty() {
                    continue;
                }

                let n_u = rows_u.len();
                let n_v = rows_v.len();
                let cap = n_u * n_v;

                // 1. Compute denominators
                denominators.clear();
                if denominators.capacity() < cap { denominators.reserve(cap - denominators.capacity()); }
                
                for &(k, _) in rows_u {
                    for &(m, _) in rows_v {
                        if k == m {
                            denominators.push(OuterScalar::<C>::one());
                        } else {
                            let diff = domain_elements[k] - domain_elements[m];
                            denominators.push(n_scalar * diff);
                        }
                    }
                }

                if denominators.is_empty() {
                    continue;
                }

                ark_ff::batch_inversion(&mut denominators);

                // 2. Accumulate coefficients
                acc_u.clear();
                acc_u.resize(n_u, OuterScalar::<C>::zero());
                acc_v.clear();
                acc_v.resize(n_v, OuterScalar::<C>::zero());

                let mut denom_idx = 0;
                for (idx_u, &(_, val_u)) in rows_u.iter().enumerate() {
                    for (idx_v, &(_, val_v)) in rows_v.iter().enumerate() {
                        let k = rows_u[idx_u].0;
                        let m = rows_v[idx_v].0;
                        let inv_denom = denominators[denom_idx];
                        denom_idx += 1;

                        if k == m { continue; }

                        let wm = domain_elements[m];
                        let wk = domain_elements[k];
                        let common = val_u * val_v * inv_denom;
                        acc_u[idx_u] += common * wm;
                        acc_v[idx_v] -= common * wk;
                    }
                }

                // 3. Collect bases for MSM (store for parallel processing)
                // Create new vectors for each pair to avoid move issues
                let mut pair_bases = Vec::with_capacity(max_col_a + max_col_b);
                let mut pair_scalars = Vec::with_capacity(max_col_a + max_col_b);
                
                for (idx_u, &(k, _)) in rows_u.iter().enumerate() {
                    if !acc_u[idx_u].is_zero() {
                        pair_bases.push(lagrange_srs[k]);
                        pair_scalars.push(acc_u[idx_u]);
                    }
                }
                for (idx_v, &(m, _)) in rows_v.iter().enumerate() {
                    if !acc_v[idx_v].is_zero() {
                        pair_bases.push(lagrange_srs[m]);
                        pair_scalars.push(acc_v[idx_v]);
                    }
                }

                if !pair_bases.is_empty() {
                    msm_tasks.push((pair_bases, pair_scalars, (i as u32, j as u32)));
                }
            }

            // Process MSMs in parallel for better CPU utilization
            let msm_start = Instant::now();
            let num_msms = msm_tasks.len();
            let total_points: usize = msm_tasks.iter().map(|(bases, _, _)| bases.len()).sum();
            
            let msm_results: Vec<((u32, u32), <C::OuterE as Pairing>::G1)> = msm_tasks
                .into_par_iter()
                .map(|(bases, scalars, pair_id)| {
                    let h_acc = <C::OuterE as Pairing>::G1::msm(&bases, &scalars).unwrap();
                    (pair_id, h_acc)
                })
                .filter(|(_, h_acc)| !h_acc.is_zero())
                .collect();
            
            let msm_elapsed = msm_start.elapsed();
            if num_msms > 0 {
                eprintln!(
                    "[Quotient] Chunk MSM: {} MSMs, {} total points, {:.2}ms ({:.0} MSM/s, {:.0} points/s)",
                    num_msms,
                    total_points,
                    msm_elapsed.as_secs_f64() * 1000.0,
                    num_msms as f64 / msm_elapsed.as_secs_f64(),
                    total_points as f64 / msm_elapsed.as_secs_f64()
                );
            }

            // SoA layout to avoid intermediate tuple allocations and copies for normalization
            let mut point_accs = Vec::with_capacity(msm_results.len());
            let mut point_ids = Vec::with_capacity(msm_results.len());
            
            for (pair_id, h_acc) in msm_results {
                point_accs.push(h_acc);
                point_ids.push(pair_id);
            }
            
            // Batch normalize to save inversions (significant for small MSMs)
            // 158M inversions -> ~26 mins. Batch norm -> ~20 secs.
            let mut affine_results = Vec::with_capacity(point_accs.len());
            if !point_accs.is_empty() {
                 let affines = <C::OuterE as Pairing>::G1::normalize_batch(&point_accs);
                 for (idx, affine) in affines.into_iter().enumerate() {
                     affine_results.push((point_ids[idx].0, point_ids[idx].1, affine));
                 }
            }
            
            affine_results
        })
        .collect();

    let count = h_wit.len();
    println!(
        "[Quotient] Witness Bases done. Found {} non-zero bases. Time: {:?}",
        count,
        wit_start.elapsed()
    );

    h_wit
}
// --- Group FFT Helpers ---

fn parallel_fft_g1<G: CurveGroup<ScalarField = F> + Send, F: PrimeField>(
    a: &mut [G],
    domain: &GeneralEvaluationDomain<F>,
) {
    let n = a.len();
    if n <= 1 { return; }
    let log_n = n.trailing_zeros();
    
    // Serial bit reverse (fast enough)
    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk { a.swap(k, rk); }
    }
    
    let mut m = 1;
    while m < n {
        let omega_m = domain.element(domain.size() / (2 * m));
        
        // Parallel Butterfly
        a.par_chunks_mut(2 * m).for_each(|chunk| {
            let mut w = F::one();
            for j in 0..m {
                let t = chunk[j + m] * w;
                let u = chunk[j];
                chunk[j] = u + t;
                chunk[j + m] = u - t;
                w *= omega_m;
            }
        });
        m *= 2;
    }
}

fn parallel_ifft_g1<G: CurveGroup<ScalarField = F> + Send, F: PrimeField>(
    a: &mut [G],
    domain: &GeneralEvaluationDomain<F>,
) {
    parallel_fft_g1(a, domain);
    if a.len() > 1 {
        a[1..].reverse();
    }
    let n_inv = domain.size_as_field_element().inverse().unwrap();
    // Parallel scaling
    a.par_iter_mut().for_each(|x| *x *= n_inv);
}

fn compute_q_const_points_from_gap<C: RecursionCycle>(
    pk_outer: &Groth16PK<C::OuterE>,
    lean_pk: &LeanProvingKey<C::OuterE>,
    vk_inner: &InnerVk<C>,
    n_inner_inputs: usize,
    sample_inner_proof: &InnerProof<C>,
) -> Vec<<C::OuterE as Pairing>::G1Affine> {
    let mut q_points =
        vec![<C::OuterE as Pairing>::G1Affine::zero(); n_inner_inputs + 1];

    // Use the sample inner proof (should be a real valid proof with non-zero curve points)
    // This ensures the witness sparsity pattern matches real proofs
    let proof_for_setup = sample_inner_proof.clone();

    let mut base_inputs = vec![InnerScalar::<C>::zero(); n_inner_inputs];

    for idx in 0..=n_inner_inputs {
        if idx > 0 {
            base_inputs[idx - 1] = InnerScalar::<C>::one();
        }

        let circuit_std =
            OuterCircuit::<C>::new(vk_inner.clone(), base_inputs.clone(), proof_for_setup.clone());
        let proof_std = Groth16::<C::OuterE>::create_proof_with_reduction_no_zk(
            circuit_std,
            pk_outer,
        )
        .expect("standard proof failed");

        let circuit_lean =
            OuterCircuit::<C>::new(vk_inner.clone(), base_inputs.clone(), proof_for_setup.clone());
        let (proof_lean, _) = prove_lean_with_randomizers(
            lean_pk,
            circuit_lean,
            OuterScalar::<C>::zero(),
            OuterScalar::<C>::zero(),
        )
        .expect("lean proof failed");

        let c_gap = proof_std.c.into_group() - proof_lean.c.into_group();

        if idx == 0 {
            q_points[0] = c_gap.into_affine();
        } else {
            let qi = (c_gap - q_points[0].into_group()).into_affine();
            q_points[idx] = qi;
            base_inputs[idx - 1] = InnerScalar::<C>::zero();
        }
    }

    q_points
}

pub fn compute_target_outer(
    vk_outer: &Groth16VK<OuterE>,
    pvugc_vk: &PvugcVk<OuterE>,
    public_inputs_inner: &[InnerFr],
) -> PairingOutput<OuterE> {
    compute_target_outer_for::<DefaultCycle>(vk_outer, pvugc_vk, public_inputs_inner)
}

pub fn compute_r_to_rho_outer_for<C: RecursionCycle>(
    r: &PairingOutput<C::OuterE>,
    rho: &OuterScalar<C>,
) -> PairingOutput<C::OuterE> {
    let r_to_rho = r.0.pow(&rho.into_bigint());
    PairingOutput(r_to_rho)
}

pub fn compute_r_to_rho_outer(r: &PairingOutput<OuterE>, rho: &OuterFr) -> PairingOutput<OuterE> {
    compute_r_to_rho_outer_for::<DefaultCycle>(r, rho)
}

pub fn compute_target_outer_for<C: RecursionCycle>(
    vk_outer: &Groth16VK<C::OuterE>,
    pvugc_vk: &PvugcVk<C::OuterE>,
    public_inputs_inner: &[InnerScalar<C>],
) -> PairingOutput<C::OuterE> {
    let x_outer: Vec<OuterScalar<C>> = public_inputs_inner
        .iter()
        .map(fr_inner_to_outer_for::<C>)
        .collect();

    crate::ppe::compute_baked_target::<C::OuterE>(vk_outer, pvugc_vk, &x_outer)
        .expect("failed to compute baked target")
}

pub fn arm_columns_outer_for<C: RecursionCycle>(
    bases: &ColumnBases<C::OuterE>,
    rho: &OuterScalar<C>,
) -> ColumnArms<C::OuterE> {
    crate::arming::arm_columns(bases, rho).expect("arm_columns failed")
}

pub fn arm_columns_outer(bases: &ColumnBases<OuterE>, rho: &OuterFr) -> ColumnArms<OuterE> {
    arm_columns_outer_for::<DefaultCycle>(bases, rho)
}
