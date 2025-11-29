//! PVUGC Operations on Outer Curve
//!
//! Thin wrappers that apply PVUGC column operations to the OUTER proof.
//! All PVUGC logic runs on BW6-761 (outer curve) which has constant-size right-legs.

use crate::arming::{ColumnArms, ColumnBases};
use crate::outer_compressed::{
    fr_inner_to_outer_for, DefaultCycle, InnerFr, InnerProof, InnerScalar, InnerVk, OuterCircuit,
    OuterE, OuterFr, OuterScalar, RecursionCycle,
};
use crate::ppe::PvugcVk;
use crate::prover_lean::{prove_lean_with_randomizers, LeanProvingKey};
use ark_ec::pairing::{Pairing, PairingOutput};
use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{Field, One, PrimeField, Zero};
use ark_groth16::{Groth16, ProvingKey as Groth16PK, VerifyingKey as Groth16VK};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::fs::File;
use std::io::{BufReader, BufWriter, Write};
use std::time::Instant;

type StatementVec<C> = Vec<InnerScalar<C>>;

/// Build PVUGC VK and Lean PK from the OUTER proving key.
///
/// IMPORTANT: When the Groth16 verifier gadget is enabled in the outer circuit,
/// the q_const computation needs to generate valid inner proofs for each sampled
/// statement. This requires the inner proving key.
///
/// The `inner_proof_generator` closure takes a vector of statement values (one per
/// public input) and returns a valid inner Groth16 proof for that statement.
/// This ensures the outer circuit's verifier constraints are satisfied during
/// q_const computation.
pub fn build_pvugc_setup_from_pk_for<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    inner_proof_generator: F,
) -> (PvugcVk<C::OuterE>, LeanProvingKey<C::OuterE>)
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    let n_inner_inputs = vk_inner.gamma_abc_g1.len() - 1;
    let canonical_samples = canonical_sample_statements::<C>(n_inner_inputs);
    build_pvugc_setup_from_pk_for_with_samples::<C, F>(
        pk_outer,
        vk_inner,
        inner_proof_generator,
        canonical_samples,
    )
}

pub fn build_pvugc_setup_from_pk_for_with_samples<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    inner_proof_generator: F,
    sample_statements: Vec<StatementVec<C>>,
) -> (PvugcVk<C::OuterE>, LeanProvingKey<C::OuterE>)
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    let start = Instant::now();
    println!("[Setup] Starting PVUGC Setup from PK...");

    let n_inner_inputs = vk_inner.gamma_abc_g1.len() - 1;
    println!(
        "[Setup] Inner public inputs (packed outer instances): {}",
        n_inner_inputs
    );
    assert_eq!(
        sample_statements.len(),
        n_inner_inputs + 1,
        "sample statements must provide n+1 entries"
    );

    // Sanitize cycle name for filename and derive a hash of the proving key so caches
    // from different PKs never collide.
    let safe_name = C::name().replace('/', "_").replace(' ', "_");
    let mut hasher = Sha256::new();
    pk_outer
        .vk
        .serialize_uncompressed(&mut hasher)
        .expect("failed to serialize vk for hashing");
    for statement in &sample_statements {
        for coord in statement {
            coord
                .serialize_uncompressed(&mut hasher)
                .expect("failed to serialize statement coord");
        }
        hasher.update(&[0u8]);
    }
    let hash = hasher.finalize();
    let hash_prefix: String = hash[..8].iter().map(|b| format!("{:02x}", b)).collect();
    let cache_path = format!("outer_lean_setup_pk_vk_{}_{}.bin", safe_name, hash_prefix);

    let cache_file = std::path::Path::new(&cache_path);
    let (lean_pk, q_points) = if cache_file.exists() {
        println!("[Setup] Found cached setup at {}, loading...", cache_path);
        let file = File::open(&cache_path).expect("failed to open cached setup");
        let reader = BufReader::with_capacity(1024 * 1024 * 1024, file); // 1GB buffer
        let (pk, q_points): (
            LeanProvingKey<C::OuterE>,
            Vec<<C::OuterE as Pairing>::G1Affine>,
        ) = CanonicalDeserialize::deserialize_uncompressed_unchecked(reader)
            .expect("failed to deserialize setup");
        println!("[Setup] Cached setup loaded in {:?}", start.elapsed());
        (pk, q_points)
    } else {
        println!("[Setup] No cache found. Computing witness bases...");
        let wb_result = compute_witness_bases::<C>(pk_outer, vk_inner, n_inner_inputs);
        println!("[Setup] Witness Bases Computed in {:?}", start.elapsed());

        let lean_pk = LeanProvingKey {
            vk: pk_outer.vk.clone(),
            beta_g1: pk_outer.beta_g1,
            delta_g1: pk_outer.delta_g1,
            a_query: pk_outer.a_query.clone(),
            b_g1_query: pk_outer.b_g1_query.clone(),
            b_g2_query: pk_outer.b_g2_query.clone(),
            h_query_wit: wb_result.h_query_wit,
            l_query: pk_outer.l_query.clone(),
        };

        println!("[Setup] Computing q_points from gap (using custom samples)...");
        let q_points = compute_q_const_points_from_gap::<C, F>(
            pk_outer,
            &lean_pk,
            vk_inner,
            &sample_statements,
            &inner_proof_generator,
        );
        println!("[Setup] q_points computed in {:?}", start.elapsed());
        println!("[Setup] Serializing setup to {}...", cache_path);
        let file = File::create(&cache_path).expect("failed to create cache file");
        let mut writer = BufWriter::with_capacity(1024 * 1024 * 1024, file); // 1GB buffer
        (lean_pk.clone(), q_points.clone())
            .serialize_uncompressed(&mut writer)
            .expect("failed to serialize setup");
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

pub fn build_pvugc_vk_outer_from_pk_for<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    inner_proof_generator: F,
) -> PvugcVk<C::OuterE>
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    build_pvugc_setup_from_pk_for::<C, F>(pk_outer, vk_inner, inner_proof_generator).0
}

pub fn build_pvugc_vk_outer_from_pk<F>(
    pk_outer: &Groth16PK<OuterE>,
    vk_inner: &InnerVk<DefaultCycle>,
    inner_proof_generator: F,
) -> PvugcVk<OuterE>
where
    F: Fn(&[InnerScalar<DefaultCycle>]) -> InnerProof<DefaultCycle>,
{
    build_pvugc_vk_outer_from_pk_for::<DefaultCycle, F>(pk_outer, vk_inner, inner_proof_generator)
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

/// Result of computing witness bases
struct WitnessBasesResult<E: Pairing> {
    /// Sparse H_{ij} bases for witness terms (off-diagonal and diagonal contributions)
    pub h_query_wit: Vec<(u32, u32, E::G1Affine)>,
}

fn compute_witness_bases<C: RecursionCycle>(
    pk: &Groth16PK<C::OuterE>,
    vk_inner: &InnerVk<C>,
    n_inner_inputs: usize,
) -> WitnessBasesResult<C::OuterE> {
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

    // CRITICAL: Domain size must match standard Groth16!
    // Standard Groth16 uses domain of size (num_constraints + num_inputs) to include
    // the "copy constraints" that encode public inputs into the A polynomial.
    let num_constraints = cs.num_constraints();
    let num_inputs = cs.num_instance_variables(); // includes constant 1
    let qap_domain_size = num_constraints + num_inputs;

    let domain = GeneralEvaluationDomain::<OuterScalar<C>>::new(qap_domain_size)
        .or_else(|| {
            GeneralEvaluationDomain::<OuterScalar<C>>::new(qap_domain_size.next_power_of_two())
        })
        .expect("domain creation failed");
    let domain_size = domain.size();

    println!(
        "[Quotient] Matrix extracted ({} constraints + {} inputs = {} QAP size). Domain size: {}. Time: {:?}",
        num_constraints,
        num_inputs,
        qap_domain_size,
        domain_size,
        start.elapsed()
    );

    let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
    let mut col_a = vec![Vec::new(); num_vars];
    let mut col_b = vec![Vec::new(); num_vars];

    // Process constraint rows from matrices
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

    // CRITICAL: Add the synthetic "copy constraint" rows for public inputs!
    // In standard Groth16, rows [num_constraints..num_constraints+num_inputs] have:
    //   A[row] = public_input[row - num_constraints] (i.e., variable index = row - num_constraints)
    //   B[row] = 0
    // This encodes the public inputs into the A polynomial.
    // Since B[row] = 0 for these rows, they don't contribute to A*B products,
    // but they DO affect the Lagrange basis representation!
    for i in 0..num_inputs {
        let row = num_constraints + i;
        if row < domain_size {
            // A[row] has coefficient 1 for variable i (the i-th public input)
            col_a[i].push((row, OuterScalar::<C>::one()));
            // B[row] = 0, so nothing to add to col_b
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
    let lagrange_srs: Vec<_> = lagrange_srs
        .into_par_iter()
        .map(|p| p.into_affine())
        .collect();
    println!(
        "[Quotient] Lagrange SRS computed in {:?}",
        fft_start.elapsed()
    );

    let num_pub = cs.num_instance_variables();
    let mut vars_a = HashSet::new();
    let mut vars_b = HashSet::new();
    for (row, terms) in matrices.a.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms {
                vars_a.insert(col);
            }
        }
    }
    for (row, terms) in matrices.b.iter().enumerate() {
        if row < domain_size {
            for &(_, col) in terms {
                vars_b.insert(col);
            }
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

    // Estimate max capacity needed for buffers to avoid reallocation in hot loop
    // Most pairs are sparse-sparse, but dense-sparse pairs (involving one_var) need large buffers.
    // We assume max_sparse ~ 10 (typical R1CS).
    // Safe upper bound: max(dense_A * 10, dense_B * 10).
    let max_col_a = col_a.iter().map(|c| c.len()).max().unwrap_or(0);
    let max_col_b = col_b.iter().map(|c| c.len()).max().unwrap_or(0);
    let buffer_capacity = std::cmp::max(max_col_a, max_col_b) * 20;
    println!(
        "[Quotient] Pre-allocating buffers of size {} to avoid churn",
        buffer_capacity
    );

    // --- Diagonal Terms Computation (Optimized via Convolution) ---
    println!("[Quotient] Computing Diagonal Correction vector Q...");
    let diag_start = Instant::now();

    // We need Q[k] = Q_k(tau) for all k.
    // Q_k(tau) = sum_m C_{k,m} L_m(tau).
    // The matrix C is circulant: C_{k,m} depends on (m-k) mod n.
    // Let u_j = C_{0,j} = Q_0(omega^j).
    // Then Q = u * L (convolution).
    // We compute this via FFT: Q = IFFT( FFT(u) . FFT(L) ).

    let n_field = domain.size_as_field_element();
    let t0 =
        (n_field - OuterScalar::<C>::one()) * (n_field + n_field).inverse().expect("2n invertible");

    // 1. Build kernel u
    let mut u = vec![OuterScalar::<C>::zero(); domain_size];
    u[0] = t0;

    // u[j] = 1 / (n * (1 - omega^j))
    // We need to batch invert.
    let mut denoms = Vec::with_capacity(domain_size - 1);
    let mut indices = Vec::with_capacity(domain_size - 1);

    for j in 1..domain_size {
        let omega_j = domain.element(j);
        let denom = n_field * (OuterScalar::<C>::one() - omega_j);
        denoms.push(denom);
        indices.push(j);
    }

    ark_ff::batch_inversion(&mut denoms);
    for (i, &j) in indices.iter().enumerate() {
        u[j] = denoms[i];
    }

    // Reverse u[1..] to compute correlation via convolution
    // We want sum_j L_j * u_{j-k} = sum_j L_j * u_{-(k-j)}
    // Convolution computes sum_j L_j * v_{k-j}. So we need v_x = u_{-x}.
    if domain_size > 1 {
        u[1..].reverse();
    }

    // 2. FFT(u)
    parallel_fft_scalar(&mut u, &domain);

    // 3. FFT(L)
    // lagrange_srs is currently [L_0, ..., L_{n-1}].
    // We need to convert to Projective for FFT
    let mut l_fft: Vec<_> = lagrange_srs.iter().map(|p| p.into_group()).collect();
    parallel_fft_g1(&mut l_fft, &domain);

    // 4. Pointwise Product in Frequency Domain
    // Q_hat[i] = u_hat[i] * L_hat[i]
    l_fft
        .par_iter_mut()
        .zip(u.par_iter())
        .for_each(|(l_val, &u_val)| {
            *l_val *= u_val;
        });

    // 5. IFFT to get Q
    parallel_ifft_g1(&mut l_fft, &domain);

    // Convert back to Affine for storage/use
    let q_vector: Vec<_> = l_fft.into_par_iter().map(|p| p.into_affine()).collect();

    println!(
        "[Quotient] Diagonal Q-vector computed in {:?}",
        diag_start.elapsed()
    );

    // --- Main Loop with Q-Vector Support ---
    // We rewrite the main loop to use q_vector for diagonal terms (k==m)

    let wit_start = Instant::now();
    let mut sorted_pairs: Vec<(usize, usize)> = active_pairs.into_iter().collect();
    sorted_pairs.sort();

    let n_scalar = domain.size_as_field_element();
    let domain_elements: Vec<_> = (0..domain.size()).map(|i| domain.element(i)).collect();
    let total_pairs = sorted_pairs.len();
    let progress_counter = std::sync::atomic::AtomicUsize::new(0);

    // Chunk size for batching
    const CHUNK_SIZE: usize = 512;

    let h_wit: Vec<_> = sorted_pairs
        .par_chunks(CHUNK_SIZE)
        .flat_map(|chunk| {
            let mut denominators = Vec::with_capacity(buffer_capacity);
            let mut acc_u = Vec::with_capacity(max_col_a);
            let mut acc_v = Vec::with_capacity(max_col_b);
            let mut msm_tasks: Vec<(
                Vec<<C::OuterE as Pairing>::G1Affine>,
                Vec<OuterScalar<C>>,
                (u32, u32),
            )> = Vec::with_capacity(chunk.len());

            for &(i, j) in chunk {
                if (i as usize) < num_pub && (j as usize) < num_pub {
                    continue;
                }

                let prog = progress_counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                if prog == 0 || prog % 100000 == 0 {
                    let elapsed = wit_start.elapsed().as_secs_f64();
                    let rate = prog as f64 / elapsed;
                    println!(
                        "[Quotient] {}/{} ({:.1}%) | {:.0} pair/s",
                        prog,
                        total_pairs,
                        (prog as f64 / total_pairs as f64) * 100.0,
                        rate
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

                // 1. Compute denominators for off-diagonal
                denominators.clear();
                if denominators.capacity() < cap {
                    denominators.reserve(cap - denominators.capacity());
                }

                for &(k, _) in rows_u {
                    for &(m, _) in rows_v {
                        if k != m {
                            let diff = domain_elements[k] - domain_elements[m];
                            denominators.push(n_scalar * diff);
                        } else {
                            denominators.push(OuterScalar::<C>::one()); // Dummy for index alignment
                        }
                    }
                }

                // Batch inversion for off-diagonal denominators
                ark_ff::batch_inversion(&mut denominators);

                // 2. Accumulate coefficients
                acc_u.clear();
                acc_u.resize(n_u, OuterScalar::<C>::zero());
                acc_v.clear();
                acc_v.resize(n_v, OuterScalar::<C>::zero());

                // Extra bases for diagonal contributions (using q_vector)
                let mut diag_bases = Vec::new();
                let mut diag_scalars = Vec::new();

                let mut denom_idx = 0;
                for (idx_u, &(_, val_u)) in rows_u.iter().enumerate() {
                    for (idx_v, &(_, val_v)) in rows_v.iter().enumerate() {
                        let k = rows_u[idx_u].0;
                        let m = rows_v[idx_v].0;
                        let inv_denom = denominators[denom_idx];
                        denom_idx += 1;

                        let prod = val_u * val_v;

                        if k == m {
                            // Diagonal term: prod * Q[k]
                            diag_bases.push(q_vector[k]);
                            diag_scalars.push(prod);
                        } else {
                            // Off-diagonal term
                            let wm = domain_elements[m];
                            let wk = domain_elements[k];
                            let common = prod * inv_denom;
                            acc_u[idx_u] += common * wm;
                            acc_v[idx_v] -= common * wk;
                        }
                    }
                }

                // 3. Collect bases for MSM
                let mut pair_bases = Vec::with_capacity(max_col_a + max_col_b + diag_bases.len());
                let mut pair_scalars = Vec::with_capacity(max_col_a + max_col_b + diag_bases.len());

                // Add off-diagonal contributions (Lagrange bases)
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

                // Add diagonal contributions (Q bases)
                pair_bases.extend(diag_bases);
                pair_scalars.extend(diag_scalars);

                if !pair_bases.is_empty() {
                    msm_tasks.push((pair_bases, pair_scalars, (i as u32, j as u32)));
                }
            }

            // Process MSMs
            let msm_results: Vec<((u32, u32), <C::OuterE as Pairing>::G1)> = msm_tasks
                .into_par_iter()
                .map(|(bases, scalars, pair_id)| {
                    let h_acc = <C::OuterE as Pairing>::G1::msm(&bases, &scalars).unwrap();
                    (pair_id, h_acc)
                })
                .filter(|(_, h_acc)| !h_acc.is_zero())
                .collect();

            let mut point_accs = Vec::with_capacity(msm_results.len());
            let mut point_ids = Vec::with_capacity(msm_results.len());
            for (pair_id, h_acc) in msm_results {
                point_accs.push(h_acc);
                point_ids.push(pair_id);
            }

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
    WitnessBasesResult { h_query_wit: h_wit }
}
// --- Group FFT Helpers ---

fn parallel_fft_scalar<F: PrimeField>(a: &mut [F], domain: &GeneralEvaluationDomain<F>) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();

    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk {
            a.swap(k, rk);
        }
    }

    let mut m = 1;
    while m < n {
        let omega_m = domain.element(domain.size() / (2 * m));

        // chunk_size = 2*m
        // We can process in parallel if chunks are large enough
        // For scalars, rayon might add overhead for small chunks, but let's stick to pattern
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

fn parallel_fft_g1<G: CurveGroup<ScalarField = F> + Send, F: PrimeField>(
    a: &mut [G],
    domain: &GeneralEvaluationDomain<F>,
) {
    let n = a.len();
    if n <= 1 {
        return;
    }
    let log_n = n.trailing_zeros();

    // Serial bit reverse (fast enough)
    for k in 0..n {
        let rk = k.reverse_bits() >> (usize::BITS - log_n);
        if k < rk {
            a.swap(k, rk);
        }
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

fn compute_q_const_points_from_gap<C, F>(
    pk_outer: &Groth16PK<C::OuterE>,
    lean_pk: &LeanProvingKey<C::OuterE>,
    vk_inner: &InnerVk<C>,
    sample_statements: &[StatementVec<C>],
    inner_proof_generator: &F,
) -> Vec<<C::OuterE as Pairing>::G1Affine>
where
    C: RecursionCycle,
    F: Fn(&[InnerScalar<C>]) -> InnerProof<C>,
{
    let mut gaps: Vec<(Vec<OuterScalar<C>>, <C::OuterE as Pairing>::G1Affine)> =
        Vec::with_capacity(sample_statements.len());

    for statement in sample_statements {
        // Generate a valid inner proof for THIS specific statement vector
        let inner_proof = inner_proof_generator(statement);
        println!("[q_const] Generating proofs for statement {:?}", statement);

        let circuit_std =
            OuterCircuit::<C>::new(vk_inner.clone(), statement.clone(), inner_proof.clone());
        let proof_std =
            Groth16::<C::OuterE>::create_proof_with_reduction_no_zk(circuit_std, pk_outer)
                .expect("standard proof failed");

        let circuit_lean =
            OuterCircuit::<C>::new(vk_inner.clone(), statement.clone(), inner_proof.clone());
        let (proof_lean, _) = prove_lean_with_randomizers(
            lean_pk,
            circuit_lean,
            OuterScalar::<C>::zero(),
            OuterScalar::<C>::zero(),
        )
        .expect("lean proof failed");

        let c_gap = proof_std.c.into_group() - proof_lean.c.into_group();

        let circuit_inputs =
            OuterCircuit::<C>::new(vk_inner.clone(), statement.clone(), inner_proof.clone());
        let cs_inputs = ConstraintSystem::<OuterScalar<C>>::new_ref();
        circuit_inputs
            .generate_constraints(cs_inputs.clone())
            .expect("input extraction failed");
        cs_inputs.finalize();
        let mut instance = cs_inputs.borrow().unwrap().instance_assignment.clone();
        let compressed_inputs = instance.split_off(1);
        gaps.push((compressed_inputs, c_gap.into_affine()));
    }

    solve_q_const_from_samples::<C>(gaps)
}

fn canonical_sample_statements<C: RecursionCycle>(n_inner_inputs: usize) -> Vec<StatementVec<C>> {
    let mut samples = Vec::with_capacity(n_inner_inputs + 1);
    samples.push(vec![InnerScalar::<C>::zero(); n_inner_inputs]);
    for idx in 0..n_inner_inputs {
        let mut statement = vec![InnerScalar::<C>::zero(); n_inner_inputs];
        statement[idx] = InnerScalar::<C>::one();
        samples.push(statement);
    }
    samples
}

fn solve_q_const_from_samples<C: RecursionCycle>(
    gaps: Vec<(Vec<OuterScalar<C>>, <C::OuterE as Pairing>::G1Affine)>,
) -> Vec<<C::OuterE as Pairing>::G1Affine> {
    assert!(
        !gaps.is_empty(),
        "at least one sample is required to recover q_const"
    );
    let num_inputs = gaps[0].0.len();
    assert_eq!(
        gaps.len(),
        num_inputs + 1,
        "need exactly n+1 samples to solve linear system"
    );
    let size = num_inputs + 1;

    let mut matrix = vec![vec![OuterScalar::<C>::zero(); size]; size];
    for (row, (compressed_inputs, _)) in gaps.iter().enumerate() {
        matrix[row][0] = OuterScalar::<C>::one();
        for (col, value) in compressed_inputs.iter().enumerate() {
            matrix[row][col + 1] = *value;
        }
    }

    let inv = invert_matrix::<C>(matrix);
    let gaps_group: Vec<_> = gaps.iter().map(|(_, gap)| gap.into_group()).collect();

    let mut q_points = Vec::with_capacity(size);
    for row in 0..size {
        let mut acc = <C::OuterE as Pairing>::G1::zero();
        for col in 0..size {
            let coeff = inv[row][col];
            if !coeff.is_zero() {
                acc += gaps_group[col] * coeff;
            }
        }
        q_points.push(acc.into_affine());
    }
    q_points
}

fn invert_matrix<C: RecursionCycle>(matrix: Vec<Vec<OuterScalar<C>>>) -> Vec<Vec<OuterScalar<C>>> {
    let size = matrix.len();
    let mut aug = vec![vec![OuterScalar::<C>::zero(); 2 * size]; size];
    for i in 0..size {
        for j in 0..size {
            aug[i][j] = matrix[i][j];
        }
        aug[i][size + i] = OuterScalar::<C>::one();
    }

    for col in 0..size {
        let pivot_row = (col..size)
            .find(|r| !aug[*r][col].is_zero())
            .expect("matrix is not invertible");
        if pivot_row != col {
            aug.swap(col, pivot_row);
        }
        let inv = aug[col][col].inverse().expect("pivot must be invertible");
        for j in 0..2 * size {
            aug[col][j] *= inv;
        }
        for row in 0..size {
            if row == col {
                continue;
            }
            let factor = aug[row][col];
            if !factor.is_zero() {
                for j in 0..2 * size {
                    let tmp = aug[col][j] * factor;
                    aug[row][j] -= tmp;
                }
            }
        }
    }

    let mut inverse = vec![vec![OuterScalar::<C>::zero(); size]; size];
    for i in 0..size {
        for j in 0..size {
            inverse[i][j] = aug[i][size + j];
        }
    }
    inverse
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
