//! PVUGC Trapdoor-Aware Audit Tool
//!
//! This tool audits circuits for algebraic security.
//! It performs:
//! 1. **Linearity Check**: Verifies that Public Inputs do not multiply each other.
//! 2. **Independence Check**: Verifies that the "Baked Quotient" Target lies outside the linear span of the
//!    "Lean CRS" + "Ciphertext" handles in the Generic Bilinear Group Model (AGBGM).
//!
//! Optimization: Uses streaming column processing + Incremental Basis + Sparse Eval.

use ark_ff::{Field, One, Zero};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial, DenseUVPolynomial,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef};
use arkworks_groth16::{
    outer_compressed::{OuterCircuit, DefaultCycle, InnerScalar, OuterFr, InnerE},
    test_fixtures::get_fixture, test_circuits::AddCircuit,
};
use ark_groth16::Groth16;
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;
use std::collections::HashMap;

type Fr = OuterFr;

// --- Trapdoor Monomial Taxonomy (Delta-Normalized) ---
// All handles/targets are multiplied by delta to clear denominators from L-queries.
// Base ring: F[alpha, beta, gamma, delta, x]
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TrapdoorMonomial {
    // --- Target Terms (scaled by delta) ---
    AlphaBetaDelta,  // alpha * beta * delta
    GammaDelta,      // gamma * delta * IC(x)
    DeltaSq,         // Any(x) * delta^2 (Merges H and u terms)
    
    // --- Handle Terms from L_k * D_pub (1/delta * delta cancels) ---
    // Result is (beta*u + alpha*v + w)(beta + V)
    BetaSqU,         // beta^2 * u
    BetaU,           // beta * u * V
    AlphaBetaV,      // alpha * beta * v
    AlphaV,          // alpha * v * V
    BetaW,           // beta * w
    W,               // w * V
    
    // Result is (beta*u + ...)(v_j)
    BetaUV,          // beta * u * v
    AlphaVV,         // alpha * v * v
    WV,              // w * v
    
    // --- Handle Terms from L_k * D_delta (Clean L * delta) ---
    // Result is (beta*u + alpha*v + w) * delta
    BetaDeltaU,      // beta * delta * u
    AlphaDeltaV,     // alpha * delta * v
    DeltaW,          // delta * w
    
    // --- Handle Terms from u_k * D_pub (Clean u * delta) ---
    // u * (beta + V) * delta = beta*delta*u + delta*u*V
    // BetaDeltaU is already defined above (MATCH!)
    DeltaUV,         // delta * u * V
    
    // --- Handle Terms from u_k * D_delta (Clean u * delta) ---
    // u * delta * delta = delta^2 * u
    // Merged into DeltaSq
    
    // --- Handle Terms from u_k * D_j (Clean u * v * delta) ---
    // u * v * delta
    DeltaPureUV,     // delta * u * v
    
    // --- Fixed Alpha Handles ---
    // alpha * D_pub * delta = alpha(beta+V)delta = alpha*beta*delta + alpha*V*delta
    // AlphaDeltaV represents alpha * delta * V_pub
    
    // alpha * D_delta * delta = alpha * delta^2
    AlphaDeltaSq,    // alpha * delta^2
}

struct TrapdoorPolyVector {
    components: Vec<(TrapdoorMonomial, DensePolynomial<Fr>)>,
}

impl TrapdoorPolyVector {
    fn new(components: Vec<(TrapdoorMonomial, DensePolynomial<Fr>)>) -> Self {
        Self { components }
    }
}

// --- Audit Subjects ---

trait AuditSubject {
    fn name(&self) -> &'static str;
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()>;
}

struct ProductionSubject(OuterCircuit<DefaultCycle>);
impl AuditSubject for ProductionSubject {
    fn name(&self) -> &'static str { "Production OuterCircuit" }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        self.0.clone().generate_constraints(cs)
    }
}

struct MockLinear;
impl AuditSubject for MockLinear {
    fn name(&self) -> &'static str { "Mock Linear (Safe)" }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        use ark_r1cs_std::prelude::*;
        let x = ark_r1cs_std::fields::fp::FpVar::new_input(cs.clone(), || Ok(Fr::one()))?;
        let five = ark_r1cs_std::fields::fp::FpVar::constant(Fr::from(5));
        x.enforce_equal(&five)?;
        Ok(())
    }
}

struct MockQuadratic;
impl AuditSubject for MockQuadratic {
    fn name(&self) -> &'static str { "Mock Quadratic (Unsafe)" }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        use ark_r1cs_std::prelude::*;
        let x = ark_r1cs_std::fields::fp::FpVar::new_input(cs.clone(), || Ok(Fr::one()))?;
        let one = ark_r1cs_std::fields::fp::FpVar::constant(Fr::from(1));
        x.mul_equals(&x, &one)?;
        Ok(())
    }
}

fn main() {
    println!("PVUGC Production Audit Tool");
    println!("===========================\n");

    let subjects: Vec<Box<dyn AuditSubject>> = vec![
        Box::new(MockLinear),
        Box::new(MockQuadratic),
        Box::new(ProductionSubject(get_valid_circuit())),
    ];

    for subject in subjects {
        println!(">>> AUDITING: {} <<<", subject.name());
        run_audit(subject.as_ref());
        println!("\n");
    }
    
    // Diagonal Basis Security Audit (for Lean Prover)
    println!(">>> DIAGONAL BASIS SECURITY AUDIT <<<");
    println!("=====================================\n");
    
    let circuit = get_valid_circuit();
    let (d, n, rank, is_secure) = audit_diagonal_basis_security(circuit);
    
    println!("\nSummary:");
    println!("  Diagonal rows (d): {}", d);
    println!("  Domain size (n):   {}", n);
    println!("  Matrix rank:       {}", rank);
    println!("  Hidden dimensions: {}", if n > 1 { n - 1 - d } else { 0 });
    println!("  Security ratio:    {:.2}% hidden", 
        if n > 1 { ((n - 1 - d) as f64 / (n - 1) as f64) * 100.0 } else { 0.0 });
    println!("\nDiagonal Basis Security: {}", 
        if is_secure { "✓ SECURE" } else { "✗ VULNERABLE" });
}

fn run_audit(subject: &dyn AuditSubject) {
    let cs = ConstraintSystem::<Fr>::new_ref();
    subject.synthesize(cs.clone()).unwrap();
    cs.finalize();
    println!("Constraints: {}", cs.num_constraints());
    let num_pub = cs.num_instance_variables();
    let num_wit = cs.num_witness_variables();
    println!("Public: {}, Witness: {}", num_pub, num_wit);

    let extractor = MatrixExtractor::new(cs.clone());
    
    // 1. Linearity Check
    let mut pub_polys = Vec::new();
    for i in 0..num_pub {
        pub_polys.push(extractor.get_column_polys(i));
    }
    
    let is_linear = check_linearity(&pub_polys, num_pub);
    if is_linear {
        println!("[PASS] Linearity Check.");
    } else {
        println!("[FAIL] Linearity Check (Public*Public detected).");
    }

    // 2. Independence Check
    let h_const = compute_h_const(&pub_polys, &extractor.domain);
    let target = build_target(&pub_polys, &h_const);
    
    let mut all_safe = true;
    let num_checks = 5;
    println!("[Independence Check] Running {} iterations for robustness...", num_checks);

    for i in 0..num_checks {
        let seed = 12345 + i as u64;
        let is_safe = check_independence_streaming(&extractor, &pub_polys, &target, num_pub, num_pub + num_wit, seed, i + 1, num_checks);
        if !is_safe {
            all_safe = false;
            println!("[FAIL] Iteration {} found dependency!", i + 1);
            break;
        }
    }

    if all_safe {
        println!("[PASS] Independence Check (All {} iterations passed).", num_checks);
    } else {
        println!("[FAIL] Independence Check (Target in Span).");
    }

    println!("RESULT: {}", 
        if is_linear && all_safe { "SAFE" } else { "UNSAFE" }
    );
}

fn get_valid_circuit() -> OuterCircuit<DefaultCycle> {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    let fixture = get_fixture();
    let x_val = InnerScalar::<DefaultCycle>::from(10u64);
    let circuit_inner = AddCircuit::with_public_input(x_val);
    let proof_inner = Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).expect("inner proof");
    let x_inner = vec![x_val];
    OuterCircuit::new((*fixture.vk_inner).clone(), x_inner, proof_inner)
}

struct MatrixExtractor {
    a_cols: Vec<Vec<(usize, Fr)>>,
    b_cols: Vec<Vec<(usize, Fr)>>,
    c_cols: Vec<Vec<(usize, Fr)>>,
    domain: GeneralEvaluationDomain<Fr>,
}

impl MatrixExtractor {
    fn new(cs: ConstraintSystemRef<Fr>) -> Self {
        let matrices = cs.to_matrices().expect("matrix extraction");
        let domain_size = cs.num_constraints().next_power_of_two();
        let domain = GeneralEvaluationDomain::<Fr>::new(domain_size).expect("domain");
        
        let num_vars = cs.num_instance_variables() + cs.num_witness_variables();
        let mut a_cols = vec![Vec::new(); num_vars];
        let mut b_cols = vec![Vec::new(); num_vars];
        let mut c_cols = vec![Vec::new(); num_vars];
        
        for (row, terms) in matrices.a.iter().enumerate() {
            if row < domain_size { for &(val, col) in terms { a_cols[col].push((row, val)); } }
        }
        for (row, terms) in matrices.b.iter().enumerate() {
            if row < domain_size { for &(val, col) in terms { b_cols[col].push((row, val)); } }
        }
        for (row, terms) in matrices.c.iter().enumerate() {
            if row < domain_size { for &(val, col) in terms { c_cols[col].push((row, val)); } }
        }
        
        Self { a_cols, b_cols, c_cols, domain }
    }
    
    fn get_column_polys(&self, col: usize) -> (DensePolynomial<Fr>, DensePolynomial<Fr>, DensePolynomial<Fr>) {
        let mut u_evals = vec![Fr::zero(); self.domain.size()];
        let mut v_evals = vec![Fr::zero(); self.domain.size()];
        let mut w_evals = vec![Fr::zero(); self.domain.size()];
        
        for &(row, val) in &self.a_cols[col] { u_evals[row] = val; }
        for &(row, val) in &self.b_cols[col] { v_evals[row] = val; }
        for &(row, val) in &self.c_cols[col] { w_evals[row] = val; }
        
        (
            DensePolynomial::from_coefficients_slice(&self.domain.ifft(&u_evals)),
            DensePolynomial::from_coefficients_slice(&self.domain.ifft(&v_evals)),
            DensePolynomial::from_coefficients_slice(&self.domain.ifft(&w_evals)),
        )
    }

    fn evaluate_column(&self, col: usize, r: Fr) -> (Fr, Fr, Fr) {
        let n_as_field = self.domain.size_as_field_element();
        let n_inv = n_as_field.inverse().unwrap();
        let z_h_at_r = r.pow([self.domain.size() as u64]) - Fr::one();
        let common = z_h_at_r * n_inv;

        let eval_sparse = |sparse: &Vec<(usize, Fr)>| -> Fr {
            let mut acc = Fr::zero();
            for &(row, val) in sparse {
                let omega_i = self.domain.element(row);
                let denom = r - omega_i;
                acc += (val * omega_i) * denom.inverse().unwrap();
            }
            acc * common
        };

        (
            eval_sparse(&self.a_cols[col]),
            eval_sparse(&self.b_cols[col]),
            eval_sparse(&self.c_cols[col]),
        )
    }
}

fn check_linearity(pub_polys: &[(DensePolynomial<Fr>, DensePolynomial<Fr>, DensePolynomial<Fr>)], num_pub: usize) -> bool {
    for i in 1..num_pub {
        for j in 1..num_pub {
            let prod = &pub_polys[i].0 * &pub_polys[j].1; 
            if !prod.is_zero() { return false; }
        }
    }
    true
}

fn compute_h_const(
    pub_polys: &[(DensePolynomial<Fr>, DensePolynomial<Fr>, DensePolynomial<Fr>)], 
    domain: &GeneralEvaluationDomain<Fr>
) -> DensePolynomial<Fr> {
    let mut a_pub = DensePolynomial::zero();
    let mut b_pub = DensePolynomial::zero();
    let mut c_pub = DensePolynomial::zero();
    for (u, v, w) in pub_polys {
        a_pub += u;
        b_pub += v;
        c_pub += w;
    }
    let numerator = &(&a_pub * &b_pub) - &c_pub;
    let (h, _) = numerator.divide_by_vanishing_poly(*domain);
    h
}

fn build_target(
    pub_polys: &[(DensePolynomial<Fr>, DensePolynomial<Fr>, DensePolynomial<Fr>)],
    h_const: &DensePolynomial<Fr>
) -> TrapdoorPolyVector {
    let mut ic = DensePolynomial::zero();
    for (u, _, _) in pub_polys { ic += u; }
    
    // Target * delta = alpha*beta*delta + gamma*delta*IC(x) - H_const(x)*delta^2
    TrapdoorPolyVector::new(vec![
        (TrapdoorMonomial::AlphaBetaDelta, DensePolynomial::from_coefficients_slice(&[Fr::one()])),
        (TrapdoorMonomial::GammaDelta, ic),
        (TrapdoorMonomial::DeltaSq, -h_const.clone()),
    ])
}

struct Basis {
    rows: Vec<Vec<Fr>>, 
    pivots: Vec<usize>,
}

impl Basis {
    fn new() -> Self { Self { rows: Vec::new(), pivots: Vec::new() } }
    
    fn reduce(&self, mut v: Vec<Fr>) -> Vec<Fr> {
        for (i, row) in self.rows.iter().enumerate() {
            let p = self.pivots[i];
            if !v[p].is_zero() {
                let factor = v[p];
                for k in p..v.len() { v[k] -= factor * row[k]; }
            }
        }
        v
    }
    
    fn insert(&mut self, v: Vec<Fr>) {
        let reduced = self.reduce(v);
        if let Some(p) = reduced.iter().position(|x| !x.is_zero()) {
            let inv = reduced[p].inverse().unwrap();
            let normalized: Vec<Fr> = reduced.iter().map(|x| *x * inv).collect();
            self.rows.push(normalized);
            self.pivots.push(p);
        }
    }
}

fn check_independence_streaming(
    extractor: &MatrixExtractor,
    pub_polys: &[(DensePolynomial<Fr>, DensePolynomial<Fr>, DensePolynomial<Fr>)],
    target: &TrapdoorPolyVector,
    num_pub: usize,
    num_vars: usize,
    seed: u64,
    check_idx: usize,
    total_checks: usize,
) -> bool {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let r = Fr::rand(&mut rng);
    
    let mut mono_set = std::collections::HashSet::new();
    for (m, _) in &target.components { mono_set.insert(m.clone()); }
    let all_monos = vec![
        TrapdoorMonomial::AlphaBetaDelta, TrapdoorMonomial::GammaDelta, TrapdoorMonomial::DeltaSq,
        TrapdoorMonomial::BetaSqU, TrapdoorMonomial::BetaU, TrapdoorMonomial::AlphaBetaV,
        TrapdoorMonomial::AlphaV, TrapdoorMonomial::BetaW, TrapdoorMonomial::W,
        TrapdoorMonomial::BetaUV, TrapdoorMonomial::AlphaVV, TrapdoorMonomial::WV,
        TrapdoorMonomial::BetaDeltaU, TrapdoorMonomial::AlphaDeltaV, TrapdoorMonomial::DeltaW,
        TrapdoorMonomial::DeltaUV, TrapdoorMonomial::DeltaPureUV,
        TrapdoorMonomial::AlphaDeltaV, TrapdoorMonomial::AlphaDeltaSq,
    ];
    for m in all_monos { mono_set.insert(m); }
    
    let mut monomials: Vec<_> = mono_set.into_iter().collect();
    monomials.sort();
    let mono_map: HashMap<_, _> = monomials.iter().enumerate().map(|(i, m)| (m.clone(), i)).collect();
    let num_dims = monomials.len();
    
    let mut basis = Basis::new();
    
    let mut add_basis_vec = |vec_map: Vec<(TrapdoorMonomial, Fr)>| {
        let mut v = vec![Fr::zero(); num_dims];
        for (m, val) in vec_map {
            if let Some(&idx) = mono_map.get(&m) { v[idx] += val; }
        }
        basis.insert(v);
    };
    
    let mut v_pub_r = Fr::zero();
    for (_, v, _) in pub_polys { v_pub_r += v.evaluate(&r); }
    
    let total_cols = num_vars;
    let step = std::cmp::max(1, total_cols / 20); 


    // The adversary has handles for Public Inputs (CRS) AND Witness Inputs (Arming).
    // Skipping 0..num_pub would be UNDER-POWERING the adversary (ignoring public handles).
    for k in 0..num_vars {
        if k % step == 0 {
            let pct = (k * 100) / total_cols;
            print!("\r[Independence Check {}/{}] Progress: {:3}%", check_idx, total_checks, pct);
            use std::io::Write;
            let _ = std::io::stdout().flush();
        }

        let (u_val, v_val, w_val) = extractor.evaluate_column(k, r);
        
        // 1. u_k * D_pub * delta -> (u)(beta+V)(delta) = beta*delta*u + delta*u*V
        add_basis_vec(vec![
            (TrapdoorMonomial::BetaDeltaU, u_val),
            (TrapdoorMonomial::DeltaUV, u_val * v_pub_r),
        ]);
        
        // 2. u_k * D_delta * delta -> u * delta^2
        add_basis_vec(vec![
            (TrapdoorMonomial::DeltaSq, u_val),
        ]);
        
        // 3. u_k * D_j * delta -> u * v_j * delta
        // Model as u * Any * delta -> DeltaPureUV * u (approx)
        add_basis_vec(vec![
            (TrapdoorMonomial::DeltaPureUV, u_val),
        ]);
        
        // 4. L_k * D_pub * delta -> (beta*u+alpha*v+w)(beta+V)
        // = beta^2*u + beta*u*V + alpha*beta*v + alpha*v*V + beta*w + w*V
        add_basis_vec(vec![
            (TrapdoorMonomial::BetaSqU, u_val),
            (TrapdoorMonomial::BetaU, u_val * v_pub_r),
            (TrapdoorMonomial::AlphaBetaV, v_val),
            (TrapdoorMonomial::AlphaV, v_val * v_pub_r),
            (TrapdoorMonomial::BetaW, w_val),
            (TrapdoorMonomial::W, w_val * v_pub_r),
        ]);
        
        // 5. L_k * D_delta * delta -> (beta*u+alpha*v+w) * delta
        // = beta*delta*u + alpha*delta*v + delta*w
        add_basis_vec(vec![
            (TrapdoorMonomial::BetaDeltaU, u_val),
            (TrapdoorMonomial::AlphaDeltaV, v_val),
            (TrapdoorMonomial::DeltaW, w_val),
        ]);
        
        // 6. L_k * D_j * delta -> (beta*u+alpha*v+w) * v_j
        // Model as (beta*u + alpha*v + w) * Any
        // = BetaUV * u + AlphaVV * v + WV * w
        add_basis_vec(vec![
            (TrapdoorMonomial::BetaUV, u_val),
            (TrapdoorMonomial::AlphaVV, v_val),
            (TrapdoorMonomial::WV, w_val),
        ]);
    }
    println!("\r[Independence Check {}/{}] Progress: 100%", check_idx, total_checks);
    
    // 7. Fixed handles
    // Alpha * D_pub * delta -> alpha(beta+V)delta = alpha*beta*delta + alpha*V*delta
    add_basis_vec(vec![
        (TrapdoorMonomial::AlphaBetaDelta, Fr::one()),
        (TrapdoorMonomial::AlphaDeltaV, v_pub_r),
    ]);
    // Alpha * D_delta * delta -> alpha * delta^2
    add_basis_vec(vec![
        (TrapdoorMonomial::AlphaDeltaSq, Fr::one()),
    ]);
    // Alpha * D_j * delta -> alpha * v_j * delta -> AlphaDeltaV * Any
    add_basis_vec(vec![
        (TrapdoorMonomial::AlphaDeltaV, Fr::one()),
    ]);
    
    // Check Target
    let mut target_vec = vec![Fr::zero(); num_dims];
    for (m, p) in &target.components {
        if let Some(&idx) = mono_map.get(&m) {
            target_vec[idx] = p.evaluate(&r);
        }
    }
    
    let residue = basis.reduce(target_vec);
    residue.iter().all(|x| x.is_zero()) == false 
}

// ============================================================================
// DIAGONAL BASIS SECURITY AUDIT
// ============================================================================
// 
// Verifies that the sparse diagonal bases don't leak the full Lagrange SRS.
// 
// The diagonal bases are: D_k = Σ_m Q_k(ω^m) · L_m for k ∈ diagonal_rows
// where Q_k(ω^m) = ω^k / (n·(ω^k - ω^m)) for m ≠ k, and (n-1)/(2n) for m = k.
//
// Security condition: rank(M) = d where M is the d×n coefficient matrix.
// This ensures each diagonal basis reveals exactly 1 dimension of information.

/// Audit the diagonal basis security for the lean prover.
/// Returns (d, n, rank, is_secure) where:
/// - d = number of diagonal rows
/// - n = domain size  
/// - rank = actual rank of coefficient matrix
/// - is_secure = true if rank == d (no degeneracy)
pub fn audit_diagonal_basis_security<C: ConstraintSynthesizer<Fr> + Clone>(
    circuit: C,
) -> (usize, usize, usize, bool) {
    use ark_poly::EvaluationDomain;
    
    let cs = ConstraintSystem::<Fr>::new_ref();
    circuit.clone().generate_constraints(cs.clone()).expect("synthesis");
    cs.finalize();
    
    let matrices = cs.to_matrices().expect("matrices");
    let num_constraints = cs.num_constraints();
    let num_inputs = cs.num_instance_variables();
    let num_pub = num_inputs;
    
    // Domain size (same as in compute_witness_bases)
    let qap_domain_size = num_constraints + num_inputs;
    let domain = GeneralEvaluationDomain::<Fr>::new(qap_domain_size)
        .or_else(|| GeneralEvaluationDomain::<Fr>::new(qap_domain_size.next_power_of_two()))
        .expect("domain");
    let n = domain.size();
    
    // Find diagonal rows (rows where both A and B have witness terms)
    let mut diagonal_rows = Vec::new();
    for k in 0..matrices.a.len().min(n) {
        let has_wit_a = matrices.a[k].iter().any(|&(_, col)| col >= num_pub);
        let has_wit_b = matrices.b[k].iter().any(|&(_, col)| col >= num_pub);
        if has_wit_a && has_wit_b {
            diagonal_rows.push(k);
        }
    }
    let d = diagonal_rows.len();
    
    if d == 0 {
        println!("[DiagAudit] No diagonal rows found. Trivially secure.");
        return (0, n, 0, true);
    }
    
    println!("[DiagAudit] Found {} diagonal rows out of {} domain size", d, n);
    println!("[DiagAudit] Ratio d/n = {:.4}%", (d as f64 / n as f64) * 100.0);
    
    // Build the coefficient matrix M where M[i][m] = Q_{k_i}(ω^m)
    // k_i is the i-th diagonal row
    let n_field = domain.size_as_field_element();
    let t0 = (n_field - Fr::one()) * (n_field + n_field).inverse().expect("2n invertible");
    
    // Precompute T[j] = 1 / (n * (1 - ω^j)) for j ≠ 0
    let mut coeffs_table = vec![Fr::zero(); n];
    coeffs_table[0] = t0;
    
    let mut denoms = Vec::with_capacity(n - 1);
    for j in 1..n {
        let omega_j = domain.element(j);
        denoms.push(n_field * (Fr::one() - omega_j));
    }
    ark_ff::batch_inversion(&mut denoms);
    for (j, inv) in denoms.into_iter().enumerate() {
        coeffs_table[j + 1] = inv;
    }
    
    // Build coefficient matrix (d rows, n columns)
    // M[i][m] = T[(m - k_i) mod n]
    let mut matrix: Vec<Vec<Fr>> = Vec::with_capacity(d);
    for &k in &diagonal_rows {
        let mut row = vec![Fr::zero(); n];
        for m in 0..n {
            let diff = if m >= k { m - k } else { m + n - k };
            row[m] = coeffs_table[diff];
        }
        matrix.push(row);
    }
    
    // Compute rank using Gaussian elimination
    let rank = compute_matrix_rank(&mut matrix, n);
    
    let is_secure = rank == d;
    
    println!("[DiagAudit] Coefficient matrix rank: {} (expected: {})", rank, d);
    if is_secure {
        println!("[DiagAudit] ✓ SECURE: Rank equals d, no degeneracy.");
        println!("[DiagAudit] Hidden subspace dimension: {} (out of {})", n - 1 - d, n - 1);
    } else {
        println!("[DiagAudit] ✗ WARNING: Rank {} < d = {}!", rank, d);
        println!("[DiagAudit] This means diagonal bases have unexpected linear dependencies.");
    }
    
    (d, n, rank, is_secure)
}

/// Compute the rank of a matrix using Gaussian elimination over a finite field.
fn compute_matrix_rank(matrix: &mut Vec<Vec<Fr>>, num_cols: usize) -> usize {
    let num_rows = matrix.len();
    if num_rows == 0 {
        return 0;
    }
    
    let mut rank = 0;
    let mut pivot_col = 0;
    
    for row in 0..num_rows {
        if pivot_col >= num_cols {
            break;
        }
        
        // Find pivot
        let mut pivot_row = None;
        for r in row..num_rows {
            if !matrix[r][pivot_col].is_zero() {
                pivot_row = Some(r);
                break;
            }
        }
        
        match pivot_row {
            Some(pr) => {
                // Swap rows
                matrix.swap(row, pr);
                
                // Scale pivot row
                let pivot_inv = matrix[row][pivot_col].inverse().expect("non-zero pivot");
                for c in pivot_col..num_cols {
                    matrix[row][c] *= pivot_inv;
                }
                
                // Eliminate column
                for r in 0..num_rows {
                    if r != row && !matrix[r][pivot_col].is_zero() {
                        let factor = matrix[r][pivot_col];
                        for c in pivot_col..num_cols {
                            let val = matrix[row][c] * factor;
                            matrix[r][c] -= val;
                        }
                    }
                }
                
                rank += 1;
                pivot_col += 1;
            }
            None => {
                // No pivot in this column, move to next
                pivot_col += 1;
                continue;
            }
        }
    }
    
    rank
}
