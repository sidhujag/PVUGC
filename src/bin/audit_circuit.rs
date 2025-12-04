//! PVUGC Trapdoor-Aware Audit Tool
//!
//! This tool audits circuits for algebraic security in the AGBGM (Algebraic Generic
//! Bilinear Group Model) for the PVUGC Witness Encryption scheme.
//!
//! ## Security Model
//!
//! With **Full Span Separation** (U, V, W all separated), the minimal secure architecture is:
//!
//! **REQUIRED:**
//! 1. Lean CRS (Baked Quotient/GT-Baking) - prevents quotient forgery
//! 2. Circuit Linearity - enables Baked Quotient strategy  
//! 3. Full Span Separation (U, V, W verified) - blocks all PK-based attacks
//! 4. Aggregation - prevents GT-Slicing attacks
//!
//! ## Audit Checks
//!
//! 1. **Linearity Check**: Verifies that Public Inputs do not multiply each other.
//! 2. **Span Separation Check**: Verifies U/V/W_pub ⊥ U/V/W_wit (critical for security!)
//! 3. **Independence Check**: Verifies target is outside adversary's span in AGBGM.
//!
//! ## Key Modeling Features
//!
//! - **ρ-Degree Separation**: Distinguishes Static (deg_ρ=0) vs Armed (deg_ρ=1) handles.
//!   Static GT table entries CANNOT reach the dynamic KEM target.
//! - **Span-Separated Pub/Wit**: Uses separate monomials (e.g., AlphaDeltaVPub vs AlphaDeltaVWit)
//!   to properly model algebraic orthogonality when span separation holds.
//!
//! Optimization: Uses streaming column processing + Incremental Basis + Sparse Eval.

use ark_ff::{Field, One, Zero};
use ark_groth16::Groth16;
use ark_poly::{
    univariate::DensePolynomial, DenseUVPolynomial, EvaluationDomain, GeneralEvaluationDomain,
    Polynomial,
};
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef, LinearCombination, Variable,
};
use ark_snark::SNARK;
use ark_std::rand::SeedableRng;
use ark_std::UniformRand;
use arkworks_groth16::{
    outer_compressed::{DefaultCycle, InnerE, InnerScalar, OuterCircuit, OuterFr},
    test_circuits::AddCircuit,
    test_fixtures::get_fixture,
};
use rayon::prelude::*;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};

type Fr = OuterFr;

// All handles/targets are multiplied by delta to clear denominators from L-queries.
// Base ring: F[alpha, beta, gamma, delta, rho, x]
//
// IMPORTANT: ρ-DEGREE SEPARATION
// The audit distinguishes between:
// - Static handles (deg_ρ = 0): GT table entries like e(α, β), e(α, v_i)
// - Armed handles (deg_ρ = 1): Dynamically armed values like e(L_k, δ^ρ)
// Static handles CANNOT synthesize the dynamic KEM target (which has deg_ρ = 1).
// The monomial names below indicate ρ-degree:
// - Monomials WITHOUT "Static" suffix: Armed (deg_ρ = 1)
// - Monomials WITH "Static" suffix: Static (deg_ρ = 0)
//
// IMPORTANT: FULL SPAN SEPARATION (U, V, W)
// When span separation holds for ALL three polynomial types:
// - U_pub ⊥ U_wit, V_pub ⊥ V_wit, W_pub ⊥ W_wit
// The adversary cannot synthesize public components from witness handles.
// We model this by using SEPARATE monomials for Pub vs Wit.

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum TrapdoorMonomial {
    // ============================================================
    // TARGET TERMS (Armed, deg_ρ = 1) - All PUBLIC polynomials!
    // ============================================================
    // Standard Groth16 extraction: e(A,B) - e(C,δ) = e(α,β) + e(IC(x), γ)
    // Since IC(x) = Σ x_i · (β·u_i + α·v_i + w_i)/γ, pairing with γ gives:
    //   e(IC(x), γ) = β·U_pub + α·V_pub + W_pub (γ cancels!)
    // So the target is: ρ·(α·β + β·U_pub + α·V_pub + W_pub)
    // Under δ-normalization: ρ·δ·(α·β + β·U_pub + α·V_pub + W_pub)
    AlphaBetaDelta, // ρ * alpha * beta * delta (fixed)
    DeltaSq,        // ρ * delta^2 (from quotient H)

    // ============================================================
    // SPAN-SEPARATED TARGET COMPONENTS (Pub vs Wit)
    // ============================================================
    // These are DISTINCT monomials when span separation holds.
    // The target uses PUBLIC polynomials (U_pub, V_pub, W_pub).
    // L-query handles provide WITNESS polynomials (U_wit, V_wit, W_wit).
    // If span separation holds, witness handles CANNOT synthesize target.
    
    // β·δ·U components
    BetaDeltaUPub, // ρ * beta * delta * U_pub (TARGET component)
    BetaDeltaUWit, // ρ * beta * delta * U_wit (from witness L-queries)
    
    // α·δ·V components
    AlphaDeltaVPub, // ρ * alpha * delta * V_pub (from bundled α handle + TARGET)
    AlphaDeltaVWit, // ρ * alpha * delta * V_wit (from witness L-queries)
    
    // δ·W components  
    DeltaWPub, // ρ * delta * W_pub (TARGET component)
    DeltaWWit, // ρ * delta * W_wit (from witness L-queries)

    // ============================================================
    // HANDLE TERMS from L_k * D_pub (Armed, deg_ρ = 1)
    // ============================================================
    // These are from WITNESS L-queries, so they use witness polynomials
    BetaSqU,    // ρ * beta^2 * u_wit
    BetaU,      // ρ * beta * u_wit * V
    AlphaBetaV, // ρ * alpha * beta * v_wit (available in standard Groth16)
    AlphaV,     // ρ * alpha * v_wit * V (available in standard Groth16)
    BetaW,      // ρ * beta * w_wit
    W,          // ρ * w_wit * V

    // Result is (beta*u + alpha*v + w)(v_j) - full L-query
    BetaUV,  // ρ * beta * u_wit * v
    AlphaVV, // ρ * alpha * v_wit * v (available in standard Groth16)
    WV,      // ρ * w_wit * v

    // ============================================================
    // OTHER HANDLE TERMS (Armed, deg_ρ = 1)
    // ============================================================
    DeltaUV,     // ρ * delta * u * V
    DeltaPureUV, // ρ * delta * u * v
    AlphaDeltaSq, // ρ * alpha * delta^2
    BetaV,       // ρ * v * beta
    PureVV,      // ρ * v * v

    // ============================================================
    // STATIC GT TABLE HANDLES (Static, deg_ρ = 0)
    // ============================================================
    // These are precomputed GT elements, NOT armed with ρ.
    // They CANNOT synthesize the target because target has deg_ρ = 1.
    // We keep them as separate monomials to prevent incorrect cancellation.
    AlphaBetaStatic,  // alpha * beta (deg_ρ = 0)
    AlphaDeltaStatic, // alpha * delta (deg_ρ = 0)
    AlphaVStatic,     // alpha * v (deg_ρ = 0)
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
    fn name(&self) -> &'static str {
        "Production OuterCircuit"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        self.0.clone().generate_constraints(cs)
    }
}

struct MockLinear;
impl AuditSubject for MockLinear {
    fn name(&self) -> &'static str {
        "Mock Linear (Safe)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        // Public input is a hash h = w1 + w2 (fixed here to 5)
        let hash_val = Fr::from(5u64);
        let mut one_lc = LinearCombination::zero();
        one_lc += (Fr::one(), Variable::One);

        let h_pub = cs.new_input_variable(|| Ok(hash_val))?;

        // Witness values for the underlying statement
        let w1 = cs.new_witness_variable(|| Ok(Fr::from(2u64)))?;
        let w2 = cs.new_witness_variable(|| Ok(Fr::from(3u64)))?;

        // Witness copy of the hash
        let h_wit = cs.new_witness_variable(|| Ok(hash_val))?;

        // Witness-only relation: w1 + w2 = h_wit
        let mut lc_b = LinearCombination::zero();
        lc_b += (Fr::one(), w1);
        lc_b += (Fr::one(), w2);
        let mut lc_c = LinearCombination::zero();
        lc_c += (Fr::one(), h_wit);
        cs.enforce_constraint(one_lc.clone(), lc_b, lc_c)?;

        // Public binding: 1 * h_pub = h_wit
        let mut lc_b2 = LinearCombination::zero();
        lc_b2 += (Fr::one(), h_pub);
        let mut lc_c2 = LinearCombination::zero();
        lc_c2 += (Fr::one(), h_wit);
        cs.enforce_constraint(one_lc, lc_b2, lc_c2)?;
        Ok(())
    }
}

struct MockQuadratic;
impl AuditSubject for MockQuadratic {
    fn name(&self) -> &'static str {
        "Mock Quadratic (Unsafe)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        use ark_r1cs_std::prelude::*;
        let x = ark_r1cs_std::fields::fp::FpVar::new_input(cs.clone(), || Ok(Fr::one()))?;
        let one = ark_r1cs_std::fields::fp::FpVar::constant(Fr::from(1));
        x.mul_equals(&x, &one)?;
        Ok(())
    }
}

/// TEST CIRCUIT: V Span Separation SHOULD FAIL
/// For v_pub ∈ span(v_wit), we need v_pub = c * v_wit (scalar multiple).
/// 
/// SIMPLE: Put x and w in B at EXACTLY the same single row.
/// Then v_x = L_0 and v_w = L_0, so v_x = 1 * v_w.
struct MockSpanViolation;
impl AuditSubject for MockSpanViolation {
    fn name(&self) -> &'static str {
        "Mock V-Span Violation (SHOULD FAIL V-span)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        let x = cs.new_input_variable(|| Ok(Fr::from(1u64)))?;  // public
        let w = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?; // witness
        let one = Variable::One;
        
        // SINGLE constraint that puts BOTH x and w in B at row 0:
        // A=1, B=(x+w), C=2
        // This gives: v_x = L_0 and v_w = L_0
        // So v_x = 1 * v_w → v_pub IS IN span(v_wit)!
        let lc_a = LinearCombination::from((Fr::one(), one));
        let mut lc_b = LinearCombination::zero();
        lc_b += (Fr::one(), x);  // x in B at row 0
        lc_b += (Fr::one(), w);  // w in B at row 0 (SAME ROW!)
        let lc_c = LinearCombination::from((Fr::from(2u64), one));
        cs.enforce_constraint(lc_a, lc_b, lc_c)?;
        
        // Add a dummy constraint to satisfy minimum circuit requirements
        // 1 * 1 = 1
        let lc_a2 = LinearCombination::from((Fr::one(), one));
        let lc_b2 = LinearCombination::from((Fr::one(), one));
        let lc_c2 = LinearCombination::from((Fr::one(), one));
        cs.enforce_constraint(lc_a2, lc_b2, lc_c2)?;
        
        Ok(())
    }
}

/// TEST CIRCUIT: U Span Separation SHOULD FAIL
/// Put x and w in A at same row (so u_x = u_w).
/// Note: This also needs x in B for statement dependence.
struct MockUSpanViolation;
impl AuditSubject for MockUSpanViolation {
    fn name(&self) -> &'static str {
        "Mock U-Span Violation (SHOULD FAIL U-span)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        let x = cs.new_input_variable(|| Ok(Fr::from(1u64)))?;  // public
        let w = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?; // witness
        let one = Variable::One;
        
        // Constraint 0: Put BOTH x and w in A at SAME row
        // A=(x+w), B=1, C=(x+w)
        // This gives: u_x = L_0 and u_w = L_0
        // So u_x = 1 * u_w → u_pub IS IN span(u_wit)!
        let mut lc_a0 = LinearCombination::zero();
        lc_a0 += (Fr::one(), x);  // x in A at row 0
        lc_a0 += (Fr::one(), w);  // w in A at row 0 (SAME ROW!)
        let lc_b0 = LinearCombination::from((Fr::one(), one));
        let mut lc_c0 = LinearCombination::zero();
        lc_c0 += (Fr::one(), x);
        lc_c0 += (Fr::one(), w);
        cs.enforce_constraint(lc_a0, lc_b0, lc_c0)?;
        
        // Constraint 1: Put x in B for statement dependence (separate row)
        // 1 * x = x
        let lc_a1 = LinearCombination::from((Fr::one(), one));
        let lc_b1 = LinearCombination::from((Fr::one(), x));
        let lc_c1 = LinearCombination::from((Fr::one(), x));
        cs.enforce_constraint(lc_a1, lc_b1, lc_c1)?;
        
        Ok(())
    }
}

/// TEST CIRCUIT: W Span Separation SHOULD FAIL (but V should pass)
/// Put x and w in C at same row (so w_x = w_w), but x in B at different row than w.
struct MockWSpanViolation;
impl AuditSubject for MockWSpanViolation {
    fn name(&self) -> &'static str {
        "Mock W-Span Violation (SHOULD FAIL W-span, V-span OK)"
    }
    fn synthesize(&self, cs: ConstraintSystemRef<Fr>) -> ark_relations::r1cs::Result<()> {
        let x = cs.new_input_variable(|| Ok(Fr::from(1u64)))?;
        let w = cs.new_witness_variable(|| Ok(Fr::from(1u64)))?;
        let one = Variable::One;
        
        // Constraint 0: Put x in B (for statement dependence) but NOT where w is in B
        // 1 * x = 1  → v_x = L_0
        let lc_a0 = LinearCombination::from((Fr::one(), one));
        let lc_b0 = LinearCombination::from((Fr::one(), x));
        let lc_c0 = LinearCombination::from((Fr::one(), one));
        cs.enforce_constraint(lc_a0, lc_b0, lc_c0)?;
        
        // Constraint 1: Put BOTH x and w in C at SAME row
        // 1 * 1 = x + w  → w_x = L_1 and w_w = L_1
        // So w_x = 1 * w_w → w_pub IS IN span(w_wit)!
        let lc_a1 = LinearCombination::from((Fr::one(), one));
        let lc_b1 = LinearCombination::from((Fr::one(), one));
        let mut lc_c1 = LinearCombination::zero();
        lc_c1 += (Fr::one(), x);  // x in C at row 1
        lc_c1 += (Fr::one(), w);  // w in C at row 1 (SAME ROW!)
        cs.enforce_constraint(lc_a1, lc_b1, lc_c1)?;
        
        Ok(())
    }
}

fn main() {
    println!("PVUGC Production Audit Tool");
    println!("===========================\n");

    let subjects: Vec<Box<dyn AuditSubject>> = vec![
        Box::new(MockLinear),
        Box::new(MockQuadratic),
        Box::new(MockSpanViolation),    // Should FAIL V-span
        Box::new(MockUSpanViolation),   // Should FAIL U-span
        Box::new(MockWSpanViolation),   // Should FAIL W-span
        Box::new(ProductionSubject(get_valid_circuit())),
    ];

    for subject in subjects {
        println!(">>> AUDITING: {} <<<", subject.name());
        run_audit(subject.as_ref());
        println!("\n");
    }
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

    // 0. Check public column structure (Lean CRS diagnostic)
    let mut public_inputs_a_zero = true; // Columns 1..num_pub (actual public inputs)
    let mut public_inputs_b_nonzero = true; // Columns 1..num_pub MUST be in B
    let constant_one_has_a = !extractor.a_cols[0].is_empty(); // Column 0 (constant "1")

    for i in 1..num_pub {
        // Skip column 0 (constant "1" is expected to have A entries)
        let a_count = extractor.a_cols[i].len();
        let b_count = extractor.b_cols[i].len();
        let c_count = extractor.c_cols[i].len();

        println!(
            "  [Column {}] A={}, B={}, C={}",
            i, a_count, b_count, c_count
        );

        if a_count > 0 {
            public_inputs_a_zero = false;
            println!(
                "  [FAIL] Column {} has A entries! Public inputs must be A-free.",
                i
            );
        }

        if b_count == 0 {
            public_inputs_b_nonzero = false;
            println!(
                "  [FAIL] Column {} has B=0! Public inputs must be in B for statement dependency.",
                i
            );
        }

        // Check if IC_i would be zero (security issue!)
        if b_count == 0 && c_count == 0 {
            println!(
                "  [SECURITY] Column {} has v_i=0 AND w_i=0 → IC_i=0 → PUBLIC INPUT NOT VERIFIED!",
                i
            );
        }
    }

    if constant_one_has_a {
        println!(
            "  [Column 0] Constant '1' has {} A entries (expected, baked into α)",
            extractor.a_cols[0].len()
        );
    }

    if public_inputs_a_zero && public_inputs_b_nonzero {
        println!("[PASS] Public input structure valid (A=0, B>0) → Lean CRS compatible & Statement Dependent");
    } else {
        println!("[FAIL] Public input structure INVALID (Check A=0 and B>0 requirements)");
    }

    // Additional guard: ensure no public column appears in both A and B on the same row
    let no_pub_ab_overlap = check_public_ab_overlap(&extractor, num_pub);
    if no_pub_ab_overlap {
        println!("[PASS] Public columns never share A/B rows.");
    } else {
        println!("[FAIL] Public column appears in both A and B on same row.");
    }

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

    // 1.5 Mixing Check (Public * Witness)
    let is_unmixed = check_mixing(&extractor, num_pub, num_pub + num_wit);
    if is_unmixed {
        println!("[PASS] Mixing Check.");
    } else {
        println!("[FAIL] Mixing Check (Public*Witness detected).");
    }

    // 1.6 Span Separation Checks (U_pub ⊥ U_wit, V_pub ⊥ V_wit, W_pub ⊥ W_wit)
    println!("\n--- Span Separation Analysis ---");
    
    // V (B-matrix) - CRITICAL for α-handle attack
    let v_span_separated = check_span_separation_matrix(
        &extractor, num_pub, num_pub + num_wit, "V", "B",
        |e, i| &e.b_cols[i],
        |e, i, r| { let (_, v, _) = e.evaluate_column(i, r); v },
    );
    if v_span_separated {
        println!("[PASS] V Span Separation (V_pub ⊥ V_wit) → α-handle attack blocked.");
    } else {
        println!("[FAIL] V Span Separation (V_pub ∈ span V_wit) → Lean CRS required!");
    }
    
    // U (A-matrix) - for L-query derived β·U attacks
    let u_span_separated = check_span_separation_matrix(
        &extractor, num_pub, num_pub + num_wit, "U", "A",
        |e, i| &e.a_cols[i],
        |e, i, r| { let (u, _, _) = e.evaluate_column(i, r); u },
    );
    if u_span_separated {
        println!("[PASS] U Span Separation (U_pub ⊥ U_wit) → β·U synthesis blocked.");
    } else {
        println!("[WARN] U Span Separation failed (U_pub ∈ span U_wit) → L-query risk.");
    }
    
    // W (C-matrix) - for L-query derived W attacks
    let w_span_separated = check_span_separation_matrix(
        &extractor, num_pub, num_pub + num_wit, "W", "C",
        |e, i| &e.c_cols[i],
        |e, i, r| { let (_, _, w) = e.evaluate_column(i, r); w },
    );
    if w_span_separated {
        println!("[PASS] W Span Separation (W_pub ⊥ W_wit) → W synthesis blocked.");
    } else {
        println!("[WARN] W Span Separation failed (W_pub ∈ span W_wit) → L-query risk.");
    }
    
    // Combined span separation result
    let full_span_separated = v_span_separated && u_span_separated && w_span_separated;
    
    println!("--- End Span Separation ---\n");

    // 2. Independence Check
    let h_const = compute_h_const(&pub_polys, &extractor.domain);
    let target = build_target(&pub_polys, &h_const);

    let num_checks = 1;
    let all_safe = run_independence_checks(
        "",
        &extractor,
        &pub_polys,
        &target,
        num_pub + num_wit,
        num_checks,
    );

    // Final verdict
    let fully_safe = is_linear && is_unmixed && all_safe && no_pub_ab_overlap;
    
    println!("\n=== SECURITY SUMMARY (AGBGM) ===");
    println!("Linearity:          {}", if is_linear { "PASS" } else { "FAIL" });
    println!("No Pub/Wit Mix:     {}", if is_unmixed { "PASS" } else { "FAIL" });
    println!("No Pub A/B Overlap: {}", if no_pub_ab_overlap { "PASS" } else { "FAIL" });
    println!("V Span Separation:  {}", if v_span_separated { "PASS" } else { "FAIL" });
    println!("U Span Separation:  {}", if u_span_separated { "PASS" } else { "FAIL" });
    println!("W Span Separation:  {}", if w_span_separated { "PASS" } else { "FAIL" });
    println!("Independence:       {}", if all_safe { "PASS" } else { "FAIL" });
    
    // Full span separation is THE critical security property
    if full_span_separated {
        println!("\n✅ FULL SPAN SEPARATION VERIFIED (U, V, W all orthogonal)!");
        println!("");
        println!("   This enables STANDARD GROTH16 architecture:");
        println!("   • Standard L-queries are SAFE");
        println!("   • Standard IC algebra");
        println!("   • Standard decap works (proof-agnostic key extraction)");
        println!("");
        println!("   Attack blocking (AGBGM verified):");
        println!("   • V-span blocks: e([α]_1, D_pub^ρ) pollution cancellation");
        println!("   • U-span blocks: β·U_pub synthesis from witness L-queries");
        println!("   • W-span blocks: W_pub synthesis from witness L-queries");
    } else {
        if !v_span_separated {
            println!("\n⚠️  V SPAN SEPARATION FAILED!");
            println!("   V_pub ∈ span(V_wit), so:");
            println!("   • e([α]_1, D_pub^ρ) pollution CAN be cancelled");
            println!("   • MUST use Lean CRS (remove [α]_1 from public PK)");
        }
        
        if !u_span_separated || !w_span_separated {
            println!("\n⚠️  U/W SPAN SEPARATION FAILED!");
            println!("   Residue synthesis attack possible:");
            println!("   • e(L_k, δ^ρ) gives ρ·(β·u_k + w_k)");
            println!("   • If U_pub or W_pub in witness span, can synthesize target");
            println!("   • This is a fundamental issue - circuit redesign may be needed");
        }
    }

    println!(
        "\nRESULT: {}",
        if fully_safe && full_span_separated {
            "✅ SECURE (Standard Groth16 with Full Span Separation)"
        } else if fully_safe {
            "⚠️  CONDITIONALLY SAFE (requires additional mitigations)"
        } else {
            "❌ UNSAFE"
        }
    );
    
    if fully_safe && full_span_separated {
        println!("\n=== MINIMAL REQUIRED ARCHITECTURE ===");
        println!("1. Lean CRS (Baked Quotient/GT-Baking) - quotient forgery prevention");
        println!("2. Circuit Linearity - verified above");
        println!("3. Full Span Separation - verified above");
        println!("4. Aggregation - prevents GT-Slicing (verify separately)");
    }
}

fn check_public_ab_overlap(extractor: &MatrixExtractor, num_pub: usize) -> bool {
    for col in 1..num_pub {
        if extractor.a_cols[col].is_empty() || extractor.b_cols[col].is_empty() {
            continue;
        }
        let rows_b: HashSet<usize> = extractor.b_cols[col].iter().map(|(row, _)| *row).collect();
        for (row, _) in &extractor.a_cols[col] {
            if rows_b.contains(row) {
                println!(
                    "  [FAIL] Column {} appears in both A and B on row {}",
                    col, row
                );
                return false;
            }
        }
    }
    true
}

fn check_mixing(extractor: &MatrixExtractor, num_pub: usize, num_vars: usize) -> bool {
    let domain_size = extractor.domain.size();
    let mut rows_pub_a = vec![false; domain_size];
    let mut rows_pub_b = vec![false; domain_size];

    // Mark rows where Public Inputs (excluding 1) appear in A and B
    for i in 1..num_pub {
        for &(row, _) in &extractor.a_cols[i] {
            rows_pub_a[row] = true;
        }
        for &(row, _) in &extractor.b_cols[i] {
            rows_pub_b[row] = true;
        }
    }

    // Check Witness columns
    for j in num_pub..num_vars {
        // If Witness in A, check if Row has Public in B
        for &(row, _) in &extractor.a_cols[j] {
            if rows_pub_b[row] {
                return false;
            }
        }
        // If Witness in B, check if Row has Public in A
        for &(row, _) in &extractor.b_cols[j] {
            if rows_pub_a[row] {
                return false;
            }
        }
    }
    true
}

/// Generalized Span Separation Check for any matrix (A, B, or C)
/// 
/// Checks if public polynomial P_pub is NOT in span of witness polynomials P_wit.
/// Uses direct row-overlap check for reliability.
/// 
/// Parameters:
/// - matrix_name: "U", "V", or "W" for display
/// - col_name: "A", "B", or "C" for display  
/// - get_col: closure to get column entries from extractor
/// - eval_col: closure to evaluate column polynomial at a point
fn check_span_separation_matrix<F, G>(
    extractor: &MatrixExtractor, 
    num_pub: usize, 
    num_vars: usize,
    matrix_name: &str,
    col_name: &str,
    get_col: F,
    eval_col: G,
) -> bool 
where
    F: Fn(&MatrixExtractor, usize) -> &Vec<(usize, Fr)>,
    G: Fn(&MatrixExtractor, usize, Fr) -> Fr + Sync,
{
    let num_wit = num_vars - num_pub;
    if num_wit == 0 {
        println!("  [{}_SPAN] No witness columns to check.", matrix_name);
        return true;
    }
    
    // Collect all rows where public inputs (1..num_pub) have entries in this matrix
    let mut pub_rows: HashSet<usize> = HashSet::new();
    for i in 1..num_pub {
        for &(row, _) in get_col(extractor, i) {
            pub_rows.insert(row);
        }
    }
    
    if pub_rows.is_empty() {
        println!("  [{}_SPAN] Public inputs have no {}-entries ({}_pub = 0). Trivially separated.", 
                 matrix_name, col_name, matrix_name.to_lowercase());
        return true;
    }
    
    println!("  [{}_SPAN] Public inputs have {}-entries at {} rows: {:?}", 
             matrix_name, col_name, pub_rows.len(), 
             pub_rows.iter().take(5).collect::<Vec<_>>());
    
    // Check if ANY witness column has entries at those same rows
    let mut overlapping_witnesses: Vec<(usize, Vec<usize>)> = Vec::new();
    
    for j in num_pub..num_vars {
        let mut overlap_rows: Vec<usize> = Vec::new();
        for &(row, _) in get_col(extractor, j) {
            if pub_rows.contains(&row) {
                overlap_rows.push(row);
            }
        }
        if !overlap_rows.is_empty() {
            overlapping_witnesses.push((j, overlap_rows));
        }
    }
    
    if overlapping_witnesses.is_empty() {
        println!("  [{}_SPAN] No witness {}-entries overlap with public {}-rows.", 
                 matrix_name, col_name, col_name);
        println!("  [{}_SPAN] By Lagrange orthogonality: {}_pub NOT in span({}_wit)", 
                 matrix_name, matrix_name.to_lowercase(), matrix_name.to_lowercase());
        return true;
    }
    
    // There ARE overlapping witnesses - need full span check
    // Example: p on {r1}, w1 on {r1,r2}, w2 on {r2} -> p = w1 - w2 is in span
    println!("  [{}_SPAN] {} witness columns have {}-entries overlapping public rows", 
             matrix_name, overlapping_witnesses.len(), col_name);
    
    // Use sampling to verify if polynomial span separation holds
    // Include ALL witness columns (num_pub..num_vars), not just overlapping ones
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(98765);
    
    // Include ALL witness columns
    let all_witnesses: Vec<usize> = (num_pub..num_vars).collect();
    let num_witnesses = all_witnesses.len();
    
    if num_witnesses == 0 {
        println!("  [{}_SPAN] No witness columns - trivially separated", matrix_name);
        return true;
    }
    
    // Need more samples than witness columns for reliable span test
    // But cap it to avoid excessive computation
    let num_samples = std::cmp::min(std::cmp::max(100, num_witnesses + 20), 300);
    
    println!("  [{}_SPAN] Building evaluation matrix: {} samples x {} witnesses...", 
             matrix_name, num_samples, num_witnesses);
    
    let mut samples: Vec<Fr> = Vec::new();
    for _ in 0..num_samples {
        let mut sample = Fr::rand(&mut rng);
        while sample.is_zero() {
            sample = Fr::rand(&mut rng);
        }
        samples.push(sample);
    }
    
    // Pre-build witness evaluation matrix (shared across public columns)
    // Each sample row is computed independently
    let start_time = std::time::Instant::now();
    let progress = AtomicUsize::new(0);
    
    println!("  [{}_SPAN] Using {} CPU cores for parallel evaluation...", 
             matrix_name, rayon::current_num_threads());
    
    let wit_matrix: Vec<Vec<Fr>> = samples
        .par_iter()
        .map(|sample| {
            let row: Vec<Fr> = all_witnesses
                .iter()
                .map(|&j| eval_col(extractor, j, *sample))
                .collect();
            
            let done = progress.fetch_add(1, Ordering::Relaxed) + 1;
            if done % 50 == 0 || done == num_samples {
                eprint!("\r  [{}_SPAN] Evaluating witnesses: {}/{} samples...", 
                       matrix_name, done, num_samples);
            }
            row
        })
        .collect();
    
    eprintln!(" done ({:.2?})", start_time.elapsed());
    
    let mut all_separated = true;
    let num_pub_to_check = num_pub - 1; // Skip column 0 (constant)
    
    for (idx, i) in (1..num_pub).enumerate() {
        // Get public polynomial evaluations
        let mut pub_evals: Vec<Fr> = Vec::new();
        for sample in &samples {
            pub_evals.push(eval_col(extractor, i, *sample));
        }
        
        // Check if public polynomial is identically zero (trivially separated)
        if pub_evals.iter().all(|x| x.is_zero()) {
            continue;
        }
        
        let in_span = check_vector_in_column_span(&wit_matrix, &pub_evals);
        
        if in_span {
            println!("  [{}_SPAN FAIL] Public column {} is IN span of ALL {} witness columns", 
                     matrix_name, i, num_witnesses);
            all_separated = false;
        }
        
        // Progress for public columns
        if (idx + 1) % 5 == 0 || idx + 1 == num_pub_to_check {
            print!("\r  [{}_SPAN] Checking public columns: {}/{}...", 
                   matrix_name, idx + 1, num_pub_to_check);
            use std::io::Write;
            std::io::stdout().flush().ok();
        }
    }
    if num_pub_to_check > 0 {
        println!(" done");
    }
    
    all_separated
}

/// Check if target vector is in the column span of matrix
/// Uses Gaussian elimination with augmented matrix
fn check_vector_in_column_span(matrix: &[Vec<Fr>], target: &[Fr]) -> bool {
    if matrix.is_empty() || matrix[0].is_empty() {
        // No witness columns - target must be zero
        return target.iter().all(|x| x.is_zero());
    }
    
    let num_rows = matrix.len();
    let num_cols = matrix[0].len();
    
    // With more rows than columns, we can properly check span membership
    // Build augmented matrix [M | target] and check consistency
    
    let mut aug: Vec<Vec<Fr>> = Vec::new();
    for (row_idx, row) in matrix.iter().enumerate() {
        let mut aug_row = row.clone();
        aug_row.push(target[row_idx]); // Augment with target
        aug.push(aug_row);
    }
    
    // Gaussian elimination
    let mut pivot_row = 0;
    for col in 0..num_cols {
        // Find pivot
        let mut found = false;
        for row in pivot_row..num_rows {
            if !aug[row][col].is_zero() {
                // Swap rows
                aug.swap(row, pivot_row);
                found = true;
                break;
            }
        }
        
        if !found {
            continue; // No pivot in this column
        }
        
        // Normalize pivot row
        let inv = aug[pivot_row][col].inverse().unwrap();
        for j in col..=num_cols {
            aug[pivot_row][j] *= inv;
        }
        
        // Eliminate other rows
        for row in 0..num_rows {
            if row != pivot_row && !aug[row][col].is_zero() {
                let factor = aug[row][col];
                // Copy pivot row values to avoid borrow conflict
                let pivot_vals: Vec<Fr> = aug[pivot_row][col..=num_cols].to_vec();
                for (j_offset, pivot_val) in pivot_vals.iter().enumerate() {
                    let j = col + j_offset;
                    aug[row][j] -= factor * pivot_val;
                }
            }
        }
        
        pivot_row += 1;
        if pivot_row >= num_rows {
            break;
        }
    }
    
    // After elimination, check if system is consistent
    // A row of form [0, 0, ..., 0 | b] where b != 0 means inconsistent
    for row in &aug {
        let all_zero_except_last = row[..num_cols].iter().all(|x| x.is_zero());
        if all_zero_except_last && !row[num_cols].is_zero() {
            return false; // Inconsistent - target NOT in span
        }
    }
    
    true // Target IS in the column span
}

fn get_valid_circuit() -> OuterCircuit<DefaultCycle> {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
    let fixture = get_fixture();
    let x_val = InnerScalar::<DefaultCycle>::from(10u64);
    let circuit_inner = AddCircuit::with_public_input(x_val);
    let proof_inner =
        Groth16::<InnerE>::prove(&fixture.pk_inner, circuit_inner, &mut rng).expect("inner proof");

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
            if row < domain_size {
                for &(val, col) in terms {
                    a_cols[col].push((row, val));
                }
            }
        }
        for (row, terms) in matrices.b.iter().enumerate() {
            if row < domain_size {
                for &(val, col) in terms {
                    b_cols[col].push((row, val));
                }
            }
        }
        for (row, terms) in matrices.c.iter().enumerate() {
            if row < domain_size {
                for &(val, col) in terms {
                    c_cols[col].push((row, val));
                }
            }
        }

        Self {
            a_cols,
            b_cols,
            c_cols,
            domain,
        }
    }

    fn get_column_polys(
        &self,
        col: usize,
    ) -> (
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    ) {
        let mut u_evals = vec![Fr::zero(); self.domain.size()];
        let mut v_evals = vec![Fr::zero(); self.domain.size()];
        let mut w_evals = vec![Fr::zero(); self.domain.size()];

        for &(row, val) in &self.a_cols[col] {
            u_evals[row] = val;
        }
        for &(row, val) in &self.b_cols[col] {
            v_evals[row] = val;
        }
        for &(row, val) in &self.c_cols[col] {
            w_evals[row] = val;
        }

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

fn check_linearity(
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    num_pub: usize,
) -> bool {
    for i in 1..num_pub {
        for j in 1..num_pub {
            let prod = &pub_polys[i].0 * &pub_polys[j].1;
            if !prod.is_zero() {
                return false;
            }
        }
    }
    true
}

fn compute_h_const(
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    domain: &GeneralEvaluationDomain<Fr>,
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
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    h_const: &DensePolynomial<Fr>,
) -> TrapdoorPolyVector {
    // Reconstruct L_pub components
    // L_pub = Sum x_i (beta u_i + alpha v_i + w_i)
    // Normalized Target (x delta) = alpha*beta*delta + delta * L_pub - H*delta^2
    // = alpha*beta*delta + beta*delta*U + alpha*delta*V + delta*W - H*delta^2

    let mut u_sum = DensePolynomial::zero();
    let mut v_sum = DensePolynomial::zero();
    let mut w_sum = DensePolynomial::zero();

    for (u, v, w) in pub_polys {
        u_sum += u;
        v_sum += v;
        w_sum += w;
    }

    // TARGET uses PUBLIC polynomials (U_pub, V_pub, W_pub) from standard IC(x)
    // These are span-separated from witness polynomials.
    TrapdoorPolyVector::new(vec![
        (
            TrapdoorMonomial::AlphaBetaDelta,
            DensePolynomial::from_coefficients_slice(&[Fr::one()]),
        ),
        (TrapdoorMonomial::BetaDeltaUPub, u_sum),   // β·δ·U_pub
        (TrapdoorMonomial::AlphaDeltaVPub, v_sum),  // α·δ·V_pub
        (TrapdoorMonomial::DeltaWPub, w_sum),       // δ·W_pub
        (TrapdoorMonomial::DeltaSq, -h_const.clone()),
    ])
}

struct Basis {
    rows: Vec<Vec<Fr>>,
    pivots: Vec<usize>,
}

impl Basis {
    fn new() -> Self {
        Self {
            rows: Vec::new(),
            pivots: Vec::new(),
        }
    }

    fn reduce(&self, mut v: Vec<Fr>) -> Vec<Fr> {
        for (i, row) in self.rows.iter().enumerate() {
            let p = self.pivots[i];
            if !v[p].is_zero() {
                let factor = v[p];
                for k in p..v.len() {
                    v[k] -= factor * row[k];
                }
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
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    target: &TrapdoorPolyVector,
    num_vars: usize,
    seed: u64,
    check_idx: usize,
    total_checks: usize,
) -> (bool, Option<String>) {
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
    let r = Fr::rand(&mut rng);

    let mut mono_set = std::collections::HashSet::new();
    for (m, _) in &target.components {
        mono_set.insert(m.clone());
    }
    let all_monos = vec![
        TrapdoorMonomial::AlphaBetaDelta,
        TrapdoorMonomial::DeltaSq,
        // Span-separated monomials (Pub vs Wit - critical for security!)
        TrapdoorMonomial::BetaDeltaUPub,
        TrapdoorMonomial::BetaDeltaUWit,
        TrapdoorMonomial::AlphaDeltaVPub,
        TrapdoorMonomial::AlphaDeltaVWit,
        TrapdoorMonomial::DeltaWPub,
        TrapdoorMonomial::DeltaWWit,
        // L-query handles (use witness polynomials)
        TrapdoorMonomial::BetaSqU,
        TrapdoorMonomial::BetaU,
        TrapdoorMonomial::AlphaBetaV,
        TrapdoorMonomial::AlphaV,
        TrapdoorMonomial::BetaW,
        TrapdoorMonomial::W,
        TrapdoorMonomial::BetaUV,
        TrapdoorMonomial::AlphaVV,
        TrapdoorMonomial::WV,
        TrapdoorMonomial::DeltaUV,
        TrapdoorMonomial::DeltaPureUV,
        TrapdoorMonomial::AlphaDeltaSq,
        TrapdoorMonomial::BetaV,
        TrapdoorMonomial::PureVV,
        // Static GT table handles (deg_ρ = 0, cannot reach armed target)
        TrapdoorMonomial::AlphaBetaStatic,
        TrapdoorMonomial::AlphaDeltaStatic,
        TrapdoorMonomial::AlphaVStatic,
    ];
    for m in all_monos {
        mono_set.insert(m);
    }

    let mut monomials: Vec<_> = mono_set.into_iter().collect();
    monomials.sort();
    let mono_map: HashMap<_, _> = monomials
        .iter()
        .enumerate()
        .map(|(i, m)| (m.clone(), i))
        .collect();
    let num_dims = monomials.len();

    let mut target_vec = vec![Fr::zero(); num_dims];
    for (m, p) in &target.components {
        if let Some(&idx) = mono_map.get(&m) {
            target_vec[idx] = p.evaluate(&r);
        }
    }

    let mut basis = Basis::new();
    let mut dependency_report: Option<String> = None;

    let mut add_basis_vec = |label: &str, col_idx: usize, vec_map: Vec<(TrapdoorMonomial, Fr)>| {
        let mut v = vec![Fr::zero(); num_dims];
        for (m, val) in vec_map {
            if let Some(&idx) = mono_map.get(&m) {
                v[idx] += val;
            }
        }
        basis.insert(v);
        if dependency_report.is_none() {
            let residue = basis.reduce(target_vec.clone());
            if residue.iter().all(|x| x.is_zero()) {
                dependency_report = Some(format!("column {} via {}", col_idx, label));
            }
        }
    };

    let mut v_pub_r = Fr::zero();
    for (_, v, _) in pub_polys {
        v_pub_r += v.evaluate(&r);
    }

    let total_cols = num_vars;
    let step = std::cmp::max(1, total_cols / 20);

    // The adversary has handles for Public Inputs (CRS) AND Witness Inputs (Arming).
    // Skipping 0..num_pub would be UNDER-POWERING the adversary (ignoring public handles).
    let num_pub = pub_polys.len();

    for k in 0..num_vars {
        if k % step == 0 {
            let pct = (k * 100) / total_cols;
            print!(
                "\r[Independence Check {}/{}] Progress: {:3}%",
                check_idx, total_checks, pct
            );
            use std::io::Write;
            let _ = std::io::stdout().flush();
        }

        let (u_val, v_val, w_val) = extractor.evaluate_column(k, r);

        // 1. u_k * D_pub * delta -> beta*delta*u + delta*u*V
        // NOTE: In PVUGC, public A-queries are zeroed, so for k < num_pub, u_val = 0.
        // For witness k >= num_pub, this uses U_wit.
        // We use BetaDeltaUWit because only witness columns have non-zero A-queries.
        add_basis_vec(
            "u_k * D_pub * delta",
            k,
            vec![
                (TrapdoorMonomial::BetaDeltaUWit, u_val),
                (TrapdoorMonomial::DeltaUV, u_val * v_pub_r),
            ],
        );

        // 2. u_k * D_delta * delta -> u * delta^2 (under δ-normalization)
        // Actual: e([u_k]_1, [δ]_2^ρ) = ρ·δ·u_k
        // Normalized: δ · (ρ·δ·u_k) = ρ·δ²·u_k → DeltaSq
        add_basis_vec(
            "u_k * D_delta * delta",
            k,
            vec![(TrapdoorMonomial::DeltaSq, u_val)],
        );

        // 3. u_k * D_j * delta -> u * v_j * delta
        add_basis_vec(
            "u_k * D_j * delta",
            k,
            vec![(TrapdoorMonomial::DeltaPureUV, u_val)],
        );

        if k >= num_pub {
            // 4. L_k * D_pub * delta -> (beta*u+alpha*v+w)(beta+V)
            add_basis_vec(
                "L_k * D_pub * delta",
                k,
                vec![
                    (TrapdoorMonomial::BetaSqU, u_val),
                    (TrapdoorMonomial::BetaU, u_val * v_pub_r),
                    (TrapdoorMonomial::AlphaBetaV, v_val),
                    (TrapdoorMonomial::AlphaV, v_val * v_pub_r),
                    (TrapdoorMonomial::BetaW, w_val),
                    (TrapdoorMonomial::W, w_val * v_pub_r),
                ],
            );

            // 5. L_k * D_delta * delta -> (beta*u+alpha*v+w) * delta
            // = beta*delta*u + alpha*delta*v + delta*w
            // Uses WITNESS variants because L-queries only exist for k >= num_pub.
            add_basis_vec(
                "L_k * D_delta * delta (WITNESS)",
                k,
                vec![
                    (TrapdoorMonomial::BetaDeltaUWit, u_val), // WITNESS U
                    (TrapdoorMonomial::AlphaDeltaVWit, v_val), // WITNESS V
                    (TrapdoorMonomial::DeltaWWit, w_val),      // WITNESS W
                ],
            );

            // 6. L_k * D_j * delta -> (beta*u+alpha*v+w) * v_j
            // Model as (beta*u + alpha*v + w) * Any
            // = BetaUV * u + AlphaVV * v + WV * w
            add_basis_vec(
                "L_k * D_j * delta",
                k,
                vec![
                    (TrapdoorMonomial::BetaUV, u_val),
                    (TrapdoorMonomial::AlphaVV, v_val),
                    (TrapdoorMonomial::WV, w_val),
                ],
            );
        }

        // 7. Raw B-Query Handles (b_g1_query)
        // Available for ALL variables (including public).
        // Actual: e([v_k]_1, [δ]_2^ρ) = ρ·δ·v_k
        // Normalized: δ · (ρ·δ·v_k) = ρ·δ²·v_k → DeltaSq
        add_basis_vec("Raw B DeltaSq", k, vec![(TrapdoorMonomial::DeltaSq, v_val)]);
        // v_k (G1) * beta (G2) -> v * beta
        add_basis_vec("Raw B BetaV", k, vec![(TrapdoorMonomial::BetaV, v_val)]);
        add_basis_vec("Raw B PureVV", k, vec![(TrapdoorMonomial::PureVV, v_val)]);
    }
    println!(
        "\r[Independence Check {}/{}] Progress: 100%",
        check_idx, total_checks
    );

    // 8. Static GT table handles (deg_rho = 0).
    // T_beta = e(alpha, beta)  → AlphaBetaStatic
    add_basis_vec(
        "GT T_beta (alpha*beta, no delta)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaBetaStatic, Fr::one())],
    );

    // T_delta = e(alpha, delta) → AlphaDeltaStatic
    add_basis_vec(
        "GT T_delta (alpha*delta, no delta^2)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaDeltaStatic, Fr::one())],
    );

    // T_v[i] = e(alpha, B_i) for *all* B-columns.
    // The adversary gets the span of {alpha * v_i}; we model that as one generic AlphaVStatic direction.
    // You can refine this later if you want multiple independent directions.
    add_basis_vec(
        "GT T_v aggregate (alpha*v, no delta)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaVStatic, Fr::one())],
    );

    // 9. Alpha * D_pub (bundled) - from e([α]_1, y_cols_rho[0])
    // This is the BUNDLED handle: adversary gets AlphaBetaDelta + AlphaDeltaVPub together.
    // They CANNOT separate these components - they come as a package.
    //
    // KEY INSIGHT: With span separation (V_pub ⊥ V_wit):
    // - The adversary gets AlphaDeltaVPub bundled with AlphaBetaDelta
    // - The target ALSO includes AlphaDeltaVPub (from standard IC)
    // - So the bundled handle contributes directly to target!
    // - Security depends on the REMAINING target (BetaDeltaUPub, DeltaWPub, DeltaSq)
    //   which CANNOT be synthesized from witness handles if span separation holds!
    add_basis_vec(
        "Alpha * y_cols_rho[0] (D_pub bundled)",
        usize::MAX,
        vec![
            (TrapdoorMonomial::AlphaBetaDelta, Fr::one()),
            (TrapdoorMonomial::AlphaDeltaVPub, v_pub_r),
        ],
    );

    // 10. Alpha * Y_wit[j] - from e([α]_1, y_cols_rho[j]) for witness columns
    // This gives ρ·α·v_j for each witness column, contributing to AlphaDeltaVWit.
    // 
    // CRITICAL: If span separation holds (V_pub ⊥ V_wit), this handle CANNOT
    // be used to cancel the AlphaDeltaVPub pollution from handle #9.
    // We model this by using a SEPARATE monomial (AlphaDeltaVWit).
    //
    // The adversary has the full span of {α·v_j} for all witness j, but this
    // cannot synthesize α·V_pub if the V polynomials are span-separated.
    add_basis_vec(
        "Alpha * y_cols_rho[wit] (V_wit span)",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaDeltaVWit, Fr::one())],
    );

    // 11. Alpha * delta_rho - from e([α]_1, delta_rho) = ρ·α·δ
    // Under δ-normalization this becomes ρ·α·δ² → AlphaDeltaSq
    add_basis_vec(
        "Alpha * delta_rho",
        usize::MAX,
        vec![(TrapdoorMonomial::AlphaDeltaSq, Fr::one())],
    );

    let residue = basis.reduce(target_vec);
    let is_safe = residue.iter().all(|x| x.is_zero()) == false;
    (is_safe, dependency_report)
}

fn run_independence_checks(
    label: &str,
    extractor: &MatrixExtractor,
    pub_polys: &[(
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
        DensePolynomial<Fr>,
    )],
    target: &TrapdoorPolyVector,
    num_vars: usize,
    num_checks: usize,
) -> bool {
    let mut all_safe = true;
    println!(
        "[Independence Check{}] Running {} iterations for robustness...",
        label, num_checks
    );
    for i in 0..num_checks {
        let seed = 12345 + i as u64;
        let (is_safe, dependency) = check_independence_streaming(
            extractor,
            pub_polys,
            target,
            num_vars,
            seed,
            i + 1,
            num_checks,
        );
        if !is_safe {
            all_safe = false;
            println!(
                "[FAIL] Independence Check{} iteration {} found dependency!",
                label,
                i + 1
            );
            if let Some(info) = dependency {
                println!("        Dependency witness: {}", info);
            }
            break;
        }
    }
    if all_safe {
        println!(
            "[PASS] Independence Check{} (All {} iterations passed).",
            label, num_checks
        );
    } else {
        println!("[FAIL] Independence Check{} (Target in Span).", label);
    }
    all_safe
}
