//! Unit tests for fast GL operations
//! Test each operation in isolation with known values

use crate::stark::gadgets::gl_fast::{self, GlVar};
use crate::stark::gadgets::gl_range::gl_alloc_u64;
use ark_relations::r1cs::ConstraintSystem;
use crate::outer_compressed::InnerFr;
use ark_r1cs_std::R1CSVar;

#[test]
fn test_gl_add_simple() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: 5 + 7 = 12 in GL
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(5)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(7)).unwrap();
    let b = GlVar(b_fp);
    
    let result = gl_fast::gl_add(cs.clone(), &a, &b).unwrap();
    
    // Check value is correct
    use crate::stark::gl_u64::fr_to_gl_u64;
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, 12, "5 + 7 should equal 12");
    
    // Check constraints are satisfied
    assert!(cs.is_satisfied().unwrap(), "gl_add constraints should be satisfied");
    eprintln!("gl_add(5, 7) = 12, constraints: {}", cs.num_constraints());
}

#[test]
fn test_gl_add_overflow() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: (p-1) + 5 should wrap to 4 in GL
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(P_U64 - 1)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(5)).unwrap();
    let b = GlVar(b_fp);
    
    let result = gl_fast::gl_add(cs.clone(), &a, &b).unwrap();
    
    use crate::stark::gl_u64::fr_to_gl_u64;
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, 4, "(p-1) + 5 should wrap to 4");
    
    assert!(cs.is_satisfied().unwrap(), "gl_add with overflow should satisfy");
    eprintln!("gl_add overflow test passed, constraints: {}", cs.num_constraints());
}

#[test]
fn test_gl_sub_simple() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: 10 - 3 = 7
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(10)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(3)).unwrap();
    let b = GlVar(b_fp);
    
    let result = gl_fast::gl_sub(cs.clone(), &a, &b).unwrap();
    
    use crate::stark::gl_u64::fr_to_gl_u64;
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, 7, "10 - 3 should equal 7");
    
    assert!(cs.is_satisfied().unwrap(), "gl_sub constraints should be satisfied");
    eprintln!("gl_sub(10, 3) = 7, constraints: {}", cs.num_constraints());
}

#[test]
fn test_gl_sub_underflow() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: 3 - 10 should wrap to p-7 in GL
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(3)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(10)).unwrap();
    let b = GlVar(b_fp);
    
    let result = gl_fast::gl_sub(cs.clone(), &a, &b).unwrap();
    
    use crate::stark::gl_u64::fr_to_gl_u64;
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, P_U64 - 7, "3 - 10 should wrap to p-7");
    
    assert!(cs.is_satisfied().unwrap(), "gl_sub with underflow should satisfy");
    eprintln!("gl_sub underflow test passed, constraints: {}", cs.num_constraints());
}

#[test]
fn test_gl_mul_simple() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: 5 * 7 = 35
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(5)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(7)).unwrap();
    let b = GlVar(b_fp);
    
    eprintln!("Testing gl_mul(5, 7)...");
    let result = gl_fast::gl_mul(cs.clone(), &a, &b).unwrap();
    
    use crate::stark::gl_u64::fr_to_gl_u64;
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, 35, "5 * 7 should equal 35");
    
    eprintln!("Value check passed");
    let satisfied = cs.is_satisfied().unwrap();
    eprintln!("CS satisfied: {}", satisfied);
    eprintln!("Constraints: {}", cs.num_constraints());
    
    assert!(satisfied, "gl_mul constraints should be satisfied");
    eprintln!("gl_mul(5, 7) = 35");
}

#[test]
fn test_gl_mul_large() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: Large multiplication that needs reduction
    let a_val = 1u64 << 40;  // 2^40
    let b_val = 1u64 << 20;  // 2^20
    // Product = 2^60, well within GL
    
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(a_val)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(b_val)).unwrap();
    let b = GlVar(b_fp);
    
    eprintln!("Testing gl_mul(2^40, 2^20)...");
    let result = gl_fast::gl_mul(cs.clone(), &a, &b).unwrap();
    
    use crate::stark::gl_u64::{fr_to_gl_u64, gl_mul};
    let expected = gl_mul(a_val, b_val);
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, expected, "Large multiplication should match");
    
    let satisfied = cs.is_satisfied().unwrap();
    eprintln!("CS satisfied: {}", satisfied);
    
    assert!(satisfied, "gl_mul large should satisfy");
    eprintln!("gl_mul large test passed, constraints: {}", cs.num_constraints());
}

#[test]
fn test_gl_inv_simple() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test: inv(7) * 7 = 1
    let (_u, v_fp) = gl_alloc_u64(cs.clone(), Some(7)).unwrap();
    let v = GlVar(v_fp);
    
    eprintln!("Testing gl_inv(7)...");
    
    // Test the actual gl_inv function
    let inv = gl_fast::gl_inv(cs.clone(), &v).unwrap();
    
    use crate::stark::gl_u64::{fr_to_gl_u64, gl_inv as host_gl_inv};
    let expected_inv = host_gl_inv(7);
    let inv_val = fr_to_gl_u64(inv.0.value().unwrap());
    
    eprintln!("  inv(7) = {}, expected = {}", inv_val, expected_inv);
    assert_eq!(inv_val, expected_inv, "Inverse value should match");
    
    let satisfied = cs.is_satisfied().unwrap();
    eprintln!("  CS satisfied: {}", satisfied);
    eprintln!("  Constraints: {}", cs.num_constraints());
    
    if !satisfied {
        let which = cs.which_is_unsatisfied();
        eprintln!("  Unsatisfied: {:?}", which);
    }
    
    assert!(satisfied, "gl_inv constraints should be satisfied");
    eprintln!("gl_inv(7) test passed");
}

#[test]
fn test_gl_operations_sequence() {
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test a sequence: (5 + 3) * 2 - 1 = 15
    let (_u, a_fp) = gl_alloc_u64(cs.clone(), Some(5)).unwrap();
    let a = GlVar(a_fp);
    
    let (_u, b_fp) = gl_alloc_u64(cs.clone(), Some(3)).unwrap();
    let b = GlVar(b_fp);
    
    eprintln!("Testing: (5 + 3) * 2 - 1...");
    let sum = gl_fast::gl_add(cs.clone(), &a, &b).unwrap();
    eprintln!("  After add, satisfied: {}", cs.is_satisfied().unwrap());
    
    let (_u, two_fp) = gl_alloc_u64(cs.clone(), Some(2)).unwrap();
    let two = GlVar(two_fp);
    
    let prod = gl_fast::gl_mul(cs.clone(), &sum, &two).unwrap();
    eprintln!("  After mul, satisfied: {}", cs.is_satisfied().unwrap());
    
    let (_u, one_fp) = gl_alloc_u64(cs.clone(), Some(1)).unwrap();
    let one = GlVar(one_fp);
    
    let result = gl_fast::gl_sub(cs.clone(), &prod, &one).unwrap();
    eprintln!("  After sub, satisfied: {}", cs.is_satisfied().unwrap());
    
    use crate::stark::gl_u64::fr_to_gl_u64;
    let result_val = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(result_val, 15, "(5+3)*2-1 should equal 15");
    
    assert!(cs.is_satisfied().unwrap(), "Sequence should satisfy");
    eprintln!("Operation sequence test passed, total constraints: {}", cs.num_constraints());
}

// ============================================================================
// Tests for LIGHT GL operations (congruence-only, no byte packing)
// ============================================================================

#[test]
fn test_gl_add_light() {
    use crate::stark::gadgets::gl_fast::{gl_add_light, GlVar};
    use crate::stark::gl_u64::{gl_add, fr_to_gl_u64};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::alloc::AllocVar;
    
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test various addition cases
    let test_cases = vec![
        (0u64, 0u64),
        (1u64, 1u64),
        (P_U64 - 1, 0),  // Max value + 0
        (P_U64 - 1, 1),  // Should wrap
        (P_U64 / 2, P_U64 / 2),  // Two halves
        (12345678901234567u64, 98765432109876543u64),
    ];
    
    for &(a_val, b_val) in &test_cases {
        let a = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(a_val))).unwrap());
        let b = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(b_val))).unwrap());
        
        let result = gl_add_light(cs.clone(), &a, &b).unwrap();
        
        // Check against native GL addition
        let expected = gl_add(a_val, b_val);
        let actual = fr_to_gl_u64(result.0.value().unwrap());
        
        assert_eq!(actual, expected, 
            "gl_add_light({}, {}) = {} but expected {}", a_val, b_val, actual, expected);
    }
    
    assert!(cs.is_satisfied().unwrap(), "CS should be satisfied");
    eprintln!("gl_add_light constraints per op: ~{}", 
        cs.num_constraints() / test_cases.len());
}

#[test]
fn test_gl_sub_light() {
    use crate::stark::gadgets::gl_fast::{gl_sub_light, GlVar};
    use crate::stark::gl_u64::{gl_sub, fr_to_gl_u64};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::alloc::AllocVar;
    
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    let test_cases = vec![
        (0u64, 0u64),
        (1u64, 0u64),
        (0u64, 1u64),  // Should wrap
        (P_U64 - 1, P_U64 - 1),
        (P_U64 - 1, 1),
        (12345678901234567u64, 98765432109876543u64),
    ];
    
    for &(a_val, b_val) in &test_cases {
        let a = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(a_val))).unwrap());
        let b = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(b_val))).unwrap());
        
        let result = gl_sub_light(cs.clone(), &a, &b).unwrap();
        
        let expected = gl_sub(a_val, b_val);
        let actual = fr_to_gl_u64(result.0.value().unwrap());
        
        assert_eq!(actual, expected,
            "gl_sub_light({}, {}) = {} but expected {}", a_val, b_val, actual, expected);
    }
    
    assert!(cs.is_satisfied().unwrap(), "CS should be satisfied");
    eprintln!("gl_sub_light constraints per op: ~{}", 
        cs.num_constraints() / test_cases.len());
}

#[test]
fn test_gl_mul_light() {
    use crate::stark::gadgets::gl_fast::{gl_mul_light, GlVar};
    use crate::stark::gl_u64::{gl_mul, fr_to_gl_u64};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::alloc::AllocVar;
    
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    let test_cases = vec![
        (0u64, 0u64),
        (1u64, 1u64),
        (0u64, P_U64 - 1),
        (2u64, P_U64 / 2 + 1),  // Should wrap
        (P_U64 - 1, P_U64 - 1),  // (p-1)^2 mod p
        (12345678901234567u64, 98765432109876543u64),
        (1234567890u64, 9876543210u64),
    ];
    
    for &(a_val, b_val) in &test_cases {
        let a = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(a_val))).unwrap());
        let b = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(b_val))).unwrap());
        
        let result = gl_mul_light(cs.clone(), &a, &b).unwrap();
        
        let expected = gl_mul(a_val, b_val);
        let actual = fr_to_gl_u64(result.0.value().unwrap());
        
        assert_eq!(actual, expected,
            "gl_mul_light({}, {}) = {} but expected {}", a_val, b_val, actual, expected);
    }
    
    assert!(cs.is_satisfied().unwrap(), "CS should be satisfied");
    eprintln!("gl_mul_light constraints per op: ~{}", 
        cs.num_constraints() / test_cases.len());
}

#[test]
fn test_gl_inv_light() {
    use crate::stark::gadgets::gl_fast::{gl_inv_light, gl_mul_light, GlVar};
    use crate::stark::gl_u64::{gl_inv, fr_to_gl_u64};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::alloc::AllocVar;
    
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    let test_cases = vec![
        1u64,
        2u64,
        3u64,
        P_U64 - 1,
        P_U64 / 2,
        12345678901234567u64,
        98765432109876543u64,
    ];
    
    for &v_val in &test_cases {
        let v = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(v_val))).unwrap());
        
        let inv = gl_inv_light(cs.clone(), &v).unwrap();
        
        // Check inverse property: v * inv = 1
        let prod = gl_mul_light(cs.clone(), &v, &inv).unwrap();
        let prod_val = fr_to_gl_u64(prod.0.value().unwrap());
        assert_eq!(prod_val, 1, "v * inv should equal 1 for v = {}", v_val);
        
        // Check against native GL inverse
        let expected = gl_inv(v_val);
        let actual = fr_to_gl_u64(inv.0.value().unwrap());
        assert_eq!(actual, expected,
            "gl_inv_light({}) = {} but expected {}", v_val, actual, expected);
    }
    
    assert!(cs.is_satisfied().unwrap(), "CS should be satisfied");
    eprintln!("gl_inv_light constraints per op: ~{}", 
        cs.num_constraints() / test_cases.len());
}

#[test]
fn test_light_ops_composition() {
    // Test that composing multiple light operations works correctly
    use crate::stark::gadgets::gl_fast::{gl_add_light, gl_sub_light, gl_mul_light, gl_inv_light, GlVar};
    use crate::stark::gl_u64::{gl_add, gl_sub, gl_mul, gl_inv, fr_to_gl_u64};
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::alloc::AllocVar;
    
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Complex expression: ((a + b) * c - d) * inv(a)
    let a_val = 12345678u64;
    let b_val = 87654321u64;
    let c_val = 11111111u64;
    let d_val = 99999999u64;
    
    let a = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(a_val))).unwrap());
    let b = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(b_val))).unwrap());
    let c = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(c_val))).unwrap());
    let d = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(d_val))).unwrap());
    
    // Circuit computation
    let sum = gl_add_light(cs.clone(), &a, &b).unwrap();
    let prod = gl_mul_light(cs.clone(), &sum, &c).unwrap();
    let diff = gl_sub_light(cs.clone(), &prod, &d).unwrap();
    let inv_a = gl_inv_light(cs.clone(), &a).unwrap();
    let result = gl_mul_light(cs.clone(), &diff, &inv_a).unwrap();
    
    // Native computation
    let sum_native = gl_add(a_val, b_val);
    let prod_native = gl_mul(sum_native, c_val);
    let diff_native = gl_sub(prod_native, d_val);
    let inv_a_native = gl_inv(a_val);
    let expected = gl_mul(diff_native, inv_a_native);
    
    let actual = fr_to_gl_u64(result.0.value().unwrap());
    assert_eq!(actual, expected, "Complex composition failed");
    
    assert!(cs.is_satisfied().unwrap(), "CS should be satisfied");
    eprintln!("Total constraints for complex expression: {}", cs.num_constraints());
}

#[test]
fn test_light_ops_edge_cases() {
    // Test edge cases and boundary conditions
    use crate::stark::gadgets::gl_fast::{gl_add_light, gl_sub_light, gl_mul_light, GlVar};
    use crate::stark::gl_u64::fr_to_gl_u64;
    use ark_r1cs_std::fields::fp::FpVar;
    use ark_r1cs_std::alloc::AllocVar;
    
    const P_U64: u64 = 0xFFFF_FFFF_0000_0001;
    
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    // Test wrapping behavior
    let max_val = P_U64 - 1;
    let max_gl = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(max_val))).unwrap());
    let one = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(1u64))).unwrap());
    
    // max + 1 should wrap to 0
    let wrapped = gl_add_light(cs.clone(), &max_gl, &one).unwrap();
    let wrapped_val = fr_to_gl_u64(wrapped.0.value().unwrap());
    assert_eq!(wrapped_val, 0, "P-1 + 1 should wrap to 0");
    
    // 0 - 1 should wrap to P-1
    let zero = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(0u64))).unwrap());
    let underflow = gl_sub_light(cs.clone(), &zero, &one).unwrap();
    let underflow_val = fr_to_gl_u64(underflow.0.value().unwrap());
    assert_eq!(underflow_val, P_U64 - 1, "0 - 1 should wrap to P-1");
    
    // Large multiplication that wraps
    let large = GlVar(FpVar::new_witness(cs.clone(), || Ok(InnerFr::from(P_U64 / 2))).unwrap());
    let prod = gl_mul_light(cs.clone(), &large, &large).unwrap();
    let prod_val = fr_to_gl_u64(prod.0.value().unwrap());
    // (P/2)^2 mod P should be computed correctly
    let expected = crate::stark::gl_u64::gl_mul(P_U64 / 2, P_U64 / 2);
    assert_eq!(prod_val, expected, "Large multiplication should wrap correctly");
    
    assert!(cs.is_satisfied().unwrap(), "CS should be satisfied");
}
