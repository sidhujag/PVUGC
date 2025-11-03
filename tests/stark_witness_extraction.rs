//! Test Winterfell STARK witness extraction
//!
//! This test generates a real Winterfell VDF proof and extracts witness data
//! for feeding into the hybrid inner circuit.

use winterfell::{math::{FieldElement, fields::f64::BaseElement}, Trace};

mod helpers;
use helpers::simple_vdf::*;

#[test]
fn test_generate_vdf_proof() {
    // Generate minimal VDF proof
    let start = BaseElement::new(3);  // BaseElement::from() only supports u8/u16/u32
    let steps = 16; // 2^4 domain (minimal for fast testing)
    
    let (proof, trace) = generate_test_vdf_proof(start, steps);
    
    // Print proof structure for inspection
    println!("VDF Proof generated successfully!");
    println!("  Trace length: {}", trace.length());
    println!("  Trace width: {}", trace.width());
    println!("  Proof bytes: {} bytes", proof.to_bytes().len());
    
    // Extract query leaves from trace
    let query_positions = vec![5, 13]; // Example positions
    let query_leaves = extract_query_leaves(&trace, &query_positions);
    
    println!("  Extracted {} query leaves", query_leaves.len());
    for (i, leaf) in query_leaves.iter().enumerate() {
        println!("    Query {}: GL limbs = {:?}", i, leaf);
    }
    
    // Validate leaf extraction against trace
    for (i, &pos) in query_positions.iter().enumerate() {
        let expected_col0 = trace.get(0, pos).as_int();
        let expected_col1 = trace.get(1, pos).as_int();
        assert_eq!(query_leaves[i][0], expected_col0);
        assert_eq!(query_leaves[i][1], expected_col1);
    }
    
    println!("✅ VDF proof generation works!");
    println!("✅ Query leaf extraction validated!");
    println!("⏳ Next: Extract FRI/DEEP witnesses (requires verifier replay or prover hooks)");
}

#[test]
#[ignore] // TODO: Requires accessing private Winterfell proof fields
fn test_fri_structure_inspection() {
    // This test will be implemented once we have:
    // 1. Verifier replay hooks, or
    // 2. Prover instrumentation to emit witness sidecar
    // 3. Public accessors for proof internals
    
    println!("⏳ FRI structure inspection pending witness extraction implementation");
}

#[test]
#[ignore] // TODO: Requires accessing Winterfell commitment internals
fn test_multiple_proofs_same_statement() {
    // This will validate proof-agnostic property once we have witness extraction
    println!("⏳ Proof-agnostic test pending witness extraction implementation");
}

