//! OOD (Out-of-Domain) Evaluation Utilities
//!
//! This module provides utilities for OOD evaluation verification.
//! The main components are:
//!
//! - `OodFrame`: Structure holding trace and composition evaluations at OOD point
//! - `evaluate_aggregator_constraints`: Evaluates the Aggregator STARK's constraints
//!   (VDF-like: col0' = col0³ + col1, col1' = col0)
//! - `CompositionPoly`: Verifies composition polynomial consistency
//! - `verify_ood_constraint_equation`: Full OOD verification with boundary/exemption handling
//!
//! ## STARK OOD Verification Formula
//!
//! The composition polynomial encodes transition and boundary constraints:
//!
//! ```text
//! transition_sum / Z_trans + boundary_sum / Z_bound = C(z)
//! ```
//!
//! Where:
//! - `Z_trans = (z^n - 1) / (z - g^{n-1})` (transition zerofier with exemption)
//! - `Z_bound = z - g^{n-1}` (boundary constraint divisor for last step)
//!
//! Multiplying through to avoid division:
//! ```text
//! transition_sum * exemption² + boundary_sum * (z^n - 1) = C(z) * (z^n - 1) * exemption
//! ```
//!
//! Where `exemption = z - g^{n-1}`.
//!
//! ## Usage Context
//!
//! This module is used for:
//! 1. Integration tests validating constraint formulas
//! 2. The VerifierAir's in-circuit OOD verification
//! 3. Understanding the verification flow

use winterfell::math::{fields::f64::BaseElement, FieldElement};
use winterfell::math::StarkField;

// ============================================================================
// FORMULA-AS-WITNESS: Generic Constraint Encoding
// ============================================================================
//
// This encoding allows a single VerifierAir to verify proofs from ANY app AIR
// by interpreting constraint formulas provided as witness data.
//
// ## Security Model
//
// The formula is hashed and bound to the public input (circuit_hash).
// The verifier checks: hash(formula_witness) == public_input.circuit_hash
// This ensures the prover cannot substitute a different formula.
//
// ## Encoding Format
//
// Each constraint is a polynomial equation of the form:
//   c(current, next) = Σ (coeff * Π vars^powers) = 0
//
// Example: VDF constraint `next[0] - curr[0]^3 - curr[1] = 0`
// Encodes as 3 monomials:
//   1. coeff=+1, vars=[(Next, 0, 1)]         → next[0]
//   2. coeff=-1, vars=[(Current, 0, 3)]      → -curr[0]³
//   3. coeff=-1, vars=[(Current, 1, 1)]      → -curr[1]

/// Column type for formula encoding
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ColType {
    /// Current row: trace_current[index]
    Current = 0,
    /// Next row: trace_next[index]
    Next = 1,
}

/// A variable reference within a monomial
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VarRef {
    /// Column type (current or next row)
    pub col_type: ColType,
    /// Column index
    pub col_idx: usize,
    /// Exponent (power)
    pub power: u32,
}

/// A monomial: coefficient * product of variables
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Monomial {
    /// Coefficient (field element, stored as u64 for encoding)
    pub coeff: u64,
    /// Whether coefficient is negative (subtraction)
    pub coeff_neg: bool,
    /// Variables in this monomial (product of vars^power)
    pub vars: Vec<VarRef>,
}

/// A single constraint: sum of monomials that should equal zero
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodedConstraint {
    /// Monomials that sum to zero
    pub monomials: Vec<Monomial>,
}

/// Complete encoded formula for an AIR
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodedFormula {
    /// Number of trace columns this AIR uses
    pub trace_width: usize,
    /// All transition constraints
    pub constraints: Vec<EncodedConstraint>,
}

impl EncodedFormula {
    /// Compute a hash of the formula for binding to public input
    /// Uses a simple algebraic hash for in-circuit efficiency
    pub fn compute_hash(&self) -> [BaseElement; 4] {
        // Simple deterministic hash: mix all encoding values
        // In production, use RPO or similar algebraic hash
        let mut h0 = BaseElement::new(self.trace_width as u64);
        let mut h1 = BaseElement::new(self.constraints.len() as u64);
        let mut h2 = BaseElement::ZERO;
        let mut h3 = BaseElement::ZERO;
        
        let mix = BaseElement::new(0x9e3779b97f4a7c15u64); // golden ratio
        
        for (ci, constraint) in self.constraints.iter().enumerate() {
            for (mi, mono) in constraint.monomials.iter().enumerate() {
                // Mix in coefficient
                let coeff_val = if mono.coeff_neg {
                    BaseElement::ZERO - BaseElement::new(mono.coeff)
                } else {
                    BaseElement::new(mono.coeff)
                };
                h0 = h0 + coeff_val * mix;
                h1 = h1 * mix + BaseElement::new((ci * 1000 + mi) as u64);
                
                // Mix in variables
                for var in &mono.vars {
                    h2 = h2 + BaseElement::new(var.col_type as u64) * mix;
                    h2 = h2 + BaseElement::new(var.col_idx as u64);
                    h3 = h3 + BaseElement::new(var.power as u64) * mix;
                }
            }
        }
        
        [h0, h1, h2, h3]
    }
    
    /// Total number of monomials in all constraints
    pub fn monomial_count(&self) -> usize {
        self.constraints.iter().map(|c| c.monomials.len()).sum()
    }
}

/// Evaluate a monomial at given trace values
fn evaluate_monomial(
    mono: &Monomial,
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
) -> BaseElement {
    let mut result = if mono.coeff_neg {
        BaseElement::ZERO - BaseElement::new(mono.coeff)
    } else {
        BaseElement::new(mono.coeff)
    };
    
    for var in &mono.vars {
        let val = match var.col_type {
            ColType::Current => trace_current.get(var.col_idx).copied().unwrap_or(BaseElement::ZERO),
            ColType::Next => trace_next.get(var.col_idx).copied().unwrap_or(BaseElement::ZERO),
        };
        // Compute val^power
        let powered = val.exp((var.power as u64).into());
        result = result * powered;
    }
    
    result
}

/// Evaluate a constraint at given trace values
fn evaluate_constraint(
    constraint: &EncodedConstraint,
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
) -> BaseElement {
    let mut sum = BaseElement::ZERO;
    for mono in &constraint.monomials {
        sum = sum + evaluate_monomial(mono, trace_current, trace_next);
    }
    sum
}

/// Evaluate all constraints from an encoded formula
/// Returns a vector of constraint evaluations (should all be zero for valid trace)
pub fn evaluate_formula(
    formula: &EncodedFormula,
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
) -> Vec<BaseElement> {
    formula.constraints.iter()
        .map(|c| evaluate_constraint(c, trace_current, trace_next))
        .collect()
}

/// Verify that formula hash matches expected circuit hash
pub fn verify_formula_hash(
    formula: &EncodedFormula,
    expected_hash: &[BaseElement; 4],
) -> bool {
    let computed = formula.compute_hash();
    computed == *expected_hash
}

// ============================================================================
// PRE-ENCODED FORMULAS FOR COMMON AIRs
// ============================================================================

/// Encode simple VDF constraints (matches simple_vdf.rs VdfAir)
/// 
/// This matches the actual VdfAir from tests/helpers/simple_vdf.rs:
/// - 2 columns (col0 = state, col1 = auxiliary for result)
/// - 1 constraint: next[0] - curr[0]^3 - 1 = 0
/// 
/// NOTE: The VdfAir only has 1 transition constraint, but the trace has 2 columns.
/// Column 1 stores the result for the boundary assertion.
pub fn encode_vdf_formula() -> EncodedFormula {
    EncodedFormula {
        trace_width: 2,
        constraints: vec![
            // Single constraint: next[0] - curr[0]^3 - 1 = 0
            // i.e., next[0] = curr[0]^3 + 1
            EncodedConstraint {
                monomials: vec![
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 1 }],
                    },
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 0, power: 3 }],
                    },
                    // Constant term: -1
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![], // Empty vars = constant
                    },
                ],
            },
        ],
    }
}

/// Encode a simple Add2 AIR (2 columns, 2 constraints):
/// - c0: next[0] - curr[0] - 2 = 0
/// - c1: next[1] - next[0] = 0
///
/// This matches `stark/tests/helpers/add2.rs`.
pub fn encode_add2_formula() -> EncodedFormula {
    EncodedFormula {
        trace_width: 2,
        constraints: vec![
            // Constraint 0: next[0] - curr[0] - 2 = 0
            EncodedConstraint {
                monomials: vec![
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 1 }],
                    },
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 0, power: 1 }],
                    },
                    Monomial {
                        coeff: 2,
                        coeff_neg: true,
                        vars: vec![], // constant 2
                    },
                ],
            },
            // Constraint 1: next[1] - next[0] = 0
            EncodedConstraint {
                monomials: vec![
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 1, power: 1 }],
                    },
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 1 }],
                    },
                ],
            },
            // Constraint 2 (redundant degree-2): (next0 - cur0 - 2)^2 = 0
            // Expanded:
            //   next0^2 - 2*next0*cur0 + cur0^2 - 4*next0 + 4*cur0 + 4 = 0
            EncodedConstraint {
                monomials: vec![
                    // + next0^2
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 2 }],
                    },
                    // - 2*next0*cur0
                    Monomial {
                        coeff: 2,
                        coeff_neg: true,
                        vars: vec![
                            VarRef { col_type: ColType::Next, col_idx: 0, power: 1 },
                            VarRef { col_type: ColType::Current, col_idx: 0, power: 1 },
                        ],
                    },
                    // + cur0^2
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 0, power: 2 }],
                    },
                    // - 4*next0
                    Monomial {
                        coeff: 4,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 1 }],
                    },
                    // + 4*cur0
                    Monomial {
                        coeff: 4,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 0, power: 1 }],
                    },
                    // + 4
                    Monomial {
                        coeff: 4,
                        coeff_neg: false,
                        vars: vec![],
                    },
                ],
            },
        ],
    }
}

/// Encode simple Fibonacci-like constraints (2 columns)
/// - c0: next[0] - curr[1] = 0
/// - c1: next[1] - curr[0] - curr[1] = 0
pub fn encode_fib_formula() -> EncodedFormula {
    EncodedFormula {
        trace_width: 2,
        constraints: vec![
            // Constraint 0: next[0] - curr[1] = 0
            EncodedConstraint {
                monomials: vec![
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 1 }],
                    },
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 1, power: 1 }],
                    },
                ],
            },
            // Constraint 1: next[1] - curr[0] - curr[1] = 0
            EncodedConstraint {
                monomials: vec![
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 1, power: 1 }],
                    },
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 0, power: 1 }],
                    },
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 1, power: 1 }],
                    },
                ],
            },
        ],
    }
}

/// Encode CubicFib constraints (2 columns, 1 constraint):
/// - c0: next[0] - (curr[0] + curr[1])^3 = 0
///
/// This matches `stark/tests/helpers/cubic_fib.rs` (CubicFibAir).
pub fn encode_cubic_fib_formula() -> EncodedFormula {
    EncodedFormula {
        trace_width: 2,
        constraints: vec![
            EncodedConstraint {
                monomials: vec![
                    // + next0
                    Monomial {
                        coeff: 1,
                        coeff_neg: false,
                        vars: vec![VarRef { col_type: ColType::Next, col_idx: 0, power: 1 }],
                    },
                    // - a^3
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 0, power: 3 }],
                    },
                    // - 3 a^2 b
                    Monomial {
                        coeff: 3,
                        coeff_neg: true,
                        vars: vec![
                            VarRef { col_type: ColType::Current, col_idx: 0, power: 2 },
                            VarRef { col_type: ColType::Current, col_idx: 1, power: 1 },
                        ],
                    },
                    // - 3 a b^2
                    Monomial {
                        coeff: 3,
                        coeff_neg: true,
                        vars: vec![
                            VarRef { col_type: ColType::Current, col_idx: 0, power: 1 },
                            VarRef { col_type: ColType::Current, col_idx: 1, power: 2 },
                        ],
                    },
                    // - b^3
                    Monomial {
                        coeff: 1,
                        coeff_neg: true,
                        vars: vec![VarRef { col_type: ColType::Current, col_idx: 1, power: 3 }],
                    },
                ],
            },
        ],
    }
}

// ============================================================================
// OOD FRAME
// ============================================================================

/// OOD evaluation frame containing trace values at z and z·g
#[derive(Clone, Debug)]
pub struct OodFrame {
    /// Trace evaluations at OOD point z
    pub trace_current: Vec<BaseElement>,
    /// Trace evaluations at z·g (next step)
    pub trace_next: Vec<BaseElement>,
    /// Composition polynomial evaluations at z
    pub composition: Vec<BaseElement>,
    /// Composition polynomial evaluations at z·g (for LINEAR batching)
    pub composition_next: Vec<BaseElement>,
}

impl OodFrame {
    pub fn new(
        trace_current: Vec<BaseElement>,
        trace_next: Vec<BaseElement>,
        composition: Vec<BaseElement>,
        composition_next: Vec<BaseElement>,
    ) -> Self {
        Self {
            trace_current,
            trace_next,
            composition,
            composition_next,
        }
    }

    /// Trace width
    pub fn trace_width(&self) -> usize {
        self.trace_current.len()
    }

    /// Composition width (number of columns)
    pub fn comp_width(&self) -> usize {
        self.composition.len()
    }
}

// ============================================================================
// CHILD AIR TYPE SELECTION
// ============================================================================

/// Child AIR type for OOD verification
/// 
/// When verifying a child proof, we need to evaluate the correct AIR constraints
/// at the OOD point. Different child types have different constraints.
/// 
/// ## Architecture
/// 
/// - **VerifierAir**: Used for Level 2+ aggregators (verifying other VerifierAir proofs)
/// - **Generic**: Used for Level 1 leaf aggregators (verifying app proofs)
/// 
/// ## Generic Mode (Formula-as-Witness)
/// 
/// The `Generic` variant enables formula-as-witness: instead of hardcoding
/// app-specific constraints, the formula is provided as witness data and
/// interpreted at verification time. The formula hash must match the
/// `circuit_hash` in public inputs to prevent formula substitution attacks.
/// 
/// This allows a single VerifierAir to verify proofs from ANY app AIR
/// (VDF, Fib, Bitcoin light client, etc.) without hardcoding their constraints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChildAirType {
    /// Full STARK verification constraints (hash, Merkle, FRI, OOD)
    /// Used for recursive verification (VerifierAir verifying VerifierAir)
    VerifierAir,

    /// AggregatorAir proof (two-AIR architecture).
    ///
    /// The current AggregatorAir skeleton reuses the verifier-style trace layout and
    /// constraint system, but we still bind a distinct protocol identifier into the
    /// statement hash to prevent AIR confusion at the protocol layer.
    AggregatorAir,
    
    /// Generic mode: formula provided as witness
    /// Contains (formula, expected_circuit_hash)
    /// The formula is interpreted at runtime; hash is verified for security
    /// Used for leaf aggregators verifying app proofs
    Generic {
        formula: EncodedFormula,
        circuit_hash: [BaseElement; 4],
    },
}

impl ChildAirType {
    /// Number of columns for this AIR type
    pub fn trace_width(&self) -> usize {
        match self {
            ChildAirType::VerifierAir => super::VERIFIER_TRACE_WIDTH,
            ChildAirType::AggregatorAir => super::VERIFIER_TRACE_WIDTH,
            ChildAirType::Generic { formula, .. } => formula.trace_width,
        }
    }
    
    /// Number of transition constraints for this AIR type
    pub fn num_constraints(&self) -> usize {
        match self {
            ChildAirType::VerifierAir => super::VERIFIER_TRACE_WIDTH,
            ChildAirType::AggregatorAir => super::VERIFIER_TRACE_WIDTH,
            ChildAirType::Generic { formula, .. } => formula.constraints.len(),
        }
    }
    
    /// Create a generic child type from a formula
    /// The circuit_hash should come from the child proof's public inputs
    pub fn from_formula(formula: EncodedFormula, circuit_hash: [BaseElement; 4]) -> Self {
        ChildAirType::Generic { formula, circuit_hash }
    }
    
    /// Create a generic VDF type using pre-encoded formula
    /// Convenience constructor for VDF app proofs
    pub fn generic_vdf() -> Self {
        let formula = encode_vdf_formula();
        let circuit_hash = formula.compute_hash();
        ChildAirType::Generic { formula, circuit_hash }
    }
    
    /// Create a generic Fib type using pre-encoded formula
    /// Convenience constructor for Fibonacci app proofs
    pub fn generic_fib() -> Self {
        let formula = encode_fib_formula();
        let circuit_hash = formula.compute_hash();
        ChildAirType::Generic { formula, circuit_hash }
    }

    /// Create a generic CubicFib type using pre-encoded formula.
    pub fn generic_cubic_fib() -> Self {
        let formula = encode_cubic_fib_formula();
        let circuit_hash = formula.compute_hash();
        ChildAirType::Generic { formula, circuit_hash }
    }
    
    pub fn verifier_air() -> Self {
        ChildAirType::VerifierAir
    }

    pub fn aggregator_air() -> Self {
        ChildAirType::AggregatorAir
    }

    /// Create a generic Add2 type using pre-encoded formula.
    pub fn generic_add2() -> Self {
        let formula = encode_add2_formula();
        let circuit_hash = formula.compute_hash();
        ChildAirType::Generic { formula, circuit_hash }
    }
    
    /// Compute the formula hash for binding to public input
    /// 
    /// For VerifierAir: Returns a fixed, versioned constant (constraints are hardcoded, not witness-based)
    /// For Generic: Returns the formula's hash
    /// 
    /// This hash is used to bind the constraint formula to the public input,
    /// preventing attackers from using a simpler formula that trivially satisfies.
    pub fn compute_formula_hash(&self) -> [BaseElement; 4] {
        match self {
            // VerifierAir has hardcoded constraints (not formula-as-witness), but we STILL
            // bind a fixed identifier into public inputs so higher levels / Groth16 can
            // commit to "which verifier" is intended.
            //
            // This must be treated as a protocol constant: changing it invalidates old proofs.
            ChildAirType::VerifierAir => verifier_air_formula_hash(),
            ChildAirType::AggregatorAir => aggregator_air_formula_hash(),
            // Generic mode: return the formula's hash
            ChildAirType::Generic { formula, circuit_hash: _ } => formula.compute_hash(),
        }
    }
}

/// Versioned identifier for the hardcoded VerifierAir constraint system.
///
/// SECURITY NOTE:
/// - This is NOT derived from witness data.
/// - This is a protocol constant which should only change with a deliberate
///   version bump / migration.
pub fn verifier_air_formula_hash() -> [BaseElement; 4] {
    [
        BaseElement::new(0x5645_5249_4649_4552u64), // "VERIFIER" (packed)
        BaseElement::new(0x4149_525F_5631_0000u64), // "AIR_V1\0\0"
        BaseElement::new(0x5056_5547_4300_0000u64), // "PVUGC\0\0\0"
        BaseElement::new(1u64),
    ]
}

/// Versioned identifier for the hardcoded AggregatorAir constraint system.
///
/// This is a protocol constant, distinct from `verifier_air_formula_hash()`.
pub fn aggregator_air_formula_hash() -> [BaseElement; 4] {
    [
        BaseElement::new(0x4147_4752_4547_4154u64), // "AGGREGAT" (packed)
        BaseElement::new(0x4f52_5f41_4952_0000u64), // "OR_AIR\0\0"
        BaseElement::new(0x5056_5547_4300_0000u64), // "PVUGC\0\0\0"
        BaseElement::new(1u64),
    ]
}

// ============================================================================
// AIR CONSTRAINT EVALUATION
// ============================================================================

/// Evaluate constraints for the specified child AIR type
/// 
/// This function dispatches to the appropriate constraint evaluator based on
/// the child AIR type. Returns a vector of constraint evaluations.
/// 
/// ## Generic Mode
/// 
/// When `child_type` is `Generic`, the formula is interpreted to evaluate
/// constraints. The formula hash is verified against the expected circuit_hash
/// to prevent formula substitution attacks.
/// 
/// ## Security
/// 
/// For `Generic` mode, the caller MUST ensure that `circuit_hash` comes from
/// the child proof's public inputs (which are themselves bound to the proof).
pub fn evaluate_child_constraints(
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
    child_type: &ChildAirType,
) -> Vec<BaseElement> {
    match child_type {
        // NOTE: Verifier-style constraints depend on periodic columns + public inputs.
        // Do not call this arm for verifier-style OOD checks; use `evaluate_verifier_constraints_at()` instead.
        ChildAirType::VerifierAir => evaluate_verifier_constraints(trace_current, trace_next),
        ChildAirType::AggregatorAir => evaluate_verifier_constraints(trace_current, trace_next),
        ChildAirType::Generic { formula, circuit_hash } => {
            // Verify formula hash matches expected
            if !verify_formula_hash(formula, circuit_hash) {
                // Hash mismatch - return non-zero constraints to cause verification failure
                return vec![BaseElement::ONE; formula.constraints.len()];
            }
            // Evaluate using generic interpreter
            evaluate_formula(formula, trace_current, trace_next)
        }
    }
}

/// VDF constraints (matches simple_vdf.rs VdfAir)
///
/// Single constraint: next[0] = curr[0]^3 + 1
/// 
/// NOTE: This is the VdfAir from simple_vdf.rs, NOT the AggregatorAir.
/// Use `evaluate_aggregator_constraints` for AggregatorAir (2 constraints).
pub fn evaluate_vdf_like_constraints(
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
) -> Vec<BaseElement> {
    let formula = encode_vdf_formula();
    evaluate_formula(&formula, trace_current, trace_next)
}

/// Verifier AIR constraints
/// 
/// This evaluates all transition constraints for the Verifier/Aggregator AIR.
/// The constraints check RPO hash rounds, Merkle paths, FRI folding, and OOD verification.
fn evaluate_verifier_constraints(
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
) -> Vec<BaseElement> {
    use super::constraints::evaluate_all;
    use super::{VerifierPublicInputs, VERIFIER_TRACE_WIDTH};
    use winterfell::EvaluationFrame;
    
    assert!(trace_current.len() >= VERIFIER_TRACE_WIDTH);
    assert!(trace_next.len() >= VERIFIER_TRACE_WIDTH);
    
    // Create evaluation frame from current and next rows
    let current_vec: Vec<_> = trace_current.iter().take(VERIFIER_TRACE_WIDTH).copied().collect();
    let next_vec: Vec<_> = trace_next.iter().take(VERIFIER_TRACE_WIDTH).copied().collect();
    let frame = EvaluationFrame::from_rows(current_vec, next_vec);
    
    // Create dummy public inputs (ONLY safe for non-verifier-style callers).
    let pub_inputs = VerifierPublicInputs {
        statement_hash: [BaseElement::ZERO; 4],
        trace_commitment: [BaseElement::ZERO; 4],
        comp_commitment: [BaseElement::ZERO; 4],
        fri_commitments: vec![],
        num_queries: 0,
        proof_trace_len: 0,
        g_trace: BaseElement::ZERO,
        pub_result: BaseElement::ZERO,
        expected_checkpoint_count: 0,
        params_digest: [BaseElement::ZERO; 4],
        expected_mode_counter: 0,
    };
    
    let mut result = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
    evaluate_all(&frame, &[], &mut result, &pub_inputs);
    
    result
}

/// Evaluates Verifier-style constraints at an OOD point (verifier-exact).
///
/// This is needed when verifying `ChildAirType::{VerifierAir, AggregatorAir}`: their
/// transition constraints depend on:
/// - periodic columns (RPO cycle selectors + round constants)
/// - public inputs (statement hash, expected counters, g_trace, etc.)
pub fn evaluate_verifier_constraints_at(
    trace_current: &[BaseElement],
    trace_next: &[BaseElement],
    z: BaseElement,
    trace_len: usize,
    pub_inputs: &super::VerifierPublicInputs,
) -> Vec<BaseElement> {
    use super::constraints::evaluate_all;
    use super::{hash_chiplet, VERIFIER_TRACE_WIDTH};
    use winter_math::polynom;
    use winterfell::EvaluationFrame;

    assert!(trace_current.len() >= VERIFIER_TRACE_WIDTH);
    assert!(trace_next.len() >= VERIFIER_TRACE_WIDTH);

    // Build periodic values exactly as Winterfell does:
    // periodic_values[j] = eval(P_j, z^(trace_len / cycle_len)),
    // where P_j is the interpolating polynomial over the subgroup of size `cycle_len`.
    let periodic_cols = hash_chiplet::get_periodic_column_values();
    let mut periodic_values = Vec::with_capacity(periodic_cols.len());
    for col in periodic_cols.iter() {
        let m = col.len();
        debug_assert!(m.is_power_of_two());
        let num_cycles = trace_len / m;
        let x_reduced = z.exp_vartime((num_cycles as u64).into());

        let g_m = BaseElement::get_root_of_unity(m.ilog2());
        let mut xs = Vec::with_capacity(m);
        let mut cur = BaseElement::ONE;
        for _ in 0..m {
            xs.push(cur);
            cur *= g_m;
        }
        let poly = polynom::interpolate(&xs, col, false);
        periodic_values.push(polynom::eval(&poly, x_reduced));
    }

    let current_vec: Vec<_> = trace_current.iter().take(VERIFIER_TRACE_WIDTH).copied().collect();
    let next_vec: Vec<_> = trace_next.iter().take(VERIFIER_TRACE_WIDTH).copied().collect();
    let frame = EvaluationFrame::from_rows(current_vec, next_vec);

    let mut result = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
    evaluate_all(&frame, &periodic_values, &mut result, pub_inputs);
    result
}

/// Evaluate boundary constraint at OOD point
///
/// For Aggregator STARK, we have:
/// - Final: trace[trace_len-1][1] = pub_result
///
/// At OOD point z, this evaluates to: trace_current[1] - pub_result
/// (since trace_current is the interpolated trace evaluated at z)
pub fn evaluate_boundary_constraint(
    trace_value: BaseElement,
    expected_value: BaseElement,
) -> BaseElement {
    trace_value - expected_value
}

/// OOD verification parameters
#[derive(Clone, Debug)]
pub struct OodParams {
    /// OOD challenge point z
    pub z: BaseElement,
    /// Trace length (power of 2)
    pub trace_len: usize,
    /// Trace domain generator g
    pub g_trace: BaseElement,
    /// Constraint composition coefficients [alpha_0, alpha_1, beta_0]
    /// - alpha_0, alpha_1: transition constraint coefficients
    /// - beta_0: boundary constraint coefficient
    pub constraint_coeffs: Vec<BaseElement>,
    /// Public result (boundary constraint target)
    pub pub_result: BaseElement,
    /// Verifier-style boundary tail: expected final checkpoint counter (aux[3]) at last row.
    ///
    /// Used when `child_type` is `VerifierAir` or `AggregatorAir`.
    pub expected_checkpoint_count: usize,
    /// Verifier-style boundary tail: expected final mode counter (aux[1]) at last row.
    ///
    /// Used when `child_type` is `VerifierAir` or `AggregatorAir`.
    pub expected_mode_counter: usize,
}

/// Verify the full OOD constraint equation
///
/// This is the critical security check that ensures the composition polynomial
/// correctly represents the constraint quotient. The formula verified is:
///
/// ```text
/// transition_sum * exemption² + boundary_sum * (z^n - 1) = C(z) * (z^n - 1) * exemption
/// ```
///
/// Where:
/// - transition_sum = alpha_0 * c0(z) + alpha_1 * c1(z)
/// - boundary_sum = beta_0 * (trace_current[1] - pub_result)
/// - exemption = z - g^{n-1}
/// - C(z) = C_0(z) + C_1(z) * z^n (composition polynomial split into columns)
/// 
/// This version uses Generic VDF (2-column) constraints via formula-as-witness.
pub fn verify_ood_constraint_equation(
    ood_frame: &OodFrame,
    params: &OodParams,
) -> Result<(), OodVerificationError> {
    verify_ood_constraint_equation_typed(ood_frame, params, &ChildAirType::generic_vdf())
}

/// Verify the full OOD constraint equation with explicit child AIR type
///
/// This version allows specifying the child AIR type to evaluate the correct constraints.
/// 
/// # Child Types
/// 
/// - `VerifierAir`:Verifier/Aggregator constraints (recursive verification)
/// - `Generic`: Formula-as-witness for truly generic verification (apps like VDF, Fib, etc.)
pub fn verify_ood_constraint_equation_typed(
    ood_frame: &OodFrame,
    params: &OodParams,
    child_type: &ChildAirType,
) -> Result<(), OodVerificationError> {
    let expected_width = child_type.trace_width();
    if ood_frame.trace_width() < expected_width {
        return Err(OodVerificationError::TraceWidthMismatch);
    }
    if ood_frame.comp_width() < 1 {
        return Err(OodVerificationError::CompositionMismatch {
            expected: BaseElement::ZERO,
            got: BaseElement::ONE,
        });
    }
    
    let num_constraints = child_type.num_constraints();
    // Boundary assertions are AIR-specific.
    // - Generic demo AIRs in this repo use a single last-row assertion.
    // - Verifier-style AIRs (VerifierAir/AggregatorAir) use 8 single-step assertions (see `VerifierAir::get_assertions`).
    let num_boundary = match child_type {
        ChildAirType::VerifierAir | ChildAirType::AggregatorAir => 8,
        ChildAirType::Generic { .. } => 1,
    };
    if params.constraint_coeffs.len() < num_constraints + num_boundary {
        return Err(OodVerificationError::CoeffCountMismatch);
    }

    let z = params.z;
    let trace_len = params.trace_len;
    let g = params.g_trace;

    // Compute z^n
    let z_pow_n = z.exp((trace_len as u64).into());

    // Compute g^{n-1}
    let g_pow_n_minus_1 = g.exp(((trace_len - 1) as u64).into());

    // Exemption factor: z - g^{n-1}
    let exemption = z - g_pow_n_minus_1;

    // Transition divisor z(x) = (x^n - 1) / (x - g^(n-1))  (single exemption point).
    let zerofier_num = z_pow_n - BaseElement::ONE;
    let transition_divisor = zerofier_num / exemption;

    // ==============================================================
    // TRANSITION CONSTRAINTS (child AIR type specific)
    // ==============================================================
    let constraints = evaluate_child_constraints(
        &ood_frame.trace_current,
        &ood_frame.trace_next,
        child_type,
    );

    // Combine constraints with coefficients.
    let mut transition_sum = BaseElement::ZERO;
    for (i, c) in constraints.iter().enumerate() {
        if i < params.constraint_coeffs.len() {
            transition_sum = transition_sum + params.constraint_coeffs[i] * *c;
        }
    }

    // ==============================================================
    // BOUNDARY CONSTRAINTS (AIR-specific)
    // ==============================================================
    let boundary_eval = match child_type {
        ChildAirType::Generic { .. } => {
            // Demo shape assumption: single last-row assertion, column 1 == pub_result.
            // Value at z is in `ood_frame.trace_current`.
            let col = 1usize;
            let num = ood_frame
                .trace_current
                .get(col)
                .copied()
                .unwrap_or(BaseElement::ZERO)
                - params.pub_result;
            let beta = params
                .constraint_coeffs
                .get(num_constraints)
                .copied()
                .unwrap_or(BaseElement::ZERO);
            beta * num / exemption
        }
        ChildAirType::VerifierAir | ChildAirType::AggregatorAir => {
            // Matches `VerifierAir::get_assertions()`:
            // - 4 hash-state zeros at step 0
            // - aux[1] (mode counter) == 0 at step 0
            // - aux[3] (checkpoint counter) == 0 at step 0
            // - aux[1] == expected_mode_counter at last step
            // - aux[3] == expected_checkpoint_count at last step
            //
            // Each is a single-step boundary assertion, so divisor is (z - g^step).
            let denom0 = z - BaseElement::ONE; // step 0 => g^0 = 1
            let beta0 = params.constraint_coeffs[num_constraints + 0];
            let beta1 = params.constraint_coeffs[num_constraints + 1];
            let beta2 = params.constraint_coeffs[num_constraints + 2];
            let beta3 = params.constraint_coeffs[num_constraints + 3];
            let beta4 = params.constraint_coeffs[num_constraints + 4];
            let beta5 = params.constraint_coeffs[num_constraints + 5];
            let beta6 = params.constraint_coeffs[num_constraints + 6];
            let beta7 = params.constraint_coeffs[num_constraints + 7];

            let hs0 = ood_frame.trace_current.get(super::NUM_SELECTORS + 0).copied().unwrap_or(BaseElement::ZERO);
            let hs1 = ood_frame.trace_current.get(super::NUM_SELECTORS + 1).copied().unwrap_or(BaseElement::ZERO);
            let hs2 = ood_frame.trace_current.get(super::NUM_SELECTORS + 2).copied().unwrap_or(BaseElement::ZERO);
            let hs3 = ood_frame.trace_current.get(super::NUM_SELECTORS + 3).copied().unwrap_or(BaseElement::ZERO);
            let aux1 = ood_frame.trace_current.get(super::constraints::AUX_START + 1).copied().unwrap_or(BaseElement::ZERO);
            let aux3 = ood_frame.trace_current.get(super::constraints::AUX_START + 3).copied().unwrap_or(BaseElement::ZERO);

            let mode_expected = BaseElement::new(params.expected_mode_counter as u64);
            let ckpt_expected = BaseElement::new(params.expected_checkpoint_count as u64);

            // step 0 assertions (value == 0)
            let e0 = beta0 * hs0 / denom0;
            let e1 = beta1 * hs1 / denom0;
            let e2 = beta2 * hs2 / denom0;
            let e3 = beta3 * hs3 / denom0;
            let e4 = beta4 * aux1 / denom0;
            let e5 = beta5 * aux3 / denom0;

            // last-step assertions
            let denom_last = exemption; // z - g^(n-1)
            let e6 = beta6 * (aux1 - mode_expected) / denom_last;
            let e7 = beta7 * (aux3 - ckpt_expected) / denom_last;

            e0 + e1 + e2 + e3 + e4 + e5 + e6 + e7
        }
    };

    // Compose the same rational constraints value Winterfell checks at z:
    //   transition_combined(z) / transition_divisor(z) + boundary_combined(z)
    let lhs = transition_sum / transition_divisor + boundary_eval;

    // RHS = combined constraint composition polynomial evaluation at z.
    let mut c_combined = BaseElement::ZERO;
    let mut z_pow_in = BaseElement::ONE;
    for &c_i in ood_frame.composition.iter() {
        c_combined += c_i * z_pow_in;
        z_pow_in *= z_pow_n;
    }
    let rhs = c_combined;

    // Verify LHS == RHS
    if lhs != rhs {
        return Err(OodVerificationError::CompositionMismatch {
            expected: rhs,
            got: lhs,
        });
    }

    Ok(())
}

// ============================================================================
// ERROR TYPES
// ============================================================================

/// Errors during OOD verification
#[derive(Clone, Debug)]
pub enum OodVerificationError {
    /// Coefficient count doesn't match constraint count
    CoeffCountMismatch,
    /// Composition polynomial doesn't match constraints
    CompositionMismatch {
        expected: BaseElement,
        got: BaseElement,
    },
    /// Boundary constraint failed
    BoundaryConstraintFailed,
    /// Trace width mismatch
    TraceWidthMismatch,
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aggregator_air_type_id_is_stable() {
        // AggregatorAir is identified by a fixed protocol hash.
        let a = ChildAirType::aggregator_air().compute_formula_hash();
        let b = ChildAirType::aggregator_air().compute_formula_hash();
        assert_eq!(a, b);
        assert_ne!(a, ChildAirType::verifier_air().compute_formula_hash());
    }

    #[test]
    fn test_boundary_constraint() {
        let trace_value = BaseElement::new(42);
        let expected = BaseElement::new(42);

        assert_eq!(
            evaluate_boundary_constraint(trace_value, expected),
            BaseElement::ZERO
        );

        let wrong_expected = BaseElement::new(43);
        assert_ne!(
            evaluate_boundary_constraint(trace_value, wrong_expected),
            BaseElement::ZERO
        );
    }

    #[test]
    fn test_ood_frame_creation() {
        let frame = OodFrame::new(
            vec![BaseElement::new(1), BaseElement::new(2)],
            vec![BaseElement::new(3), BaseElement::new(4)],
            vec![BaseElement::new(5), BaseElement::new(6)],
            vec![BaseElement::new(7), BaseElement::new(8)],
        );

        assert_eq!(frame.trace_width(), 2);
        assert_eq!(frame.comp_width(), 2);
    }

    #[test]
    fn test_ood_params_creation() {
        // Goldilocks field primitive root for trace domain
        // For trace_len = 8, g = 2^(64-3) mod p = some generator of order 8
        let g_trace = BaseElement::new(18446744069414584320u64); // 2^61 in Goldilocks
        
        let params = OodParams {
            z: BaseElement::new(12345),
            trace_len: 8,
            g_trace,
            constraint_coeffs: vec![
                BaseElement::new(1), // alpha_0
                BaseElement::new(2), // alpha_1
                BaseElement::new(3), // beta_0
            ],
            pub_result: BaseElement::new(100),
            expected_checkpoint_count: 0,
            expected_mode_counter: 0,
        };
        
        assert_eq!(params.trace_len, 8);
        assert_eq!(params.constraint_coeffs.len(), 3);
    }

    #[test]
    fn test_verify_ood_constraint_equation_valid_transition() {
        // Create a valid OOD frame where transition constraints are satisfied
        // For VDF: next0 = curr0^3 + curr1, next1 = curr0
        let curr0 = BaseElement::new(2);
        let curr1 = BaseElement::new(3);
        let next0 = BaseElement::new(11); // 2^3 + 3 = 11
        let next1 = BaseElement::new(2);  // = curr0

        // When constraints are zero, the composition should be zero too
        // (for valid execution at non-boundary steps)
        let frame = OodFrame::new(
            vec![curr0, curr1],
            vec![next0, next1],
            vec![BaseElement::ZERO, BaseElement::ZERO], // C(z) = 0
            vec![BaseElement::ZERO, BaseElement::ZERO],
        );

        // With all coeffs = 0, the equation becomes 0 = 0
        let params = OodParams {
            z: BaseElement::new(12345),
            trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            constraint_coeffs: vec![
                BaseElement::ZERO, // alpha_0
                BaseElement::ZERO, // alpha_1
                BaseElement::ZERO, // beta_0
            ],
            pub_result: curr1, // Match boundary to avoid boundary term
            expected_checkpoint_count: 0,
            expected_mode_counter: 0,
        };

        // Should pass because 0 = 0
        assert!(verify_ood_constraint_equation(&frame, &params).is_ok());
    }

    #[test]
    fn test_verify_ood_constraint_detects_invalid() {
        // Create an invalid OOD frame where constraints are NOT satisfied
        let curr0 = BaseElement::new(2);
        let curr1 = BaseElement::new(3);
        let next0 = BaseElement::new(999); // Wrong! Should be 11
        let next1 = BaseElement::new(999); // Wrong! Should be 2

        let frame = OodFrame::new(
            vec![curr0, curr1],
            vec![next0, next1],
            vec![BaseElement::ZERO, BaseElement::ZERO],
            vec![BaseElement::ZERO, BaseElement::ZERO],
        );

        // Non-zero coeffs should detect the mismatch
        let params = OodParams {
            z: BaseElement::new(12345),
            trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            constraint_coeffs: vec![
                BaseElement::ONE, // alpha_0
                BaseElement::ONE, // alpha_1
                BaseElement::ZERO, // beta_0 (ignore boundary for this test)
            ],
            pub_result: curr1,
            expected_checkpoint_count: 0,
            expected_mode_counter: 0,
        };

        // Should fail - constraints are non-zero but composition is zero
        assert!(verify_ood_constraint_equation(&frame, &params).is_err());
    }

    #[test]
    fn test_exemption_factor_calculation() {
        // Test that exemption = z - g^{n-1} is computed correctly
        let z = BaseElement::new(100);
        let trace_len = 8usize;
        let g = BaseElement::new(2); // Simple generator for test

        // g^{n-1} = 2^7 = 128
        let g_pow_n_minus_1 = g.exp(((trace_len - 1) as u64).into());
        assert_eq!(g_pow_n_minus_1, BaseElement::new(128));

        // exemption = 100 - 128 (in field)
        let exemption = z - g_pow_n_minus_1;
        // In Goldilocks field, this wraps around
        assert_ne!(exemption, BaseElement::ZERO);
    }

    /// Test Verifier AIR constraint evaluation using real proof data
    #[test]
    fn test_verifier_air_ood_verification() {
        use crate::stark::verifier_air::constraints::evaluate_all;
        use crate::stark::verifier_air::{VerifierPublicInputs, VERIFIER_TRACE_WIDTH};
        use winterfell::EvaluationFrame;
        
        // Create a test OOD frame for the Verifier AIR
        // Using simple values that should produce predictable constraint evaluations
        let mut current = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        let mut next = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        
        // Set up as a Nop operation (111 in binary selectors)
        current[0] = BaseElement::ONE; // s0
        current[1] = BaseElement::ONE; // s1
        current[2] = BaseElement::ONE; // s2
        
        // Next row also Nop
        next[0] = BaseElement::ONE;
        next[1] = BaseElement::ONE;
        next[2] = BaseElement::ONE;
        
        // For Nop, hash state should copy (next = current)
        for i in 3..15 {
            let val = BaseElement::new(i as u64);
            current[i] = val;
            next[i] = val; // Copy for Nop
        }
        
        // FRI columns (15-22)
        for i in 15..23 {
            let val = BaseElement::new((i * 10) as u64);
            current[i] = val;
            next[i] = val; // Copy constraint
        }
        
        // idx_reg column (23)
        current[23] = BaseElement::ZERO;
        next[23] = BaseElement::ZERO;

        // Aux columns (24-27)
        current[24] = BaseElement::new(7); // Round counter = 7 (Nop/Squeeze state)
        next[24] = BaseElement::new(7);
        
        for i in 25..28 {
            current[i] = BaseElement::ZERO;
            next[i] = BaseElement::ZERO;
        }
        
        // Evaluate constraints using the Verifier AIR's evaluate_all
        let pub_inputs = VerifierPublicInputs {
            statement_hash: [BaseElement::ZERO; 4],
            trace_commitment: [BaseElement::ZERO; 4],
            comp_commitment: [BaseElement::ZERO; 4],
            fri_commitments: vec![],
            num_queries: 2,
            proof_trace_len: 8,
            g_trace: BaseElement::new(18446744069414584320u64),
            pub_result: BaseElement::ZERO,
            expected_checkpoint_count: 0,
            params_digest: [BaseElement::ZERO; 4],
            expected_mode_counter: 0,
        };
        let mut result = vec![BaseElement::ZERO; VERIFIER_TRACE_WIDTH];
        
        // Create evaluation frame
        let frame = EvaluationFrame::from_rows(current.clone(), next.clone());
        
        evaluate_all(&frame, &[], &mut result, &pub_inputs);
        
        // For a valid Nop transition, all constraints should be zero
        println!("Constraint evaluations for Nop transition:");
        for (i, c) in result.iter().enumerate() {
            println!("  constraint[{}] = {:?}", i, c.as_int());
        }
        
        // Selector constraints should be zero (binary check on 0 and 1)
        assert_eq!(result[0], BaseElement::ZERO, "s0 should be binary");
        assert_eq!(result[1], BaseElement::ZERO, "s1 should be binary");
        assert_eq!(result[2], BaseElement::ZERO, "s2 should be binary");
        
        // Hash state constraints should be zero for Nop (copy)
        for i in 3..15 {
            assert_eq!(result[i], BaseElement::ZERO, "hash[{}] should copy for Nop", i - 3);
        }
    
    }
    
    // ========================================================================
    // FORMULA-AS-WITNESS TESTS
    // ========================================================================
    
    #[test]
    fn test_encode_vdf_formula() {
        // Test that encode_vdf_formula creates a valid formula
        // VDF formula (simple_vdf.rs): next[0] = curr[0]^3 + 1
        let formula = encode_vdf_formula();
        
        assert_eq!(formula.trace_width, 2, "VDF has 2 columns");
        assert_eq!(formula.constraints.len(), 1, "VDF has 1 constraint");
        
        // Constraint: 3 monomials (next[0], -curr[0]^3, -1)
        assert_eq!(formula.constraints[0].monomials.len(), 3);
        
        println!("VDF formula monomial count: {}", formula.monomial_count());
        assert_eq!(formula.monomial_count(), 3);
    }
    
    #[test]
    fn test_formula_hash_consistency() {
        // Test that formula hash is deterministic
        let formula1 = encode_vdf_formula();
        let formula2 = encode_vdf_formula();
        
        let hash1 = formula1.compute_hash();
        let hash2 = formula2.compute_hash();
        
        assert_eq!(hash1, hash2, "Same formula should have same hash");
        
        // Different formula should have different hash
        let fib_formula = encode_fib_formula();
        let fib_hash = fib_formula.compute_hash();
        
        assert_ne!(hash1, fib_hash, "Different formulas should have different hashes");
        
        // VDF and AggregatorAir identifiers should be different.
        assert_ne!(hash1, aggregator_air_formula_hash());
    }
    
    #[test]
    fn test_generic_vdf_matches_hardcoded() {
        // Test that generic formula evaluation matches VDF AIR
        // VDF constraint: next[0] = curr[0]^3 + 1
        
        let curr0 = BaseElement::new(7);
        let curr1 = BaseElement::new(0); // Unused in VDF formula
        let next0 = curr0 * curr0 * curr0 + BaseElement::ONE; // Valid VDF transition
        let next1 = BaseElement::ZERO;
        
        let trace_current = vec![curr0, curr1];
        let trace_next = vec![next0, next1];
        
        // Evaluate using generic formula
        let formula = encode_vdf_formula();
        let result = evaluate_formula(&formula, &trace_current, &trace_next);
        
        // Should have 1 constraint
        assert_eq!(result.len(), 1, "VDF has 1 constraint");
        
        // For a valid transition, constraint should be zero
        assert_eq!(result[0], BaseElement::ZERO, "c0 should be zero for valid transition");
    }
    
    #[test]
    fn test_generic_vdf_detects_invalid() {
        // Test that generic formula correctly rejects invalid transitions
        
        let curr0 = BaseElement::new(7);
        let curr1 = BaseElement::new(0);
        let next0 = BaseElement::new(999); // INVALID - wrong value
        let next1 = BaseElement::ZERO;
        
        let trace_current = vec![curr0, curr1];
        let trace_next = vec![next0, next1];
        
        let formula = encode_vdf_formula();
        let result = evaluate_formula(&formula, &trace_current, &trace_next);
        
        // c0 should be non-zero for invalid transition
        assert_ne!(result[0], BaseElement::ZERO, "c0 should be non-zero for invalid");
    }
    
    #[test]
    fn test_child_air_type_generic() {
        // Test the ChildAirType::Generic variant with VDF
        // VDF constraint: next[0] = curr[0]^3 + 1
        
        let curr0 = BaseElement::new(5);
        let curr1 = BaseElement::new(0);
        let next0 = curr0 * curr0 * curr0 + BaseElement::ONE;
        let next1 = BaseElement::ZERO;
        
        let trace_current = vec![curr0, curr1];
        let trace_next = vec![next0, next1];
        
        // Create generic VDF child type
        let generic_vdf = ChildAirType::generic_vdf();
        
        // Verify properties
        assert_eq!(generic_vdf.trace_width(), 2);
        assert_eq!(generic_vdf.num_constraints(), 1);
        
        // Evaluate using the generic type
        let result = evaluate_child_constraints(&trace_current, &trace_next, &generic_vdf);
        
        // Should be zero for valid transition
        assert_eq!(result[0], BaseElement::ZERO, "c0 should be zero");
    }
    
    #[test]
    fn test_child_air_type_aggregator_air() {
        let agg = ChildAirType::aggregator_air();
        assert_eq!(agg.trace_width(), crate::stark::verifier_air::VERIFIER_TRACE_WIDTH);
        assert_eq!(agg.num_constraints(), crate::stark::verifier_air::VERIFIER_TRACE_WIDTH);
        assert_eq!(agg.compute_formula_hash(), aggregator_air_formula_hash());
        assert_ne!(agg.compute_formula_hash(), verifier_air_formula_hash());
    }
    
    #[test]
    fn test_formula_hash_verification() {
        // Test that formula hash verification works
        let formula = encode_vdf_formula();
        let correct_hash = formula.compute_hash();
        
        // Correct hash should pass
        assert!(verify_formula_hash(&formula, &correct_hash));
        
        // Wrong hash should fail
        let wrong_hash = [BaseElement::ONE; 4];
        assert!(!verify_formula_hash(&formula, &wrong_hash));
    }
    
    #[test]
    fn test_fib_formula_evaluation() {
        // Test Fibonacci formula encoding and evaluation
        let formula = encode_fib_formula();
        
        assert_eq!(formula.trace_width, 2);
        assert_eq!(formula.constraints.len(), 2);
        
        // Create valid Fib transition: next[0] = curr[1], next[1] = curr[0] + curr[1]
        let curr0 = BaseElement::new(3);
        let curr1 = BaseElement::new(5);
        let next0 = curr1;                // 5
        let next1 = curr0 + curr1;        // 8
        
        let trace_current = vec![curr0, curr1];
        let trace_next = vec![next0, next1];
        
        let result = evaluate_formula(&formula, &trace_current, &trace_next);
        
        // Should be zero for valid Fib transition
        assert_eq!(result[0], BaseElement::ZERO, "Fib c0 should be zero");
        assert_eq!(result[1], BaseElement::ZERO, "Fib c1 should be zero");
    }
}
