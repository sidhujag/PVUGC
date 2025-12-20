//! Shared test circuits for PVUGC testing
//!
//! Generic circuits that work on both InnerFr and OuterFr for flexible testing.

use ark_ff::PrimeField;
use ark_r1cs_std::alloc::AllocVar;
use ark_r1cs_std::eq::EqGadget;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

/// Addition circuit: x = y + z (generic over field)
///
/// Perfect for testing witness independence:
/// - Statement (public): x
/// - Witness (private): y, z such that x = y + z
/// - Multiple valid witnesses for same statement
#[derive(Clone)]
pub struct AddCircuit<F: PrimeField> {
    pub x: Option<F>,
    pub y: Option<F>,
    pub z: Option<F>,
}

impl<F: PrimeField> AddCircuit<F> {
    /// Create circuit with public input x and auto-generated witnesses
    ///
    /// x: PUBLIC (statement)
    /// y, z: PRIVATE (auto-generated such that x = y + z)
    pub fn with_public_input(public_x: F) -> Self {
        // Choose arbitrary witnesses y, z such that public_x = y + z
        // Simple split: y = x/2, z = x - y
        let two = F::from(2u64);
        let y = public_x / two;
        let z = public_x - y;

        Self {
            x: Some(public_x),
            y: Some(y),
            z: Some(z),
        }
    }

    /// Create circuit with public input and specific private witnesses
    ///
    /// public_x: PUBLIC (statement)
    /// witness_y, witness_z: PRIVATE (must satisfy public_x = witness_y + witness_z)
    pub fn new(public_x: F, witness_y: F, witness_z: F) -> Self {
        Self {
            x: Some(public_x),
            y: Some(witness_y),
            z: Some(witness_z),
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for AddCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let x_var = FpVar::new_input(cs.clone(), || {
            self.x.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let y_var = FpVar::new_witness(cs.clone(), || {
            self.y.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let z_var = FpVar::new_witness(cs.clone(), || {
            self.z.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let sum = &y_var + &z_var;
        x_var.enforce_equal(&sum)?;

        Ok(())
    }
}

/// Two-input circuit mimicking SP1's Groth16 wrapper structure
///
/// PUBLIC inputs:
/// - input1: First public input (e.g., vkey_hash)
/// - input2: Second public input (e.g., committed_values_digest)
///
/// PRIVATE witness:
/// - witness: A value that satisfies: witness = input1 + input2
#[derive(Clone)]
pub struct TwoInputCircuit<F: PrimeField> {
    pub input1: Option<F>,
    pub input2: Option<F>,
    pub witness: Option<F>,
}

impl<F: PrimeField> TwoInputCircuit<F> {
    /// Create circuit with two public inputs
    pub fn new(input1: F, input2: F) -> Self {
        let witness = input1 + input2;
        Self {
            input1: Some(input1),
            input2: Some(input2),
            witness: Some(witness),
        }
    }
    
    /// Create with specific witness
    pub fn with_witness(input1: F, input2: F, witness: F) -> Self {
        Self {
            input1: Some(input1),
            input2: Some(input2),
            witness: Some(witness),
        }
    }
}

impl<F: PrimeField> ConstraintSynthesizer<F> for TwoInputCircuit<F> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        // Two public inputs (like SP1's vkey_hash and committed_values_digest)
        let input1_var = FpVar::new_input(cs.clone(), || {
            self.input1.ok_or(SynthesisError::AssignmentMissing)
        })?;
        
        let input2_var = FpVar::new_input(cs.clone(), || {
            self.input2.ok_or(SynthesisError::AssignmentMissing)
        })?;

        let witness_var = FpVar::new_witness(cs.clone(), || {
            self.witness.ok_or(SynthesisError::AssignmentMissing)
        })?;

        // Constraint: witness = input1 + input2
        let sum = &input1_var + &input2_var;
        witness_var.enforce_equal(&sum)?;

        Ok(())
    }
}
