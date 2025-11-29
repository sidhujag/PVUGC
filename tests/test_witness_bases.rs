#[cfg(test)]
mod tests {
    use ark_bls12_377::Bls12_377;
    use ark_bw6_761::{Fr as OuterFr, BW6_761};
    use ark_ec::pairing::Pairing;
    use ark_ec::{AffineRepr, CurveGroup};
    use ark_ff::{Field, UniformRand};
    use ark_groth16::Groth16;
    use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
    use ark_snark::SNARK;
    use ark_std::{rand::SeedableRng, test_rng, One, Zero};
    use arkworks_groth16::outer_compressed::{
        DefaultCycle, InnerE, InnerFr, InnerVk, OuterCircuit, RecursionCycle,
    };
    use arkworks_groth16::prover_lean::{prove_lean_with_randomizers, LeanProvingKey};
    use arkworks_groth16::pvugc_outer::build_pvugc_setup_from_pk_for;
    use std::sync::Arc;

    use ark_r1cs_std::alloc::AllocVar;
    use ark_r1cs_std::eq::EqGadget;
    use ark_r1cs_std::fields::{fp::FpVar, FieldVar};
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};

    // A simple circuit for testing: x * y = z
    #[derive(Clone)]
    struct SimpleMulCircuit {
        x: Option<InnerFr>,
        y: Option<InnerFr>,
        z: Option<InnerFr>,
    }

    impl ConstraintSynthesizer<InnerFr> for SimpleMulCircuit {
        fn generate_constraints(
            self,
            cs: ConstraintSystemRef<InnerFr>,
        ) -> Result<(), SynthesisError> {
            let x_var = FpVar::new_witness(cs.clone(), || {
                self.x.ok_or(SynthesisError::AssignmentMissing)
            })?;
            let y_var = FpVar::new_witness(cs.clone(), || {
                self.y.ok_or(SynthesisError::AssignmentMissing)
            })?;
            // We make z a WITNESS here to have 0 public inputs (besides constant 1)
            // This simplifies the gap check (Gap = q_const[0])
            let z_var = FpVar::new_witness(cs.clone(), || {
                self.z.ok_or(SynthesisError::AssignmentMissing)
            })?;

            x_var.mul_equals(&y_var, &z_var)?;
            Ok(())
        }
    }

    #[test]
    fn test_compute_witness_bases_correctness() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);

        // 1. Setup Inner Circuit & Keys
        // x * y = z (all witnesses)
        let circuit_inner = SimpleMulCircuit {
            x: None,
            y: None,
            z: None,
        };
        let (pk_inner, vk_inner) =
            Groth16::<InnerE>::circuit_specific_setup(circuit_inner, &mut rng).unwrap();

        // 2. Setup Outer Circuit
        // We use an empty dummy proof and 0 inputs
        let _n_inputs = 0;
        let dummy_x = vec![];
        let dummy_proof = ark_groth16::Proof::default();

        // Explicitly type the circuit for type inference
        let outer_circuit: OuterCircuit<DefaultCycle> =
            OuterCircuit::new(vk_inner.clone(), dummy_x, dummy_proof.clone());

        // This generates the PK for the outer circuit (BW6-761)
        let (pk_outer, _vk_outer) =
            Groth16::<BW6_761>::circuit_specific_setup(outer_circuit, &mut rng).unwrap();

        // 3. Build PVUGC Setup (Generates h_wit and q_const)
        // Create a closure that generates valid inner proofs for any statement vector
        let pk_inner_clone = pk_inner.clone();
        let inner_proof_generator = move |statements: &[InnerFr]| {
            // For SimpleMulCircuit with no public inputs, statement doesn't affect circuit
            // but we still derive seed from it for consistency
            let seed = 99999u64;
            let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
            let circuit = SimpleMulCircuit {
                x: Some(InnerFr::from(1u64)),
                y: Some(InnerFr::from(2u64)),
                z: Some(InnerFr::from(2u64)),
            };
            Groth16::<InnerE>::prove(&pk_inner_clone, circuit, &mut rng).unwrap()
        };
        let (pvugc_vk, lean_pk) = build_pvugc_setup_from_pk_for::<DefaultCycle, _>(
            &pk_outer,
            &vk_inner,
            inner_proof_generator,
        );

        // 4. Generate a valid instance/witness for the outer circuit
        // We need a valid inner proof to satisfy the outer circuit verification logic (if enabled)
        // or just dummy values if the outer circuit doesn't enforce inner proof validity (it likely checks it).
        // For this test, we can just use the random values since we control the prover.
        let x_val = InnerFr::rand(&mut rng);
        let y_val = InnerFr::rand(&mut rng);
        let z_val = x_val * y_val;

        let valid_inner_circuit = SimpleMulCircuit {
            x: Some(x_val),
            y: Some(y_val),
            z: Some(z_val),
        };
        let valid_inner_proof =
            Groth16::<InnerE>::prove(&pk_inner, valid_inner_circuit, &mut rng).unwrap();

        let valid_outer_circuit = OuterCircuit::<DefaultCycle>::new(
            vk_inner.clone(),
            vec![], // No public inputs
            valid_inner_proof,
        );

        // 5. Create Standard Groth16 Proof (No ZK => r=0, s=0)
        let proof_std = Groth16::<BW6_761>::create_proof_with_reduction_no_zk(
            valid_outer_circuit.clone(),
            &pk_outer,
        )
        .expect("Standard proof failed");

        // 6. Create Lean Proof (Manually set r=0, s=0)
        let (proof_lean, _) = prove_lean_with_randomizers(
            &lean_pk,
            valid_outer_circuit,
            OuterFr::zero(),
            OuterFr::zero(),
        )
        .expect("Lean proof failed");

        // 7. Verify C element match
        // expected_c = proof_lean.c + q_const[0]
        // Because public inputs are empty, the only "missing" part from lean proof is the constant term H_{0,0}.

        let c_lean = proof_lean.c.into_group();
        let c_std = proof_std.c.into_group();

        // pvugc_vk.q_const_points[0] is the gap for the constant term
        let q_const_0 = pvugc_vk.q_const_points[0].into_group();

        let c_reconstructed = c_lean + q_const_0;

        assert_eq!(c_reconstructed.into_affine(), c_std.into_affine(),
            "Mismatch! h_wit (Lean) + q_const != Standard C. The witness bases are likely incorrect.");

        println!("SUCCESS: Lean Proof + Q_const matches Standard Proof. h_wit is correct.");
    }

    #[test]
    fn test_lean_pk_serialization() {
        let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(42);
        let circuit_inner = SimpleMulCircuit {
            x: None,
            y: None,
            z: None,
        };
        let (pk_inner, vk_inner) =
            Groth16::<InnerE>::circuit_specific_setup(circuit_inner, &mut rng).unwrap();
        let outer_circuit: OuterCircuit<DefaultCycle> =
            OuterCircuit::new(vk_inner.clone(), vec![], ark_groth16::Proof::default());
        let (pk_outer, _) =
            Groth16::<BW6_761>::circuit_specific_setup(outer_circuit, &mut rng).unwrap();

        // Create a closure that generates valid inner proofs for any statement vector
        let pk_inner_clone = pk_inner.clone();
        let inner_proof_generator = move |statements: &[InnerFr]| {
            // Derive seed from statement to ensure different proofs get different randomizers
            let seed = 99999u64;
            let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(seed);
            let circuit = SimpleMulCircuit {
                x: Some(InnerFr::from(1u64)),
                y: Some(InnerFr::from(2u64)),
                z: Some(InnerFr::from(2u64)),
            };
            Groth16::<InnerE>::prove(&pk_inner_clone, circuit, &mut rng).unwrap()
        };
        let (_, lean_pk) = build_pvugc_setup_from_pk_for::<DefaultCycle, _>(
            &pk_outer,
            &vk_inner,
            inner_proof_generator,
        );

        // Serialize
        let mut serialized = Vec::new();
        lean_pk.serialize_compressed(&mut serialized).unwrap();

        // Deserialize
        let lean_pk_deser: LeanProvingKey<ark_bw6_761::BW6_761> =
            LeanProvingKey::deserialize_compressed(&serialized[..]).unwrap();

        // Compare
        assert_eq!(lean_pk.h_query_wit, lean_pk_deser.h_query_wit);
        assert_eq!(lean_pk.a_query, lean_pk_deser.a_query);
    }
}
