//! RPO-256 Compatibility Test (Using Light RPO)
//!
//! Verifies that our light GL-native RPO gadget produces identical output to Winterfell's Rp64_256
//! This validates that light RPO is a drop-in replacement for heavy RPO

use arkworks_groth16::gadgets::rpo_gl_light::{RpoParamsGLLight, rpo_hash_elements_light, rpo_merge_light};
use arkworks_groth16::gadgets::gl_fast::GlVar;
use arkworks_groth16::gadgets::gl_range::gl_alloc_u64_vec;
use arkworks_groth16::inner_stark_full::enforce_gl_eq;
use arkworks_groth16::outer_compressed::InnerFr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::{ConstraintSystem, ConstraintSystemRef};
use winter_crypto::hashers::Rp64_256;
use winter_crypto::{Hasher, Digest, ElementHasher};
use winter_math::fields::f64::BaseElement as GL;

#[test]
fn test_rpo_matches_winterfell_hash() {
    // Test vector: hash a short sequence
    let test_input = vec![
        GL::new(1),
        GL::new(2),
        GL::new(3),
        GL::new(4),
    ];
    
    // Host-side Winterfell hash
    let digest_host = Rp64_256::hash_elements(&test_input);
    let digest_bytes = digest_host.as_bytes();
    
    // Extract as 4 GL values (8 bytes each, LE)
    let mut expected = [0u64; 4];
    for i in 0..4 {
        let chunk = &digest_bytes[i*8..(i+1)*8];
        expected[i] = u64::from_le_bytes([
            chunk[0], chunk[1], chunk[2], chunk[3],
            chunk[4], chunk[5], chunk[6], chunk[7],
        ]);
    }
    
    // Circuit-side with LIGHT RPO
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    let input_fp = gl_alloc_u64_vec(cs.clone(), &[1,2,3,4]).unwrap();
    let input_gl: Vec<GlVar> = input_fp.iter().map(|fp| GlVar(fp.clone())).collect();
    let digest = rpo_hash_elements_light(cs.clone(), &input_gl, &RpoParamsGLLight::default()).unwrap();
    
    // Check lane-wise equality
    assert_eq!(digest.len(), 4);
    
    // Verify digest values are valid
    for lane in &digest {
        let _val = lane.0.value().unwrap();
    }
    
    for i in 0..4 {
        let expected_var = FpVar::constant(InnerFr::from(expected[i]));
        let matches = enforce_gl_eq(&digest[i].0, &expected_var);
        if matches.is_err() || !cs.is_satisfied().unwrap() {
            panic!("Light RPO mismatch at lane {}: expected {}, got circuit value", i, expected[i]);
        }
    }
    assert!(cs.is_satisfied().unwrap(), "Light RPO gadget doesn't match Winterfell on test vectors!");
}

#[test]
fn rpo_matches_winterfell_on_small_vectors() {
    use winter_crypto::hashers::Rp64_256;
    use winter_math::fields::f64::BaseElement as GL;
    use winter_crypto::ElementHasher;
    use ark_relations::r1cs::ConstraintSynthesizer;

    let _host = |xs: &[u64]| {
        let els: Vec<GL> = xs.iter().map(|&x| GL::try_from(x).unwrap()).collect();
        let d = Rp64_256::hash_elements(&els);
        let bytes = d.as_bytes(); // 32 bytes = 4 lanes
        bytes.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect::<Vec<_>>()
    };

    let cs = ConstraintSystem::<InnerFr>::new_ref();
    let _params = RpoParamsGLLight::default();

    // Simple wrapper to enter synthesis mode
    struct TestCircuit;
    impl ConstraintSynthesizer<InnerFr> for TestCircuit {
        fn generate_constraints(self, cs: ConstraintSystemRef<InnerFr>) -> Result<(), ark_relations::r1cs::SynthesisError> {
            // Test multiple input sizes to cover block boundaries
            for xs in [&[1u64][..], &[1,2], &[1,2,3,4], &[1,2,3,4,5,6,7,8], &[1,2,3,4,5,6,7,8,9]] {
                let expect = (|| {
                    let els: Vec<GL> = xs.iter().map(|&x| GL::try_from(x).unwrap()).collect();
                    let d = Rp64_256::hash_elements(&els);
                    let bytes = d.as_bytes();
                    bytes.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect::<Vec<_>>()
                })();
                
                let inputs_fp = if xs.is_empty() {
                    vec![]
                } else {
                    gl_alloc_u64_vec(cs.clone(), xs)?
                };
                let inputs_gl: Vec<GlVar> = inputs_fp.iter().map(|fp| GlVar(fp.clone())).collect();
                let got = rpo_hash_elements_light(cs.clone(), &inputs_gl, &RpoParamsGLLight::default())?;
                
                for i in 0..4 {
                    enforce_gl_eq(&got[i].0, &FpVar::constant(InnerFr::from(expect[i])))?;
                }
            }
            Ok(())
        }
    }

    TestCircuit.generate_constraints(cs.clone()).expect("Light RPO verification failed");
    assert!(cs.is_satisfied().unwrap(), "Light RPO gadget doesn't match Winterfell on test vectors!");
}

#[test]
fn test_rpo_matches_winterfell_merge() {
    // Test merge of two digests
    let left_input = vec![GL::new(1), GL::new(2), GL::new(3), GL::new(4)];
    let right_input = vec![GL::new(5), GL::new(6), GL::new(7), GL::new(8)];
    
    // Host-side hashes
    let left_digest = Rp64_256::hash_elements(&left_input);
    let right_digest = Rp64_256::hash_elements(&right_input);
    
    // Host-side merge
    let merged_host = Rp64_256::merge(&[left_digest, right_digest]);
    let merged_bytes = merged_host.as_bytes();
    
    let mut expected = [0u64; 4];
    for i in 0..4 {
        let chunk = &merged_bytes[i*8..(i+1)*8];
        expected[i] = u64::from_le_bytes([
            chunk[0], chunk[1], chunk[2], chunk[3],
            chunk[4], chunk[5], chunk[6], chunk[7],
        ]);
    }
    
    // Circuit-side with LIGHT RPO
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    let left_fp = gl_alloc_u64_vec(cs.clone(), &[1,2,3,4]).unwrap();
    let right_fp = gl_alloc_u64_vec(cs.clone(), &[5,6,7,8]).unwrap();
    
    let left_gl: Vec<GlVar> = left_fp.iter().map(|fp| GlVar(fp.clone())).collect();
    let right_gl: Vec<GlVar> = right_fp.iter().map(|fp| GlVar(fp.clone())).collect();
    
    // First hash both sides
    let left_digest = rpo_hash_elements_light(cs.clone(), &left_gl, &RpoParamsGLLight::default()).unwrap();
    let right_digest = rpo_hash_elements_light(cs.clone(), &right_gl, &RpoParamsGLLight::default()).unwrap();
    
    // Then merge
    let merged = rpo_merge_light(cs.clone(), &left_digest, &right_digest, &RpoParamsGLLight::default()).unwrap();
    
    // Verify
    for i in 0..4 {
        let expected_var = FpVar::constant(InnerFr::from(expected[i]));
        enforce_gl_eq(&merged[i].0, &expected_var).unwrap();
    }
    
    assert!(cs.is_satisfied().unwrap(), "Light RPO merge doesn't match Winterfell!");
}

