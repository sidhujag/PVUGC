//! RPO-256 Compatibility Test
//!
//! Verifies that our GL-native RPO gadget produces identical output to Winterfell's Rp64_256

use arkworks_groth16::gadgets::rpo_gl::{RpoParamsGL, rpo_hash_elements_gl};
use arkworks_groth16::gadgets::gl_range::gl_alloc_u64_vec;
use arkworks_groth16::inner_stark_full::enforce_gl_eq;
use arkworks_groth16::outer_compressed::InnerFr;
use ark_r1cs_std::fields::fp::FpVar;
use ark_r1cs_std::fields::FieldVar;
use ark_r1cs_std::R1CSVar;
use ark_relations::r1cs::ConstraintSystem;
use ark_ff::{BigInteger, PrimeField};
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
    
    // Circuit-side
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    let input_gl = gl_alloc_u64_vec(cs.clone(), &[1,2,3,4]).unwrap();
    let digest = rpo_hash_elements_gl(cs.clone(), &RpoParamsGL::default(), &input_gl).unwrap();
    
    // Check lane-wise equality
    assert_eq!(digest.len(), 4);
    
    for i in 0..4 {
        let val = digest[i].value().unwrap();
        let bytes = val.into_bigint().to_bytes_le();
        let mut v = 0u64;
        for (j, &b) in bytes.iter().enumerate().take(8) {
            v |= (b as u64) << (j * 8);
        }
    }
    
    for i in 0..4 {
        let expected_var = FpVar::constant(InnerFr::from(expected[i]));
        let matches = enforce_gl_eq(&digest[i], &expected_var);
        if matches.is_err() || !cs.is_satisfied().unwrap() {
            panic!("RPO mismatch at lane {}: expected {}, got circuit value", i, expected[i]);
        }
    }
    assert!(cs.is_satisfied().unwrap(), "RPO gadget doesn't match Winterfell on test vectors!");
}

#[test]
fn rpo_matches_winterfell_on_small_vectors() {
    use winter_crypto::hashers::Rp64_256;
    use winter_math::fields::f64::BaseElement as GL;
    use winter_crypto::Hasher;

    let host = |xs: &[u64]| {
        let els: Vec<GL> = xs.iter().map(|&x| GL::try_from(x).unwrap()).collect();
        let d = Rp64_256::hash_elements(&els);
        let bytes = d.as_bytes(); // 32 bytes = 4 lanes
        bytes.chunks(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect::<Vec<_>>()
    };

    let cs = ConstraintSystem::<InnerFr>::new_ref();
    let params = RpoParamsGL::default();

    // Test multiple input sizes to cover block boundaries
    for xs in [&[1u64][..], &[1,2], &[1,2,3,4], &[1,2,3,4,5,6,7,8], &[1,2,3,4,5,6,7,8,9]] {
        let expect = host(xs);
        
        let inputs = if xs.is_empty() {
            vec![]
        } else {
            gl_alloc_u64_vec(cs.clone(), xs).unwrap()
        };
        let got = rpo_hash_elements_gl(cs.clone(), &params, &inputs).unwrap();
        
        for i in 0..4 {
            let val = got[i].value().unwrap();
            let bytes = val.into_bigint().to_bytes_le();
            let mut v = 0u64;
            for (j, &b) in bytes.iter().enumerate().take(8) {
                v |= (b as u64) << (j * 8);
            }
        }
        
        for i in 0..4 {
            enforce_gl_eq(&got[i], &FpVar::constant(InnerFr::from(expect[i]))).unwrap();
        }
    }
    assert!(cs.is_satisfied().unwrap(), "RPO gadget doesn't match Winterfell on test vectors!");
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
    
    // Circuit-side
    use arkworks_groth16::gadgets::rpo_gl::rpo_merge_gl;
    let cs = ConstraintSystem::<InnerFr>::new_ref();
    
    let left_gl = gl_alloc_u64_vec(cs.clone(), &[1,2,3,4]).unwrap();
    let right_gl = gl_alloc_u64_vec(cs.clone(), &[5,6,7,8]).unwrap();
    
    // First hash both sides
    let left_digest = rpo_hash_elements_gl(cs.clone(), &RpoParamsGL::default(), &left_gl).unwrap();
    let right_digest = rpo_hash_elements_gl(cs.clone(), &RpoParamsGL::default(), &right_gl).unwrap();
    
    // Then merge
    let merged = rpo_merge_gl(cs.clone(), &RpoParamsGL::default(), &left_digest, &right_digest).unwrap();
    
    // Verify
    for i in 0..4 {
        let expected_var = FpVar::constant(InnerFr::from(expected[i]));
        enforce_gl_eq(&merged[i], &expected_var).unwrap();
    }
    
    assert!(cs.is_satisfied().unwrap(), "RPO merge doesn't match Winterfell!");
}

