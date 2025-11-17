//! Groth16-based verifiable encryption for adaptor shares.
//!
//! The circuit proves, in zero knowledge, that a published ciphertext/tag pair
//! was produced with the PVUGC DEM using the same pairing-derived key
//! `K = R^ρ`, without revealing either `K` or the decrypted adaptor scalar.
//! Public inputs exposed by the proof are:
//!   * `h_k = Poseidon("PVUGC/VE/hk" || K_bytes)`
//!   * `ad_digest = Poseidon("PVUGC/AD_CORE" || len || ad_core_bytes)`
//!   * `ciphertext` bytes
//!   * `tau` (DEM tag)
//!   * `h_m = Poseidon("PVUGC/VE/hm" || plaintext)`
//!
//! The adaptor Schnorr PoK must bind to `h_m` to ensure the plaintext matches
//! the published adaptor commitment `T_i = m·G`.

use crate::error::Error;
use crate::{
    api::enforce_public_inputs_are_outputs,
    ct::{ad_core_digest, compute_key_commitment_tag, DemP2, DEM_PROFILE_ID},
    poseidon_fr381_t3::{absorb_bytes_native_fr, absorb_bytes_var_fr, POSEIDON381_PARAMS_T3_V1},
    secp256k1::{decompress_secp_point, enforce_secp_fixed_base_mul, point_to_field_elements},
};
use ark_bls12_381::{Bls12_381, Fr};
use ark_ec::AffineRepr;
use ark_crypto_primitives::sponge::{
    constraints::CryptographicSpongeVar,
    poseidon::{constraints::PoseidonSpongeVar, PoseidonSponge as PoseidonSpongeNative},
    CryptographicSponge,
};
use ark_ff::ToConstraintField;
use ark_groth16::{prepare_verifying_key, Groth16, PreparedVerifyingKey, Proof, ProvingKey};
use ark_r1cs_std::{eq::EqGadget, uint8::UInt8};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, SynthesisError};
use ark_secp256k1::Affine as SecpAffine;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_std::One;
use core::convert::TryInto;
use core::ops::BitXor;
use once_cell::sync::Lazy;
use rand_core::OsRng;
use std::sync::Arc;

const DEM_KEYSTREAM_DOMAIN: &[u8] = b"PVUGC/DEM/keystream";
const DEM_TAG_DOMAIN: &[u8] = b"PVUGC/DEM/tag";
const HK_DOMAIN: &[u8] = b"PVUGC/VE/hk";
const HM_DOMAIN: &[u8] = b"PVUGC/VE/hm";

fn hash_with_domain(domain: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut sponge = PoseidonSpongeNative::<Fr>::new(&POSEIDON381_PARAMS_T3_V1);
    absorb_bytes_native_fr(&mut sponge, domain);
    absorb_bytes_native_fr(&mut sponge, payload);
    sponge
        .squeeze_bytes(32)
        .try_into()
        .expect("poseidon hash length")
}

fn gt_serialized_len() -> usize {
    use ark_ec::pairing::Pairing;
    let one = <Bls12_381 as Pairing>::TargetField::one();
    crate::ct::serialize_gt::<Bls12_381>(&one).len()
}

struct AdaptorVeKeys {
    proving_key: Arc<ProvingKey<Bls12_381>>,
    prepared_vk: PreparedVerifyingKey<Bls12_381>,
    key_len: usize,
    ct_len: usize,
}

static VE_KEYS: Lazy<AdaptorVeKeys> = Lazy::new(|| {
    use ark_std::rand::{rngs::StdRng, SeedableRng};

    let key_len = gt_serialized_len();
    // Adaptor shares are 32-byte secp256k1 scalars.
    let ct_len = 32usize;
    let circuit = AdaptorVeCircuit::blank(key_len, ct_len);
    let mut rng = StdRng::seed_from_u64(0x4156_4145_4352_5950); // "AVAECRYP" in ASCII
    let pk = Groth16::<Bls12_381>::generate_random_parameters_with_reduction(circuit, &mut rng)
        .expect("failed to set up adaptor VE circuit");
    let pvk = prepare_verifying_key(&pk.vk);
    AdaptorVeKeys {
        proving_key: Arc::new(pk),
        prepared_vk: pvk,
        key_len,
        ct_len,
    }
});

/// Groth16 proof that the ciphertext/tag encrypts the adaptor scalar.
#[derive(Clone, Debug, CanonicalSerialize, CanonicalDeserialize)]
pub struct AdaptorVeProof {
    pub proof: Proof<Bls12_381>,
    pub h_k: [u8; 32],
    pub h_m: [u8; 32],
}

impl AdaptorVeProof {
    /// Create a dummy proof for testing (skips expensive VE circuit)
    pub fn dummy() -> Self {
        use ark_ec::AffineRepr;
        Self {
            proof: Proof {
                a: <Bls12_381 as ark_ec::pairing::Pairing>::G1Affine::generator(),
                b: <Bls12_381 as ark_ec::pairing::Pairing>::G2Affine::generator(),
                c: <Bls12_381 as ark_ec::pairing::Pairing>::G1Affine::generator(),
            },
            h_k: [0u8; 32],
            h_m: [0u8; 32],
        }
    }
}

struct AdaptorVeCircuit {
    key_bytes: Option<Vec<u8>>,
    ciphertext: Option<Vec<u8>>,
    ad_digest: Option<[u8; 32]>,
    tag: Option<[u8; 32]>,
    h_k: Option<[u8; 32]>,
    h_m: Option<[u8; 32]>,
    key_len: usize,
    ct_len: usize,
    t_point: SecpAffine,
}

impl AdaptorVeCircuit {
    fn blank(key_len: usize, ct_len: usize) -> Self {
        // Use generator instead of identity for blank circuit to avoid subgroup check failure
        Self {
            key_bytes: None,
            ciphertext: None,
            ad_digest: None,
            tag: None,
            h_k: None,
            h_m: None,
            key_len,
            ct_len,
            t_point: SecpAffine::generator(),
        }
    }

    fn new(
        key_bytes: Vec<u8>,
        ciphertext: Vec<u8>,
        ad_digest: [u8; 32],
        tag: [u8; 32],
        h_k: [u8; 32],
        h_m: [u8; 32],
        key_len: usize,
        ct_len: usize,
        t_point: SecpAffine,
    ) -> Self {
        Self {
            key_bytes: Some(key_bytes),
            ciphertext: Some(ciphertext),
            ad_digest: Some(ad_digest),
            tag: Some(tag),
            h_k: Some(h_k),
            h_m: Some(h_m),
            key_len,
            ct_len,
            t_point,
        }
    }
}

impl ConstraintSynthesizer<Fr> for AdaptorVeCircuit {
    fn generate_constraints(self, cs: ConstraintSystemRef<Fr>) -> Result<(), SynthesisError> {
        let key_len = self.key_len;
        let ct_len = self.ct_len;

        let key_bytes = self.key_bytes.unwrap_or_else(|| vec![0u8; key_len]);
        let ciphertext = self.ciphertext.unwrap_or_else(|| vec![0u8; ct_len]);
        let ad_digest = self.ad_digest.unwrap_or([0u8; 32]);
        let tag = self.tag.unwrap_or([0u8; 32]);
        let h_k = self.h_k.unwrap_or([0u8; 32]);
        let h_m = self.h_m.unwrap_or([0u8; 32]);

        assert_eq!(key_bytes.len(), key_len);
        assert_eq!(ciphertext.len(), ct_len);

        // Public inputs (as byte arrays).
        let h_k_input = UInt8::new_input_vec(cs.clone(), &h_k)?;
        let ad_digest_input = UInt8::new_input_vec(cs.clone(), &ad_digest)?;
        let ct_input = UInt8::new_input_vec(cs.clone(), &ciphertext)?;
        let tag_input = UInt8::new_input_vec(cs.clone(), &tag)?;
        let h_m_input = UInt8::new_input_vec(cs.clone(), &h_m)?;

        // Witness: key bytes
        let key_var = UInt8::new_witness_vec(cs.clone(), &key_bytes)?;

        // 1. h_k consistency
        let hk_domain = constants_to_uint8(HK_DOMAIN);
        let computed_h_k = poseidon_var_digest(cs.clone(), &hk_domain, &key_var)?;
        enforce_bytes_equal(&computed_h_k, &h_k_input)?;

        // 2. Derive keystream blocks and decrypt
        let mut plaintext = Vec::with_capacity(ct_len);
        if ct_len > 0 {
            let keystream_domain = constants_to_uint8(DEM_KEYSTREAM_DOMAIN);
            let mut sponge = new_poseidon_sponge_var(cs.clone())?;
            poseidon_var_absorb_bytes(&mut sponge, &keystream_domain)?;
            poseidon_var_absorb_bytes(&mut sponge, &key_var)?;
            poseidon_var_absorb_bytes(&mut sponge, &ad_digest_input)?;
            let counter_zero = constants_to_uint8(&0u32.to_le_bytes());
            poseidon_var_absorb_bytes(&mut sponge, &counter_zero)?;
            let ks_block = sponge.squeeze_bytes(ct_len)?;
            for (i, ks_byte) in ks_block.into_iter().enumerate() {
                let pt_byte = ct_input[i].clone().bitxor(&ks_byte);
                plaintext.push(pt_byte);
            }
        }

        // 3. Tag consistency
        let mut tag_sponge = new_poseidon_sponge_var(cs.clone())?;
        let tag_domain = constants_to_uint8(DEM_TAG_DOMAIN);
        poseidon_var_absorb_bytes(&mut tag_sponge, &tag_domain)?;
        poseidon_var_absorb_bytes(&mut tag_sponge, &key_var)?;
        poseidon_var_absorb_bytes(&mut tag_sponge, &ad_digest_input)?;
        poseidon_var_absorb_bytes(&mut tag_sponge, &ct_input)?;
        let computed_tag = tag_sponge.squeeze_bytes(32)?;
        enforce_bytes_equal(&computed_tag, &tag_input)?;

        // 4. h_m derived from plaintext
        let mut hm_sponge = new_poseidon_sponge_var(cs.clone())?;
        let hm_domain = constants_to_uint8(HM_DOMAIN);
        poseidon_var_absorb_bytes(&mut hm_sponge, &hm_domain)?;
        poseidon_var_absorb_bytes(&mut hm_sponge, &plaintext)?;
        let computed_h_m = hm_sponge.squeeze_bytes(32)?;
        enforce_bytes_equal(&computed_h_m, &h_m_input)?;

        let adaptor_scalar: [UInt8<Fr>; 32] = plaintext
            .clone()
            .try_into()
            .map_err(|_| SynthesisError::Unsatisfiable)?;
        enforce_secp_fixed_base_mul(cs.clone(), &adaptor_scalar, &self.t_point, None)?;

        enforce_public_inputs_are_outputs(cs)?;
        Ok(())
    }
}

fn constants_to_uint8(bytes: &[u8]) -> Vec<UInt8<Fr>> {
    bytes.iter().map(|b| UInt8::constant(*b)).collect()
}

fn enforce_bytes_equal(a: &[UInt8<Fr>], b: &[UInt8<Fr>]) -> Result<(), SynthesisError> {
    for (lhs, rhs) in a.iter().zip(b.iter()) {
        lhs.enforce_equal(rhs)?;
    }
    Ok(())
}

fn new_poseidon_sponge_var(
    cs: ConstraintSystemRef<Fr>,
) -> Result<PoseidonSpongeVar<Fr>, SynthesisError> {
    Ok(PoseidonSpongeVar::new(cs, &POSEIDON381_PARAMS_T3_V1))
}

fn poseidon_var_absorb_bytes(
    sponge: &mut PoseidonSpongeVar<Fr>,
    bytes: &[UInt8<Fr>],
) -> Result<(), SynthesisError> {
    absorb_bytes_var_fr(sponge, bytes)
}

fn poseidon_var_digest(
    cs: ConstraintSystemRef<Fr>,
    domain: &[UInt8<Fr>],
    data: &[UInt8<Fr>],
) -> Result<Vec<UInt8<Fr>>, SynthesisError> {
    let mut sponge = new_poseidon_sponge_var(cs)?;
    poseidon_var_absorb_bytes(&mut sponge, domain)?;
    poseidon_var_absorb_bytes(&mut sponge, data)?;
    sponge.squeeze_bytes(32)
}

/// Validate GT element bytes for security
fn validate_gt_element(k_bytes: &[u8]) -> Result<(), Error> {
    use ark_bls12_381::{Fq12, Fr};
    use ark_ff::{Field, One, PrimeField, Zero};
    use ark_serialize::CanonicalDeserialize;

    // 1. Deserialize to ensure valid Fq12 element
    let element = Fq12::deserialize_compressed(k_bytes)
        .map_err(|_| Error::Crypto("Invalid GT element: deserialization failed".into()))?;

    // 2. Reject additive zero (not a valid GT element for encryption)
    if element.is_zero() {
        return Err(Error::Crypto("GT element cannot be zero".into()));
    }

    // 3. Reject multiplicative identity (encryption would become public)
    if element.is_one() {
        return Err(Error::Crypto("GT element cannot be identity".into()));
    }

    // 4. Subgroup check: verify element^r == 1 where r is the scalar field order
    // Note: Technically redundant since keys from honest pairings are guaranteed
    // in-subgroup, but provides fail-fast for honest operators detecting bugs
    let subgroup_check = element.pow(Fr::MODULUS.into());
    if subgroup_check != Fq12::one() {
        return Err(Error::Crypto(
            "GT element must be in the prime-order subgroup".into(),
        ));
    }

    Ok(())
}

/// Produce an adaptor VE proof.
pub fn prove_adaptor_ve(
    k_bytes: &[u8],
    ad_core: &[u8],
    ciphertext: &[u8],
    tau: &[u8],
    plaintext: &[u8],
) -> Result<AdaptorVeProof, Error> {
    let keys = &*VE_KEYS;
    if k_bytes.len() != keys.key_len {
        return Err(Error::Crypto(
            "invalid key length for adaptor VE proof".into(),
        ));
    }
    if ciphertext.len() != keys.ct_len || plaintext.len() != keys.ct_len || tau.len() != 32 {
        return Err(Error::Crypto(
            "invalid ciphertext or tag length for adaptor VE proof".into(),
        ));
    }

    // Validate GT element for honest-operator fail-fast (NOT a security boundary)
    // Real security: tag verification at decapsulation time prevents wrong-key attacks
    validate_gt_element(k_bytes)?;

    let ad_digest = ad_core_digest(ad_core);
    let t_point = extract_t_from_ad_core(ad_core)?;
    let dem = DemP2::new(k_bytes, ad_core);
    if dem.encrypt(plaintext) != ciphertext {
        return Err(Error::Crypto(
            "plaintext does not match ciphertext under provided key".into(),
        ));
    }
    if compute_key_commitment_tag(k_bytes, ad_core, ciphertext) != tau {
        return Err(Error::Crypto("tag does not match ciphertext/key".into()));
    }

    let h_k = hash_with_domain(HK_DOMAIN, k_bytes);
    let h_m = hash_with_domain(HM_DOMAIN, plaintext);

    let circuit = AdaptorVeCircuit::new(
        k_bytes.to_vec(),
        ciphertext.to_vec(),
        ad_digest,
        to_array32(tau),
        h_k,
        h_m,
        keys.key_len,
        keys.ct_len,
        t_point,
    );

    let proof = Groth16::<Bls12_381>::create_random_proof_with_reduction(
        circuit,
        &keys.proving_key,
        &mut OsRng,
    )
    .map_err(|e| Error::Crypto(format!("failed to prove adaptor VE: {e}")))?;

    let proof_obj = AdaptorVeProof { proof, h_k, h_m };
    Ok(proof_obj)
}

/// Verify an adaptor VE proof against the published data.
pub fn verify_adaptor_ve(
    proof: &AdaptorVeProof,
    ad_core: &[u8],
    ciphertext: &[u8],
    tau: &[u8],
) -> bool {
    let keys = &*VE_KEYS;
    if ciphertext.len() != keys.ct_len || tau.len() != 32 {
        return false;
    }
    let t_point = match extract_t_from_ad_core(ad_core) {
        Ok(p) => p,
        Err(_) => return false,
    };
    let ad_digest = ad_core_digest(ad_core);
    let public_inputs = assemble_public_inputs(
        &proof.h_k, &ad_digest, ciphertext, tau, &proof.h_m, &t_point,
    );
    debug_assert_eq!(
        public_inputs.len() + 1,
        keys.prepared_vk.vk.gamma_abc_g1.len(),
        "public input length mismatch"
    );
    let prepared_inputs =
        match Groth16::<Bls12_381>::prepare_inputs(&keys.prepared_vk, &public_inputs) {
            Ok(inputs) => inputs,
            Err(_) => return false,
        };
    Groth16::<Bls12_381>::verify_proof_with_prepared_inputs(
        &keys.prepared_vk,
        &proof.proof,
        &prepared_inputs,
    )
    .unwrap_or(false)
}

fn to_array32(bytes: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    out.copy_from_slice(&bytes[..32]);
    out
}

fn assemble_public_inputs(
    h_k: &[u8; 32],
    ad_digest: &[u8; 32],
    ciphertext: &[u8],
    tau: &[u8],
    h_m: &[u8; 32],
    t_point: &SecpAffine,
) -> Vec<Fr> {
    let mut inputs = Vec::new();
    inputs.extend(bytes_to_field_elements(h_k));
    inputs.extend(bytes_to_field_elements(ad_digest));
    inputs.extend(bytes_to_field_elements(ciphertext));
    inputs.extend(bytes_to_field_elements(tau));
    inputs.extend(bytes_to_field_elements(h_m));
    inputs.extend(point_to_field_elements::<Fr>(t_point));
    inputs
}

fn bytes_to_field_elements(bytes: &[u8]) -> Vec<Fr> {
    ToConstraintField::<Fr>::to_field_elements(bytes).expect("to_field_elements failed")
}

fn extract_t_from_ad_core(ad_core: &[u8]) -> Result<SecpAffine, Error> {
    fn read_slice<'a>(
        ad_core: &'a [u8],
        cursor: &mut usize,
        len: usize,
        label: &str,
    ) -> Result<&'a [u8], Error> {
        if *cursor + len > ad_core.len() {
            return Err(Error::Crypto(format!(
                "AD_core too short reading {}",
                label
            )));
        }
        let slice = &ad_core[*cursor..*cursor + len];
        *cursor += len;
        Ok(slice)
    }

    fn read_len(ad_core: &[u8], cursor: &mut usize, label: &str) -> Result<usize, Error> {
        let bytes = read_slice(ad_core, cursor, 4, label)?;
        let arr: [u8; 4] = bytes.try_into().expect("len slice");
        let len = u32::from_le_bytes(arr) as usize;
        if *cursor + len > ad_core.len() {
            return Err(Error::Crypto(format!("AD_core {} length overflow", label)));
        }
        Ok(len)
    }

    let mut cursor = 0usize;
    let profile = read_slice(ad_core, &mut cursor, DEM_PROFILE_ID.len(), "profile")?;
    if profile != DEM_PROFILE_ID {
        return Err(Error::Crypto("AD_core profile mismatch".into()));
    }

    read_slice(ad_core, &mut cursor, 32, "vk_hash")?;
    read_slice(ad_core, &mut cursor, 32, "x_hash")?;
    read_slice(ad_core, &mut cursor, 32, "ctx_hash")?;
    read_slice(ad_core, &mut cursor, 32, "tapleaf_hash")?;
    read_slice(ad_core, &mut cursor, 1, "tapleaf_version")?;
    let txid_len = read_len(ad_core, &mut cursor, "txid_template")?;
    read_slice(ad_core, &mut cursor, txid_len, "txid_template_bytes")?;
    let path_len = read_len(ad_core, &mut cursor, "path_tag")?;
    read_slice(ad_core, &mut cursor, path_len, "path_tag_bytes")?;
    read_slice(ad_core, &mut cursor, 4, "share_index")?;
    let t_i_len = read_len(ad_core, &mut cursor, "t_i")?;
    let t_i_bytes = read_slice(ad_core, &mut cursor, t_i_len, "t_i_bytes")?.to_vec();
    let t_agg_len = read_len(ad_core, &mut cursor, "t_aggregate")?;
    read_slice(ad_core, &mut cursor, t_agg_len, "t_aggregate_bytes")?;
    let armed_bases_len = read_len(ad_core, &mut cursor, "armed_bases")?;
    read_slice(ad_core, &mut cursor, armed_bases_len, "armed_bases_bytes")?;
    let armed_delta_len = read_len(ad_core, &mut cursor, "armed_delta")?;
    read_slice(ad_core, &mut cursor, armed_delta_len, "armed_delta_bytes")?;
    read_slice(ad_core, &mut cursor, 32, "gs_instance_digest")?;

    if cursor != ad_core.len() {
        return Err(Error::Crypto("AD_core trailing bytes".into()));
    }

    decompress_secp_point(&t_i_bytes)
        .ok_or_else(|| Error::Crypto("invalid secp adaptor commitment in AD_core".into()))
}

#[cfg(test)]
mod tests {
    use super::{AdaptorVeCircuit, *};
    use crate::ct::AdCore;
    use crate::secp256k1::{compress_secp_point, scalar_bytes_to_point};
    use ark_relations::r1cs::ConstraintSystem;

    #[test]
    fn adaptor_ve_roundtrip() {
        let key_bytes = vec![1u8; super::gt_serialized_len()];
        let plaintext = vec![3u8; 32];
        let mut scalar_array = [0u8; 32];
        scalar_array.copy_from_slice(&plaintext);
        let t_point = scalar_bytes_to_point(&scalar_array);
        let t_bytes = compress_secp_point(&t_point);
        let ad_core = AdCore::new(
            [2u8; 32],
            [3u8; 32],
            [4u8; 32],
            [5u8; 32],
            0xc0,
            vec![6u8; 10],
            "compute",
            0,
            t_bytes.clone(),
            t_bytes.clone(),
            vec![7u8; 33],
            vec![8u8; 33],
            [9u8; 32],
        )
        .serialize();
        let dem = DemP2::new(&key_bytes, &ad_core);
        let ciphertext = dem.encrypt(&plaintext);
        let tau = compute_key_commitment_tag(&key_bytes, &ad_core, &ciphertext);

        let proof = prove_adaptor_ve(&key_bytes, &ad_core, &ciphertext, &tau, &plaintext).unwrap();
        assert!(verify_adaptor_ve(&proof, &ad_core, &ciphertext, &tau));

        // Change ciphertext should fail
        let mut bad_ct = ciphertext.clone();
        bad_ct[0] ^= 1;
        assert!(!verify_adaptor_ve(&proof, &ad_core, &bad_ct, &tau));
    }

    #[test]
    #[ignore = "heavy circuit generation; run manually"]
    fn adaptor_ve_constraint_count() {
        let key_len = super::gt_serialized_len();
        let ct_len = super::VE_KEYS.ct_len;
        let circuit = AdaptorVeCircuit::blank(key_len, ct_len);
        let cs = ConstraintSystem::<Fr>::new_ref();
        circuit.generate_constraints(cs.clone()).unwrap();
        let num_constraints = cs.num_constraints();
        println!("Adaptor VE circuit constraints: {}", num_constraints);
        assert!(num_constraints > 0);
    }
}
