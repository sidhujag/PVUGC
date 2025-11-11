//! Deterministic Poseidon2 parameters for BLS12-381 Fr, width=3.
//! Mirrors the Fr(377) construction used by the STARK verifier but targets
//! the Groth16 scalar field so we can reuse the same hash inside the VE circuit
//! and host-side DEM.

use ark_bls12_381::Fr;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_crypto_primitives::sponge::{poseidon::PoseidonSponge, CryptographicSponge};
use ark_ec::AdditiveGroup;
use ark_ff::{Field, PrimeField};
use ark_std::Zero;
use once_cell::sync::Lazy;
use sha2::{Digest, Sha256};

const WIDTH: usize = 3;
const RATE: usize = 2; // WIDTH - capacity
const CAPACITY: usize = 1;
const RF: usize = 8;
const RP: usize = 56;
const ALPHA: u64 = 5;
const DOMAIN: &[u8] = b"PVUGC-Poseidon2-Fr381-t=3-v1";

fn fr_from_le32(bytes: [u8; 32]) -> Fr {
    Fr::from_le_bytes_mod_order(&bytes)
}

fn prng_fr_stream(tag: &[u8], count: usize) -> Vec<Fr> {
    let mut out = Vec::with_capacity(count);
    let mut ctr: u64 = 0;
    while out.len() < count {
        let mut h = Sha256::new();
        h.update(DOMAIN);
        h.update(&[0x00]);
        h.update(tag);
        h.update(&ctr.to_le_bytes());
        let digest = h.finalize();
        let mut le = [0u8; 32];
        le.copy_from_slice(&digest[..32]);
        let fe = fr_from_le32(le);
        if !fe.is_zero() {
            out.push(fe);
        }
        ctr = ctr.wrapping_add(1);
    }
    out
}

fn generate_mds_cauchy(width: usize) -> [[Fr; WIDTH]; WIDTH] {
    let mut xs = prng_fr_stream(b"mds/x", width * 4);
    let mut ys = prng_fr_stream(b"mds/y", width * 4);
    xs.dedup();
    ys.dedup();
    for xi in 0..=(xs.len().saturating_sub(width)) {
        'try_y: for yi in 0..=(ys.len().saturating_sub(width)) {
            let x = &xs[xi..(xi + width)];
            let y = &ys[yi..(yi + width)];
            for i in 0..width {
                for j in 0..width {
                    if (x[i] + y[j]).is_zero() {
                        continue 'try_y;
                    }
                }
            }
            let mut m = [[Fr::ZERO; WIDTH]; WIDTH];
            for i in 0..width {
                for j in 0..width {
                    m[i][j] = (x[i] + y[j]).inverse().unwrap();
                }
            }
            return m;
        }
    }
    let mut identity = [[Fr::ZERO; WIDTH]; WIDTH];
    for i in 0..width {
        identity[i][i] = Fr::ONE;
    }
    identity
}

fn generate_ark(width: usize, rf: usize, rp: usize) -> Vec<[Fr; WIDTH]> {
    let rounds = rf + rp;
    let stream = prng_fr_stream(b"ark", rounds * width);
    stream
        .chunks_exact(width)
        .map(|chunk| [chunk[0], chunk[1], chunk[2]])
        .collect()
}

pub fn poseidon2_fr381_t3_v1() -> PoseidonConfig<Fr> {
    let mds = generate_mds_cauchy(WIDTH);
    let ark = generate_ark(WIDTH, RF, RP)
        .into_iter()
        .map(|row| row.to_vec())
        .collect::<Vec<_>>();
    PoseidonConfig {
        full_rounds: RF,
        partial_rounds: RP,
        alpha: ALPHA,
        mds: mds.into_iter().map(|row| row.to_vec()).collect(),
        ark,
        rate: RATE,
        capacity: CAPACITY,
    }
}

pub static POSEIDON381_PARAMS_T3_V1: Lazy<PoseidonConfig<Fr>> =
    Lazy::new(|| poseidon2_fr381_t3_v1());

/// Absorb bytes into a native Poseidon sponge using little-endian base-256 packing.
pub fn absorb_bytes_native_fr(sponge: &mut PoseidonSponge<Fr>, bytes: &[u8]) {
    if bytes.is_empty() {
        sponge.absorb(&Fr::from(0u64));
        return;
    }
    for chunk in bytes.chunks(8) {
        let mut acc = 0u64;
        for (i, byte) in chunk.iter().enumerate() {
            acc |= (*byte as u64) << (8 * i);
        }
        sponge.absorb(&Fr::from(acc));
    }
}

#[cfg(feature = "r1cs")]
use ark_crypto_primitives::sponge::constraints::CryptographicSpongeVar;
#[cfg(feature = "r1cs")]
use ark_crypto_primitives::sponge::poseidon::constraints::PoseidonSpongeVar;
#[cfg(feature = "r1cs")]
use ark_r1cs_std::{fields::fp::FpVar, fields::FieldVar, uint8::UInt8};
#[cfg(feature = "r1cs")]
use ark_relations::r1cs::SynthesisError;

#[cfg(feature = "r1cs")]
/// Absorb bytes into a Poseidon sponge gadget using the same base-256 packing.
pub fn absorb_bytes_var_fr(
    sponge: &mut PoseidonSpongeVar<Fr>,
    bytes: &[UInt8<Fr>],
) -> Result<(), SynthesisError> {
    if bytes.is_empty() {
        sponge.absorb(&FpVar::<Fr>::constant(Fr::from(0u64)))?;
        return Ok(());
    }
    for chunk in bytes.chunks(8) {
        let fe = bytes_to_field_le(chunk)?;
        sponge.absorb(&fe)?;
    }
    Ok(())
}

#[cfg(feature = "r1cs")]
fn bytes_to_field_le(bytes: &[UInt8<Fr>]) -> Result<FpVar<Fr>, SynthesisError> {
    if bytes.is_empty() {
        return Ok(FpVar::<Fr>::constant(Fr::from(0u64)));
    }
    let base = FpVar::<Fr>::constant(Fr::from(256u64));
    let mut acc = FpVar::<Fr>::constant(Fr::from(0u64));
    let mut pow = FpVar::<Fr>::constant(Fr::from(1u64));
    for byte in bytes {
        acc = &acc + &(&byte.to_fp()? * &pow);
        pow = &pow * &base;
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;

    #[test]
    fn params_are_deterministic() {
        let a = poseidon2_fr381_t3_v1();
        let b = poseidon2_fr381_t3_v1();
        assert_eq!(a.full_rounds, b.full_rounds);
        assert_eq!(a.partial_rounds, b.partial_rounds);
        assert_eq!(a.alpha, b.alpha);
        assert_eq!(a.ark[0][0], b.ark[0][0]);
        assert_eq!(a.mds[0][0], b.mds[0][0]);
    }

    #[test]
    fn sponge_runs() {
        let cfg = poseidon2_fr381_t3_v1();
        let mut sponge = PoseidonSponge::<Fr>::new(&cfg);
        sponge.absorb(&Fr::from(123u64));
        sponge.absorb(&Fr::from(456u64));
        let _: Vec<Fr> = sponge.squeeze_field_elements(1);
    }
}
