//! Deterministic Poseidon2-style params for Fr(BLS12-377), t=3, alpha=5,
//! RF=8, RP=56, derived from domain tag "PVUGC-Poseidon2-Fr377-t=3-v1".
//!
//! Exposes: POSEIDON377_PARAMS_T3_V1: PoseidonConfig<Fr377>

use ark_bls12_377::Fr as Fr377;
use ark_crypto_primitives::sponge::poseidon::PoseidonConfig;
use ark_ec::AdditiveGroup;
use ark_ff::{Field, PrimeField};
use ark_std::Zero;
use once_cell::sync::Lazy;
use sha2::{Digest, Sha256};

const WIDTH: usize = 3;
const RATE: usize = 2; // WIDTH - capacity
const CAP: usize = 1;
const RF: usize = 8;
const RP: usize = 56;
const ALPHA: u64 = 5;
const DOMAIN: &[u8] = b"PVUGC-Poseidon2-Fr377-t=3-v1";

fn fr_from_le32(bytes: [u8; 32]) -> Fr377 {
    Fr377::from_le_bytes_mod_order(&bytes)
}

fn prng_fr_stream(tag: &[u8], count: usize) -> Vec<Fr377> {
    let mut out = Vec::with_capacity(count);
    let mut ctr: u64 = 0;
    while out.len() < count {
        let mut h = Sha256::new();
        h.update(DOMAIN);
        h.update(&[0x00]);
        h.update(tag);
        h.update(&ctr.to_le_bytes());
        let d = h.finalize();
        let mut le = [0u8; 32];
        le.copy_from_slice(&d[..32]);
        let fe = fr_from_le32(le);
        if !fe.is_zero() {
            out.push(fe);
        }
        ctr = ctr.wrapping_add(1);
    }
    out
}

fn generate_mds_cauchy(width: usize) -> [[Fr377; WIDTH]; WIDTH] {
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
            let mut m = [[Fr377::ZERO; WIDTH]; WIDTH];
            for i in 0..width {
                for j in 0..width {
                    m[i][j] = (x[i] + y[j]).inverse().unwrap();
                }
            }
            return m;
        }
    }
    let mut id = [[Fr377::ZERO; WIDTH]; WIDTH];
    for i in 0..width {
        id[i][i] = Fr377::ONE;
    }
    id
}

fn generate_ark(width: usize, rf: usize, rp: usize) -> Vec<[Fr377; WIDTH]> {
    let rounds = rf + rp;
    let stream = prng_fr_stream(b"ark", rounds * width);
    stream
        .chunks_exact(width)
        .map(|c| [c[0], c[1], c[2]])
        .collect()
}

pub fn poseidon2_fr377_t3_v1() -> PoseidonConfig<Fr377> {
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
        capacity: CAP,
    }
}

pub static POSEIDON377_PARAMS_T3_V1: Lazy<PoseidonConfig<Fr377>> =
    Lazy::new(|| poseidon2_fr377_t3_v1());

#[cfg(test)]
mod tests {
    use super::*;
    use ark_crypto_primitives::sponge::poseidon::PoseidonSponge;
    use ark_crypto_primitives::sponge::CryptographicSponge;

    #[test]
    fn params_deterministic() {
        let a = poseidon2_fr377_t3_v1();
        let b = poseidon2_fr377_t3_v1();
        assert_eq!(a.full_rounds, b.full_rounds);
        assert_eq!(a.partial_rounds, b.partial_rounds);
        assert_eq!(a.alpha, b.alpha);
        assert_eq!(a.ark[0][0], b.ark[0][0]);
        assert_eq!(a.mds[0][0], b.mds[0][0]);
    }

    #[test]
    fn sponge_runs() {
        let cfg = poseidon2_fr377_t3_v1();
        let mut s = PoseidonSponge::<Fr377>::new(&cfg);
        s.absorb(&Fr377::from(123u64));
        s.absorb(&Fr377::from(456u64));
        let _out: Vec<Fr377> = s.squeeze_field_elements(1);
    }
}
