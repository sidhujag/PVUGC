//! Reduced-parameter executable of Praxis Figures 6–7 for (x − y)² = 1,
//! with x,y Boolean. The public capsule contains group elements, the form
//! matrix and a masked 100-bit message. This small research profile has no
//! security-level claim.
//!
//! N=2, n_c=1, F_max=1, ν=2, D=6, d_R=2, k=1, n=4, K1=1, K2=2,
//! J=J'=1. The unseeded uniform matrix and independent small entries of r
//! follow §5.1. Search is exhaustive at this range. Encapsulate encrypts a
//! uniform 100-bit seed with the Figure 6 XOR mask, then expands the seed for
//! the DEM. The concrete hash domains and wire encoding are prototype-specific.

use ark_bn254::{Bn254, Fr, G1Affine, G1Projective, G2Affine, G2Projective};
use ark_ec::{
    pairing::{Pairing, PairingOutput},
    CurveGroup, PrimeGroup,
};
use ark_ff::{BigInteger, FftField, Field, One, PrimeField, UniformRand, Zero};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, SerializationError};
use rand::{CryptoRng, Rng, RngCore};
use sha2::{Digest, Sha256};
use std::array::from_fn;
use zeroize::Zeroizing;

const G: u64 = 8;
const D: usize = 6;
const LEGS: usize = 6;
type GT = PairingOutput<Bn254>;
type Poly = Vec<Fr>;
type Seed100 = [u8; 13];
const LAST_BYTE_MASK: u8 = 0xf0;

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct Capsule {
    // One row, two columns in F_q[Y]/(Y²+1), public by construction.
    matrix: [[Fr; 2]; 2],
    left: [[G1Affine; 2]; 3],
    quotient: [G1Affine; D],
    remainder: G1Affine,
    cancel: [G1Affine; 3],
    right: Right,
    alpha_right: Right,
    alpha_key: GT,
    masked_seed: Seed100,
}

impl Capsule {
    // Four Frs, 16 G1s, 196 G2s, one GT, and one 100-bit masked message.
    pub const WIRE_BYTES: usize = 4 * 32 + 16 * 32 + 196 * 64 + 384 + 13;

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(Self::WIRE_BYTES);
        self.serialize_compressed(&mut bytes)
            .expect("serializing to a Vec");
        bytes
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, SerializationError> {
        if bytes.len() != Self::WIRE_BYTES {
            return Err(SerializationError::InvalidData);
        }
        // Checked arkworks decoding verifies subgroup membership. Re-encoding
        // also enforces a unique byte string for the commitment to this capsule.
        let capsule = Self::deserialize_compressed(bytes)?;
        if capsule.masked_seed[12] & !LAST_BYTE_MASK != 0 || capsule.to_bytes() != bytes {
            return Err(SerializationError::InvalidData);
        }
        Ok(capsule)
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
struct Right {
    factor: [[[G2Affine; 2]; 3]; LEGS],
    search: [G2Affine; LEGS],
    quotient: [G2Affine; LEGS],
    remainder: [G2Affine; LEGS],
    tie: [[G2Affine; 3]; 3],
    cross_plus: [[G2Affine; 7]; 3],
    cross_minus: [[G2Affine; 7]; 2],
}

fn fr(n: u64) -> Fr {
    Fr::from(n)
}

fn product(a: &[Fr], b: &[Fr]) -> Poly {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut result = vec![Fr::zero(); a.len() + b.len() - 1];
    for (i, v) in a.iter().enumerate() {
        for (j, u) in b.iter().enumerate() {
            result[i + j] += *v * u;
        }
    }
    result
}

fn subtract(a: &[Fr], b: &[Fr]) -> Poly {
    (0..a.len().max(b.len()))
        .map(|i| coeff(a, i) - coeff(b, i))
        .collect()
}

fn coeff(a: &[Fr], i: usize) -> Fr {
    a.get(i).copied().unwrap_or_default()
}

fn evaluate(a: &[Fr], x: Fr) -> Fr {
    a.iter().rev().fold(Fr::zero(), |value, &c| value * x + c)
}

fn substitute(a: &[Fr], scale: Fr) -> Poly {
    let mut power = Fr::one();
    a.iter()
        .map(|c| {
            let term = *c * power;
            power *= scale;
            term
        })
        .collect()
}

fn div_rem(a: &[Fr], monic: &[Fr]) -> (Poly, Poly) {
    debug_assert_eq!(monic.last(), Some(&Fr::one()));
    let mut rem = a.to_vec();
    let mut quo = vec![Fr::zero(); (a.len() + 1).saturating_sub(monic.len())];
    for i in (0..quo.len()).rev() {
        quo[i] = rem[i + monic.len() - 1];
        for (j, &m) in monic.iter().enumerate() {
            rem[i + j] -= quo[i] * m;
        }
    }
    rem.truncate(monic.len() - 1);
    (quo, rem)
}

fn exact(a: &[Fr], monic: &[Fr]) -> Option<Poly> {
    let (quo, rem) = div_rem(a, monic);
    rem.iter().all(Zero::is_zero).then_some(quo)
}

fn vanishing(points: &[Fr]) -> Poly {
    points
        .iter()
        .fold(vec![Fr::one()], |acc, &x| product(&acc, &[-x, Fr::one()]))
}

fn interpolate(points: &[Fr], values: &[Fr]) -> Poly {
    let mut poly = vec![Fr::zero(); points.len()];
    for (i, &value) in values.iter().enumerate() {
        if value.is_zero() {
            continue;
        }
        let others: Vec<_> = points
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, p)| *p)
            .collect();
        let basis = vanishing(&others);
        let scale = value / evaluate(&basis, points[i]);
        for (dst, c) in poly.iter_mut().zip(basis) {
            *dst += scale * c;
        }
    }
    poly
}

struct Qap {
    points: [Fr; D],
    a: [Poly; 3],
    b: [Poly; 3],
    z0: Poly,
    z: Poly,
    full_z: Poly,
    corner: Poly,
}

impl Qap {
    fn new() -> Self {
        // d0,d1,d2,rho and the disjoint coset {+1,-1}.
        let points = [fr(2), fr(3), fr(4), fr(5), Fr::one(), -Fr::one()];
        let z0 = vanishing(&points[..4]);
        let z = vanishing(&[points[0], points[1], points[2], points[4], points[5]]);
        let full_z = product(&z, &[-points[3], Fr::one()]);
        let zp = evaluate(&z0, points[4]);
        let zm = evaluate(&z0, points[5]);
        let one = Fr::one();
        let zero = Fr::zero();
        let a_values = [
            [zero, -one, -one, one, zero, zm],
            [zero, one, zero, zero, zp, zero],
            [zero, zero, one, zero, -zp, zero],
        ];
        let b_values = [
            [one, zero, zero, one, zero, -one],
            [zero, one, zero, zero, one, zero],
            [zero, zero, one, zero, -one, zero],
        ];
        let a = a_values.map(|v| interpolate(&points, &v));
        let b = b_values.map(|v| interpolate(&points, &v));
        let corner = interpolate(&points, &[zero, zero, zero, one, zero, zero]);
        Self {
            points,
            a,
            b,
            z0,
            z,
            full_z,
            corner,
        }
    }

    fn openings(&self, w: &[Fr; 3]) -> Option<(Poly, Poly, Fr)> {
        let combination = |polys: &[Poly; 3]| -> Poly {
            (0..D)
                .map(|k| (0..3).map(|j| w[j] * polys[j][k]).sum())
                .collect()
        };
        let p = product(&combination(&self.a), &combination(&self.b));
        let coset_values: Vec<_> = self.points[4..]
            .iter()
            .map(|&x| evaluate(&p, x) / evaluate(&self.z0, x))
            .collect();
        let rem = interpolate(&self.points[4..], &coset_values);
        if !rem[0].is_zero() {
            return None;
        } // Exponents divisible by ν are forbidden.
        let shifted = subtract(&p, &product(&self.z0, &rem));
        Some((
            exact(&subtract(&shifted, &self.corner), &self.full_z)?,
            exact(&shifted, &self.z)?,
            rem[1],
        ))
    }
}

fn extension() -> (Fr, Fr, [Fr; 5]) {
    let c0 = Fr::GENERATOR;
    let mut exponent = Fr::MODULUS_MINUS_ONE_DIV_TWO;
    exponent.div2();
    let omega = c0.pow(exponent);
    debug_assert_eq!(omega.square(), -Fr::one());
    (
        c0,
        omega,
        [-c0, Fr::zero(), Fr::zero(), Fr::zero(), Fr::one()],
    )
}

// Definition 5.1 with d_R=2; columns multiply 1 and x+yY modulo Y²+1.
fn form_columns(m: &[[Fr; 2]; 2]) -> [[Fr; 4]; 3] {
    [
        [Fr::one(), Fr::zero(), m[0][0], m[0][1]],
        [Fr::zero(), Fr::zero(), m[1][0], m[1][1]],
        [Fr::zero(), Fr::zero(), -m[1][1], m[1][0]],
    ]
}

// K1=1: each of six legs serves one copy. Index 0 is the key copy.
const EXP: [usize; LEGS] = [0, 1, 0, 2, 3, 2];
const KIND: [usize; LEGS] = [0, 1, 2, 0, 1, 2];

struct Ties {
    weights: [Fr; LEGS],
    zero: [Poly; 3],
    plus: [Poly; 3],
    minus: [Poly; 2],
}

fn ties(matrix: &[[Fr; 2]; 2], w: &[Fr; 3]) -> Option<Ties> {
    let (_c0, omega, modulus) = extension();
    let forms = form_columns(matrix);
    let z: Poly = (0..4)
        .map(|e| (0..3).map(|i| forms[i][e] * w[i]).sum())
        .collect();
    let neg = substitute(&z, -omega.inverse()?);
    let mid = substitute(&z, -Fr::one());
    let pos = substitute(&z, -omega);
    let u = div_rem(&product(&z, &neg), &modulus).1;
    let v = div_rem(&product(&z, &mid), &modulus).1;
    let weights = from_fn(|i| {
        if KIND[i] == 2 {
            coeff(&v, EXP[i])
        } else {
            coeff(&u, EXP[i])
        }
    });
    let us = substitute(&u, -omega);
    // Eq. (6): K1=1 gives U'=U, V'=V, and U''=U(-omega*T).
    let first = subtract(&product(&u, &mid), &product(&v, &neg));
    let second = subtract(&product(&u, &pos), &product(&us, &neg));
    let third = subtract(&product(&v, &pos), &product(&us, &mid));
    let zero = [
        exact(&first, &modulus)?,
        exact(&second, &modulus)?,
        exact(&third, &modulus)?,
    ];
    let plus = [first, product(&u, &pos), product(&v, &pos)];
    let minus = [
        subtract(&[], &product(&us, &neg)),
        subtract(&[], &product(&us, &mid)),
    ];
    Some(Ties {
        weights,
        zero,
        plus,
        minus,
    })
}

fn g1(x: Fr) -> G1Affine {
    (G1Projective::generator() * x).into_affine()
}
fn g2(x: Fr) -> G2Affine {
    (G2Projective::generator() * x).into_affine()
}
fn nonzero<R: RngCore + CryptoRng>(rng: &mut R) -> Fr {
    loop {
        let x = Fr::rand(rng);
        if !x.is_zero() {
            return x;
        }
    }
}

// H_key([κ]_T) has μ=100 output bits, using the first 100 SHA-256 bits
// in big-endian bit order. XOR is its own inverse.
fn xor_mask(gt: &GT, input: &Seed100) -> Seed100 {
    let mut bytes = Zeroizing::new(Vec::new());
    gt.serialize_compressed(&mut *bytes)
        .expect("serializing to a Vec");
    let mut hash = Sha256::new();
    hash.update(b"PVUGC/Praxis/BN254/reduced-bqs/H-key-100/v1");
    hash.update(bytes.as_slice());
    let digest: Zeroizing<[u8; 32]> = Zeroizing::new(hash.finalize().into());
    let mut output: Seed100 = from_fn(|j| input[j] ^ digest[j]);
    output[12] &= LAST_BYTE_MASK;
    output
}

fn expand_seed(seed: &Seed100) -> [u8; 32] {
    let mut hash = Sha256::new();
    hash.update(b"PVUGC/Praxis/BN254/reduced-bqs/DEM-seed-100/v1");
    hash.update(seed);
    hash.finalize().into()
}

pub fn encapsulate<R: RngCore + CryptoRng>(rng: &mut R) -> (Capsule, [u8; 32]) {
    let qap = Qap::new();
    let (c0, omega, _) = extension();
    let matrix = from_fn(|_| from_fn(|_| Fr::rand(rng)));
    let forms = form_columns(&matrix);
    let r: [Fr; 3] = from_fn(|_| fr(rng.gen_range(2..=G + 1)));
    let y: [Fr; 3] = from_fn(|_| Fr::rand(rng));
    let tau = loop {
        let t = Fr::rand(rng);
        if !qap.points.contains(&t) {
            break t;
        }
    };
    let omega12 = Fr::rand(rng);
    let omega22 = nonzero(rng);
    let alpha = nonzero(rng);
    let pi = nonzero(rng);
    let s_kind: [Fr; 3] = from_fn(|_| nonzero(rng));
    let upsilon = nonzero(rng);
    let zeta: [Fr; 3] = from_fn(|_| nonzero(rng));
    let eta: [Fr; 3] = from_fn(|_| nonzero(rng));
    let epsilon = loop {
        let e = nonzero(rng);
        if e != -Fr::one() {
            break e;
        }
    };
    let pi_left = pi * (Fr::one() + epsilon);
    let a = qap.a.each_ref().map(|p| evaluate(p, tau));
    let b = qap.b.each_ref().map(|p| evaluate(p, tau));
    let left = from_fn(|i| {
        [
            g1(pi_left * y[i]),
            g1(pi_left * (omega12 * y[i] + omega22 * a[i])),
        ]
    });
    let quotient = from_fn(|e| g1(zeta[0] * tau.pow([e as u64])));
    let remainder = g1(zeta[1] * tau);
    let cancel = y.map(|yi| g1(zeta[2] * yi));
    let s: [Fr; LEGS] = from_fn(|i| s_kind[KIND[i]] * upsilon.pow([EXP[i] as u64]));
    let gamma = s.map(|si| pi_left * si);
    let kappa = gamma[0] * evaluate(&qap.corner, tau);
    let pu = upsilon.pow([4]) - c0;
    let theta: [[Fr; 3]; LEGS] = from_fn(|leg| {
        from_fn(|i| {
            let zm = evaluate(&forms[i], -upsilon / omega);
            let zc = evaluate(&forms[i], -upsilon);
            let zp = evaluate(&forms[i], -omega * upsilon);
            let pow = upsilon.pow([EXP[leg] as u64]);
            if KIND[leg] == 2 {
                pow * (eta[2] * zp - eta[0] * zm)
            } else {
                pow * (eta[0] * zc + eta[1] * zp)
                    - (-omega * upsilon).pow([EXP[leg] as u64]) * (eta[1] * zm + eta[2] * zc)
                        / epsilon
            }
        })
    });
    let make_right = |scale: Fr| {
        let point = |x: Fr| g2(scale * x);
        let factor = from_fn(|leg| {
            from_fn(|i| {
                let second = s[leg] * (b[i] - y[i]) / omega22;
                [
                    point(s[leg] * (r[i] + a[i]) + theta[leg][i] - omega12 * second),
                    point(second),
                ]
            })
        });
        let quotient = from_fn(|leg| {
            let z = if leg == 0 { &qap.full_z } else { &qap.z };
            point(gamma[leg] * evaluate(z, tau) / zeta[0])
        });
        let remainder = gamma.map(|g| point(g * evaluate(&qap.z0, tau) / zeta[1]));
        let base = |a: usize, e: usize| pi * eta[a] * upsilon.pow([e as u64]) / zeta[2];
        Right {
            factor,
            search: s.map(point),
            quotient,
            remainder,
            tie: from_fn(|a| from_fn(|e| point(base(a, e) * pu))),
            cross_plus: from_fn(|a| from_fn(|e| point(base(a, e) * epsilon))),
            cross_minus: from_fn(|a| from_fn(|e| point(base(a + 1, e) / epsilon))),
        }
    };
    let key = GT::generator() * kappa;
    let mut seed = Zeroizing::new([0; 13]);
    rng.fill_bytes(&mut *seed);
    seed[12] &= LAST_BYTE_MASK;
    let capsule = Capsule {
        matrix,
        left,
        quotient,
        remainder,
        cancel,
        right: make_right(Fr::one()),
        alpha_right: make_right(alpha),
        alpha_key: key * alpha,
        masked_seed: xor_mask(&key, &seed),
    };
    (capsule, expand_seed(&seed))
}

fn sum_g1(points: &[G1Affine], factors: &[Fr]) -> G1Projective {
    debug_assert!(factors.len() <= points.len());
    points.iter().zip(factors).map(|(p, c)| *p * c).sum()
}
fn sum_g2(points: &[G2Affine], factors: &[Fr]) -> G2Projective {
    debug_assert!(factors.len() <= points.len());
    points.iter().zip(factors).map(|(p, c)| *p * c).sum()
}

pub fn decapsulate(capsule: &Capsule, witness: [bool; 2]) -> Option<[u8; 32]> {
    if capsule.masked_seed[12] & !LAST_BYTE_MASK != 0 {
        return None;
    }
    let w = [
        Fr::one(),
        fr(u64::from(witness[0])),
        fr(u64::from(witness[1])),
    ];
    let (key_q, other_q, rem) = Qap::new().openings(&w)?;
    let ties = ties(&capsule.matrix, &w)?;
    let key_weight = ties.weights[0];
    let inverse_weight = key_weight.inverse()?;
    let f: [G1Projective; 2] = from_fn(|j| (0..3).map(|i| capsule.left[i][j] * w[i]).sum());
    let y = sum_g1(&capsule.cancel, &w);
    let p_key = sum_g1(&capsule.quotient, &key_q);
    let p_other = sum_g1(&capsule.quotient, &other_q);
    let p_rem = capsule.remainder * rem;
    let comb = |right: &Right| {
        // Multi-pair products use one final exponentiation per sum; negated
        // first factors encode the subtractions in Comb, Figure 7.
        let mut lhs = Vec::new();
        let mut rhs = Vec::new();
        let mut search_lhs = Vec::new();
        let mut search_rhs = Vec::new();
        for (leg, &weight) in ties.weights.iter().enumerate() {
            for j in 0..2 {
                let h: G2Projective = (0..3).map(|i| right.factor[leg][i][j] * w[i]).sum();
                lhs.push((f[j] * weight).into_affine());
                rhs.push(h.into_affine());
            }
            search_lhs.push((f[0] * weight).into_affine());
            search_rhs.push(right.search[leg]);
        }
        let mut b = G2Projective::zero();
        for a in 0..3 {
            b += sum_g2(&right.tie[a], &ties.zero[a]);
            b += sum_g2(&right.cross_plus[a], &ties.plus[a]);
        }
        for a in 0..2 {
            b += sum_g2(&right.cross_minus[a], &ties.minus[a]);
        }
        lhs.extend([
            (-p_key).into_affine(),
            (-p_other).into_affine(),
            (-p_rem).into_affine(),
            (-y).into_affine(),
        ]);
        rhs.extend([
            (right.quotient[0] * key_weight).into_affine(),
            sum_g2(&right.quotient[1..], &ties.weights[1..]).into_affine(),
            sum_g2(&right.remainder, &ties.weights).into_affine(),
            b.into_affine(),
        ]);
        (
            Bn254::multi_pairing(lhs, rhs),
            Bn254::multi_pairing(search_lhs, search_rhs),
        )
    };
    let (lambda, psi) = comb(&capsule.right);
    let (alpha_lambda, alpha_psi) = comb(&capsule.alpha_right);
    let search_target = alpha_lambda - capsule.alpha_key * key_weight;
    // Equivalent to the centered search for §5.1: r(w) is the sum of
    // (1+wt) independent values in {2,...,g+1}. Ψ=0 also recovers K.
    let ones = 1 + u64::from(witness[0]) + u64::from(witness[1]);
    let first = 2 * ones;
    let mut candidate = alpha_psi * fr(first);
    for v in first..=ones * (G + 1) {
        if candidate == search_target {
            let recovered_gt = (lambda - psi * fr(v)) * inverse_weight;
            let seed = Zeroizing::new(xor_mask(&recovered_gt, &capsule.masked_seed));
            return Some(expand_seed(&seed));
        }
        candidate += alpha_psi;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn group_ciphertext_roundtrip_and_scope() {
        let mut rng = StdRng::seed_from_u64(7627);
        let (capsule, key) = encapsulate(&mut rng);
        let bytes = capsule.to_bytes();
        assert_eq!(bytes.len(), Capsule::WIRE_BYTES);
        let opened = Capsule::from_bytes(&bytes).unwrap();
        drop(capsule);
        for bits in [[true, false], [false, true]] {
            assert_eq!(decapsulate(&opened, bits), Some(key));
        }
        for bits in [[false, false], [true, true]] {
            assert_eq!(decapsulate(&opened, bits), None);
        }
        let mut tampered = opened.clone();
        tampered.alpha_key += GT::generator();
        assert_eq!(decapsulate(&tampered, [true, false]), None);
        let mut changed_message = opened.clone();
        changed_message.masked_seed[0] ^= 1;
        let changed_key = decapsulate(&changed_message, [true, false]).expect("valid witness");
        assert_ne!(changed_key, key);
        assert_eq!(
            decapsulate(&changed_message, [false, true]),
            Some(changed_key)
        );
        let mut bad_padding = opened;
        bad_padding.masked_seed[12] |= 1;
        assert!(Capsule::from_bytes(&bad_padding.to_bytes()).is_err());
        assert_eq!(decapsulate(&bad_padding, [true, false]), None);
        assert!(Capsule::from_bytes(&bytes[1..]).is_err());
        let mut padded = bytes.clone();
        padded.push(0);
        assert!(Capsule::from_bytes(&padded).is_err());
        let mut corrupt = bytes;
        corrupt[..32].fill(0xff);
        assert!(Capsule::from_bytes(&corrupt).is_err());
    }

    #[test]
    fn fresh_encapsulations_produce_independent_outputs_for_this_fixture() {
        let mut rng = StdRng::seed_from_u64(49017);
        let (first, k1) = encapsulate(&mut rng);
        let (second, k2) = encapsulate(&mut rng);
        assert_ne!(first.to_bytes(), second.to_bytes());
        assert_ne!(k1, k2);
        for witness in [[true, false], [false, true]] {
            assert_eq!(decapsulate(&first, witness), Some(k1));
            assert_eq!(decapsulate(&second, witness), Some(k2));
        }
    }
}
