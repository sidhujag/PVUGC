//! Cut-and-choose arming for the reduced Praxis profile.
//! Network peers must authenticate and agree on the roster, manifest, and
//! commitment board before revealing any coins. A stopped session never reopens.
pub mod wire;

use crate::rank::{decapsulate, encapsulate, Capsule};
use ark_serialize::CanonicalSerialize;
use chacha20poly1305::aead::{Aead, KeyInit, Payload};
use chacha20poly1305::{ChaCha20Poly1305, Nonce};
use k256::elliptic_curve::{sec1::ToEncodedPoint, Field, PrimeField};
use k256::schnorr::{
    signature::{Signer, Verifier},
    Signature, SigningKey,
};
use k256::{ProjectivePoint, Scalar};
use rand::{seq::SliceRandom, CryptoRng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use thiserror::Error;
use zeroize::{Zeroize, Zeroizing};

type Hash = [u8; 32];

#[derive(Clone, Copy, Debug)]
pub struct Slot {
    pub cancel_sighash: Hash,
    pub policy_digest: Hash,
}

impl Slot {
    pub fn fixture(cancel_sighash: Hash) -> Self {
        Self {
            cancel_sighash,
            policy_digest: fixture_policy_digest(),
        }
    }
}

pub fn fixture_policy_digest() -> Hash {
    Sha256::digest(b"PVUGC/Praxis/fixture/v1/BN254/bool(x,y)/(x-y)^2=1").into()
}

#[derive(Debug, Error)]
pub enum Error {
    #[error("invalid roster, commitment, policy, or ceremony dimensions")]
    Manifest,
    #[error("mismatched commitment board, seed, or challenge")]
    Coin,
    #[error("incorrect setup opening")]
    Opening,
    #[error("the supplied witness did not recover every participant's committed share")]
    Witness,
}

#[derive(Clone)]
struct Row {
    header: Capsule,
    encrypted: Vec<u8>,
}

#[derive(Clone)]
pub struct Contribution {
    id: u32,
    coefficients: Vec<ProjectivePoint>,
    possession: Signature,
    rows: Vec<Row>,
}

pub struct Opening {
    index: usize,
    value: Hash,
    coins: Hash,
}

impl Drop for Opening {
    fn drop(&mut self) {
        self.value.zeroize();
        self.coins.zeroize();
    }
}

pub struct PrivateOpenings {
    digest: Hash,
    openings: Vec<Opening>,
}

fn point_bytes(point: ProjectivePoint) -> Vec<u8> {
    point.to_affine().to_encoded_point(true).as_bytes().to_vec()
}

fn tagged(tag: &[u8], fields: &[&[u8]]) -> Hash {
    let mut h = Sha256::new();
    h.update(b"pvugc/praxis-ceremony/v1");
    for field in std::iter::once(&tag).chain(fields.iter()) {
        h.update((field.len() as u64).to_be_bytes());
        h.update(field);
    }
    h.finalize().into()
}

fn context(slot: Slot, id: u32, coefficients: &[ProjectivePoint], m: usize) -> Hash {
    let mut encoded = Vec::new();
    for &point in coefficients {
        let bytes = point_bytes(point);
        encoded.push(bytes.len() as u8);
        encoded.extend(bytes);
    }
    tagged(
        b"polynomial",
        &[
            &slot.policy_digest,
            &slot.cancel_sighash,
            &id.to_be_bytes(),
            &(m as u32).to_be_bytes(),
            &encoded,
        ],
    )
}

fn evaluation(coefficients: &[ProjectivePoint], index: usize) -> ProjectivePoint {
    let x = Scalar::from(index as u64 + 1);
    coefficients
        .iter()
        .rev()
        .fold(ProjectivePoint::IDENTITY, |y, &c| y * x + c)
}

fn scalar(bytes: &Hash) -> Result<Scalar, Error> {
    Option::from(Scalar::from_repr((*bytes).into())).ok_or(Error::Opening)
}

fn row_aad(ctx: &Hash, index: usize) -> Hash {
    tagged(b"evaluation", &[ctx, &(index as u32).to_be_bytes()])
}

fn cipher(key: &Hash, aad: &Hash) -> ChaCha20Poly1305 {
    let derived = Zeroizing::new(tagged(b"DEM key", &[key, aad]));
    ChaCha20Poly1305::new((&*derived).into())
}

fn encrypt_row(ctx: &Hash, opening: &Opening) -> Row {
    let mut rng = ChaCha20Rng::from_seed(opening.coins);
    let (header, key) = encapsulate(&mut rng);
    let key = Zeroizing::new(key);
    let aad = row_aad(ctx, opening.index);
    // Each row has independent KEM coins and a slot/index-specific DEM key.
    let encrypted = cipher(&key, &aad)
        .encrypt(
            &Nonce::default(),
            Payload {
                msg: &opening.value,
                aad: &aad,
            },
        )
        .expect("32-byte share encryption");
    Row { header, encrypted }
}

fn row_digest(row: &Row) -> Hash {
    let mut header = Vec::with_capacity(row.header.compressed_size());
    row.header
        .serialize_compressed(&mut header)
        .expect("memory buffer");
    tagged(b"capsule", &[&header, &row.encrypted])
}

fn package_digest(ctx: &Hash, package: &Contribution) -> Hash {
    let mut h = Sha256::new();
    h.update(ctx);
    h.update(package.possession.to_bytes());
    for row in &package.rows {
        h.update(row_digest(row));
    }
    h.finalize().into()
}

// Index 0 in memory represents x=1. The Bitcoin scalar lives at x=0.
pub fn arm<R: RngCore + CryptoRng>(
    slot: &Slot,
    id: u32,
    share: Scalar,
    m: usize,
    rng: &mut R,
) -> Result<(Contribution, PrivateOpenings), Error> {
    if !(2..=256).contains(&m)
        || share == Scalar::ZERO
        || slot.policy_digest != fixture_policy_digest()
    {
        return Err(Error::Manifest);
    }
    let mut polynomial = Zeroizing::new(vec![share]);
    polynomial.extend((0..m / 2).map(|_| Scalar::random(&mut *rng)));
    let coefficients: Vec<_> = polynomial
        .iter()
        .map(|c| ProjectivePoint::GENERATOR * c)
        .collect();
    let ctx = context(*slot, id, &coefficients, m);
    let signing = SigningKey::from_bytes(&share.to_bytes()).map_err(|_| Error::Manifest)?;
    let possession: Signature = signing.sign(&ctx);
    let mut rows = Vec::with_capacity(m);
    let mut openings = Vec::with_capacity(m);
    for index in 0..m {
        let x = Scalar::from(index as u64 + 1);
        let value = polynomial
            .iter()
            .rev()
            .fold(Scalar::ZERO, |y, &c| y * x + c);
        let mut coins = [0; 32];
        rng.fill_bytes(&mut coins);
        let opening = Opening {
            index,
            value: value.to_bytes().into(),
            coins,
        };
        rows.push(encrypt_row(&ctx, &opening));
        openings.push(opening);
    }
    let package = Contribution {
        id,
        coefficients,
        possession,
        rows,
    };
    let digest = package_digest(&ctx, &package);
    Ok((package, PrivateOpenings { digest, openings }))
}

pub struct Frozen {
    slot: Slot,
    m: usize,
    contributions: Vec<Contribution>,
    package_hashes: Vec<Hash>,
    digest: Hash,
}

impl Frozen {
    /// The expected roster and points come from authenticated participants before
    /// proposal validation. A coordinator cannot remove or replace the honest entry.
    pub fn new(
        slot: Slot,
        roster: &[(u32, ProjectivePoint)],
        contributions: Vec<Contribution>,
        m: usize,
    ) -> Result<Self, Error> {
        if !(2..=256).contains(&m)
            || slot.policy_digest != fixture_policy_digest()
            || roster.is_empty()
            || roster.len() != contributions.len()
            || roster.windows(2).any(|w| w[0].0 >= w[1].0)
        {
            return Err(Error::Manifest);
        }
        let mut seen = std::collections::HashSet::new();
        let mut sum = ProjectivePoint::IDENTITY;
        let mut package_hashes = Vec::with_capacity(roster.len());
        for (&(id, point), p) in roster.iter().zip(&contributions) {
            if p.id != id
                || point == ProjectivePoint::IDENTITY
                || !seen.insert(point_bytes(point))
                || p.rows.len() != m
                || p.coefficients.len() != m / 2 + 1
                || point != p.coefficients[0]
            {
                return Err(Error::Manifest);
            }
            let ctx = context(slot, id, &p.coefficients, m);
            let pk = k256::schnorr::VerifyingKey::from_bytes(&point_bytes(point)[1..])
                .map_err(|_| Error::Manifest)?;
            pk.verify(&ctx, &p.possession)
                .map_err(|_| Error::Manifest)?;
            sum += point;
            package_hashes.push(package_digest(&ctx, p));
        }
        if sum == ProjectivePoint::IDENTITY {
            return Err(Error::Manifest);
        }
        let digest = tagged(b"manifest", &[&package_hashes.concat()]);
        Ok(Self {
            slot,
            m,
            contributions,
            package_hashes,
            digest,
        })
    }

    pub fn adaptor_points(&self) -> impl Iterator<Item = ProjectivePoint> + '_ {
        self.contributions.iter().map(|p| p.coefficients[0])
    }

    pub fn lock_commits<'a>(&'a self, commits: &[Hash]) -> Result<Board<'a>, Error> {
        if commits.len() != self.contributions.len() {
            return Err(Error::Coin);
        }
        Ok(Board {
            frozen: self,
            commits: commits.to_vec(),
            digest: tagged(b"board", &[&self.digest, &commits.concat()]),
        })
    }

    pub fn verify<'a>(
        &'a self,
        challenge: &Challenge,
        reveals: &[Vec<Opening>],
    ) -> Result<Verified<'a>, Error> {
        if challenge.manifest != self.digest || reveals.len() != self.contributions.len() {
            return Err(Error::Opening);
        }
        let mut samples = Vec::with_capacity(reveals.len());
        for (p, openings) in self.contributions.iter().zip(reveals) {
            if openings.len() != challenge.selected.len() {
                return Err(Error::Opening);
            }
            let ctx = context(self.slot, p.id, &p.coefficients, self.m);
            let mut values = Vec::new();
            for (&index, o) in challenge.selected.iter().zip(openings) {
                let y = scalar(&o.value)?;
                if index != o.index
                    || ProjectivePoint::GENERATOR * y != evaluation(&p.coefficients, index)
                    || row_digest(&encrypt_row(&ctx, o)) != row_digest(&p.rows[index])
                {
                    return Err(Error::Opening);
                }
                values.push((index, y));
            }
            samples.push(values);
        }
        Ok(Verified {
            frozen: self,
            samples,
        })
    }
}

pub struct Board<'a> {
    frozen: &'a Frozen,
    commits: Vec<Hash>,
    digest: Hash,
}

pub fn coin_commit(frozen: &Frozen, index: usize, seed: &Hash) -> Hash {
    tagged(
        b"coin",
        &[&frozen.digest, &(index as u64).to_be_bytes(), seed],
    )
}

pub struct PrivateCoin {
    manifest: Hash,
    index: usize,
    seed: Zeroizing<Hash>,
}

pub fn create_coin<R: RngCore + CryptoRng>(
    frozen: &Frozen,
    index: usize,
    rng: &mut R,
) -> Result<(Hash, PrivateCoin), Error> {
    if index >= frozen.contributions.len() {
        return Err(Error::Coin);
    }
    let mut seed = Zeroizing::new([0; 32]);
    rng.fill_bytes(&mut *seed);
    Ok((
        coin_commit(frozen, index, &seed),
        PrivateCoin {
            manifest: frozen.digest,
            index,
            seed,
        },
    ))
}

impl PrivateCoin {
    pub fn reveal(self, board: &Board<'_>) -> Result<(Hash, BoardReceipt), Error> {
        if self.manifest != board.frozen.digest
            || board.commits.get(self.index)
                != Some(&coin_commit(board.frozen, self.index, &self.seed))
        {
            return Err(Error::Coin);
        }
        Ok((
            *self.seed,
            BoardReceipt {
                digest: board.digest,
                index: self.index,
            },
        ))
    }
}

pub struct BoardReceipt {
    digest: Hash,
    index: usize,
}

pub struct Challenge {
    board: Hash,
    manifest: Hash,
    selected: Vec<usize>,
}

impl Board<'_> {
    pub fn challenge(&self, seeds: &[Hash]) -> Result<Challenge, Error> {
        if seeds.len() != self.commits.len() {
            return Err(Error::Coin);
        }
        let mut combined = [0u8; 32];
        for (index, seed) in seeds.iter().enumerate() {
            if self.commits[index] != coin_commit(self.frozen, index, seed) {
                return Err(Error::Coin);
            }
            for (b, s) in combined.iter_mut().zip(seed) {
                *b ^= s;
            }
        }
        let mut rng = ChaCha20Rng::from_seed(tagged(b"subset", &[&self.frozen.digest, &combined]));
        let mut selected: Vec<_> = (0..self.frozen.m).collect();
        selected.shuffle(&mut rng);
        selected.truncate(self.frozen.m / 2);
        selected.sort_unstable();
        Ok(Challenge {
            board: self.digest,
            manifest: self.frozen.digest,
            selected,
        })
    }
}

impl PrivateOpenings {
    /// Consumes the secret state. Opening a second subset of the same manifest
    /// would disclose the share. Crash recovery must abandon the entire session.
    pub fn respond(
        self,
        frozen: &Frozen,
        challenge: &Challenge,
        index: usize,
        receipt: &BoardReceipt,
    ) -> Result<Vec<Opening>, Error> {
        if receipt.digest != challenge.board
            || receipt.index != index
            || challenge.manifest != frozen.digest
            || frozen.package_hashes.get(index) != Some(&self.digest)
        {
            return Err(Error::Opening);
        }
        Ok(self
            .openings
            .into_iter()
            .filter(|o| challenge.selected.binary_search(&o.index).is_ok())
            .collect())
    }
}

fn interpolate_at_zero(samples: &[(usize, Scalar)]) -> Scalar {
    let mut sum = Scalar::ZERO;
    for &(i, y) in samples {
        let x = Scalar::from(i as u64 + 1);
        let mut numerator = Scalar::ONE;
        let mut denominator = Scalar::ONE;
        for &(j, _) in samples {
            if i != j {
                let other = Scalar::from(j as u64 + 1);
                numerator *= -other;
                denominator *= x - other;
            }
        }
        sum += y * numerator * denominator.invert().unwrap();
    }
    sum
}

pub struct Verified<'a> {
    frozen: &'a Frozen,
    samples: Vec<Vec<(usize, Scalar)>>,
}

impl Verified<'_> {
    pub fn recover(&self, witness: [bool; 2]) -> Result<Vec<Scalar>, Error> {
        let mut shares = Vec::new();
        for (p, opened) in self.frozen.contributions.iter().zip(&self.samples) {
            let ctx = context(self.frozen.slot, p.id, &p.coefficients, self.frozen.m);
            let recovered = p
                .rows
                .iter()
                .enumerate()
                .find_map(|(index, row)| {
                    if opened.iter().any(|&(i, _)| i == index) {
                        return None;
                    }
                    let key = Zeroizing::new(decapsulate(&row.header, witness)?);
                    let aad = row_aad(&ctx, index);
                    let bytes = Zeroizing::new(
                        cipher(&key, &aad)
                            .decrypt(
                                &Nonce::default(),
                                Payload {
                                    msg: &row.encrypted,
                                    aad: &aad,
                                },
                            )
                            .ok()?,
                    );
                    let value = scalar(bytes.as_slice().try_into().ok()?).ok()?;
                    if ProjectivePoint::GENERATOR * value != evaluation(&p.coefficients, index) {
                        return None;
                    }
                    let mut all = opened.clone();
                    all.push((index, value));
                    let secret = interpolate_at_zero(&all);
                    (ProjectivePoint::GENERATOR * secret == p.coefficients[0]).then_some(secret)
                })
                .ok_or(Error::Witness)?;
            shares.push(recovered);
        }
        Ok(shares)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_rows_hit_the_combinatorial_bound() {
        // Only rows 0 and 1 match their committed ciphertexts. With d=2 out
        // of M=4, exactly one of the six possible subsets can pass the audit.
        let mut rng = ChaCha20Rng::from_seed([41; 32]);
        let slot = Slot::fixture([19; 32]);
        let share = Scalar::from(71u64);
        let (mut package, state) = arm(&slot, 7, share, 4, &mut rng).unwrap();
        package.rows[2].encrypted[0] ^= 1;
        package.rows[3].encrypted[0] ^= 1;
        let roster = [(7, ProjectivePoint::GENERATOR * share)];
        let frozen = Frozen::new(slot, &roster, vec![package], 4).unwrap();
        let mut passes = Vec::new();
        for i in 0..4 {
            for j in i + 1..4 {
                let selected = vec![i, j];
                let openings = selected
                    .iter()
                    .map(|&index| {
                        let o = &state.openings[index];
                        Opening {
                            index,
                            value: o.value,
                            coins: o.coins,
                        }
                    })
                    .collect();
                // Inject a challenge only inside this private unit test to
                // enumerate the exact audit distribution without guessing seeds.
                let c = Challenge {
                    manifest: frozen.digest,
                    board: [0; 32],
                    selected,
                };
                if let Ok(v) = frozen.verify(&c, &[openings]) {
                    passes.push((i, j));
                    assert!(v.recover([true, false]).is_err());
                }
            }
        }
        assert_eq!(passes, vec![(0, 1)]);
    }

    #[test]
    fn setup_rejects_wrong_roster_slot_board_and_seed() {
        let mut rng = ChaCha20Rng::from_seed([96; 32]);
        let slot = Slot::fixture([27; 32]);
        let (p, state) = arm(&slot, 1, Scalar::ONE, 2, &mut rng).unwrap();
        let (q, _) = arm(&slot, 2, Scalar::from(2u64), 2, &mut rng).unwrap();
        let roster = [
            (1, ProjectivePoint::GENERATOR),
            (2, ProjectivePoint::GENERATOR * Scalar::from(2u64)),
        ];
        let packages = vec![p.clone(), q.clone()];
        assert!(Frozen::new(slot, &roster, vec![p], 2).is_err());
        let wrong = Slot::fixture([13; 32]);
        assert!(Frozen::new(wrong, &roster, packages.clone(), 2).is_err());
        assert!(Frozen::new(slot, &[roster[1], roster[0]], packages.clone(), 2).is_err());
        let frozen = Frozen::new(slot, &roster, packages, 2).unwrap();
        let (commit, coin) = create_coin(&frozen, 0, &mut rng).unwrap();
        let other_seed = [55; 32];
        let first = frozen
            .lock_commits(&[commit, coin_commit(&frozen, 1, &other_seed)])
            .unwrap();
        let (honest_seed, receipt) = coin.reveal(&first).unwrap();
        assert!(first.challenge(&[honest_seed, [0; 32]]).is_err());
        let alternate = frozen
            .lock_commits(&[commit, coin_commit(&frozen, 1, &[23; 32])])
            .unwrap();
        let alternate_challenge = alternate.challenge(&[honest_seed, [23; 32]]).unwrap();
        assert!(state
            .respond(&frozen, &alternate_challenge, 0, &receipt)
            .is_err());
    }
}
