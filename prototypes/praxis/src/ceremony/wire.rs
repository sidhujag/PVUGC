//! Portable publication of a completed reduced-profile ceremony. In roster order
//! each contribution carries its ID, coefficient points, possession proof, rows,
//! public coin commitment and reveal, then only the audited row openings.
//! Bitcoin signers authenticate the archive ID before pre-signing. Recomputing
//! an ID from a file received from the challenger does not authenticate it.
use super::{point_bytes, tagged, Contribution, Error, Frozen, Hash, Opening, Row, Slot};
use crate::rank::Capsule;
use k256::schnorr::Signature;
use k256::{ProjectivePoint, PublicKey, Scalar};
use std::io::Read;

const MAGIC: &[u8; 8] = b"PVGPXA01";
const HEADER_BYTES: usize = 8 + 2 * 32 + 2 + 4;
const POINT_BYTES: usize = 33;
const DEM_BYTES: usize = 32 + 16;
const OPENING_BYTES: usize = 2 + 32 + 32;

pub fn archive_id(bytes: &[u8]) -> [u8; 32] {
    tagged(b"public archive", &[bytes])
}

fn archive_len(m: usize, n: usize) -> Result<usize, Error> {
    if !(2..=256).contains(&m) || n == 0 || u32::try_from(n).is_err() {
        return Err(Error::Manifest);
    }
    let d = m / 2;
    let participant = 4
        + (d + 1) * POINT_BYTES
        + 64
        + m * (Capsule::WIRE_BYTES + DEM_BYTES)
        + 2 * 32
        + d * OPENING_BYTES;
    participant
        .checked_mul(n)
        .and_then(|n| n.checked_add(HEADER_BYTES))
        .ok_or(Error::Manifest)
}

fn read_array<const N: usize>(input: &mut &[u8]) -> Result<[u8; N], Error> {
    let mut bytes = [0; N];
    input.read_exact(&mut bytes).map_err(|_| Error::Manifest)?;
    Ok(bytes)
}

// The compressed SEC1 identity (one zero byte) is padded with zeros in this
// fixed-width frame. A polynomial can have zero nonconstant coefficients.
fn encode_point(point: ProjectivePoint) -> [u8; POINT_BYTES] {
    let mut bytes = [0; POINT_BYTES];
    let encoded = point_bytes(point);
    bytes[..encoded.len()].copy_from_slice(&encoded);
    bytes
}

fn decode_point(bytes: [u8; POINT_BYTES]) -> Result<ProjectivePoint, Error> {
    if bytes == [0; POINT_BYTES] {
        return Ok(ProjectivePoint::IDENTITY);
    }
    if !matches!(bytes[0], 0x02 | 0x03) {
        return Err(Error::Manifest);
    }
    let key = PublicKey::from_sec1_bytes(&bytes).map_err(|_| Error::Manifest)?;
    let point = ProjectivePoint::from(*key.as_affine());
    if encode_point(point) != bytes {
        return Err(Error::Manifest);
    }
    Ok(point)
}

pub fn encode_public(
    frozen: &Frozen,
    commits: &[[u8; 32]],
    seeds: &[[u8; 32]],
    openings: &[Vec<Opening>],
) -> Result<Vec<u8>, Error> {
    let len = archive_len(frozen.m, frozen.contributions.len())?;
    let challenge = frozen.lock_commits(commits)?.challenge(seeds)?;
    // This also prevents the writer from ever publishing unopened row coins.
    frozen.verify(&challenge, openings)?;
    let mut output = Vec::new();
    output.try_reserve_exact(len).map_err(|_| Error::Manifest)?;
    output.extend_from_slice(MAGIC);
    output.extend_from_slice(&frozen.slot.cancel_sighash);
    output.extend_from_slice(&frozen.slot.policy_digest);
    output.extend_from_slice(&(frozen.m as u16).to_be_bytes());
    output.extend_from_slice(&(frozen.contributions.len() as u32).to_be_bytes());
    for (i, package) in frozen.contributions.iter().enumerate() {
        output.extend_from_slice(&package.id.to_be_bytes());
        for &point in &package.coefficients {
            output.extend_from_slice(&encode_point(point));
        }
        output.extend_from_slice(&package.possession.to_bytes());
        for row in &package.rows {
            if row.encrypted.len() != DEM_BYTES {
                return Err(Error::Manifest);
            }
            output.extend_from_slice(&row.header.to_bytes());
            output.extend_from_slice(&row.encrypted);
        }
        output.extend_from_slice(&commits[i]);
        output.extend_from_slice(&seeds[i]);
        for opening in &openings[i] {
            output.extend_from_slice(&(opening.index as u16).to_be_bytes());
            output.extend_from_slice(&opening.value);
            output.extend_from_slice(&opening.coins);
        }
    }
    debug_assert_eq!(output.len(), len);
    Ok(output)
}

pub struct Archive {
    frozen: Frozen,
    commits: Vec<Hash>,
    seeds: Vec<Hash>,
    openings: Vec<Vec<Opening>>,
}

impl Archive {
    /// Pin all dimensions using the original authenticated roster and compare
    /// the exact byte count before allocating or deserializing any group points.
    pub fn decode(
        bytes: &[u8],
        expected_slot: Slot,
        roster: &[(u32, ProjectivePoint)],
        expected_m: usize,
        expected_archive: [u8; 32],
    ) -> Result<Self, Error> {
        if bytes.len() != archive_len(expected_m, roster.len())?
            || archive_id(bytes) != expected_archive
        {
            return Err(Error::Manifest);
        }
        let mut input = bytes;
        if &read_array::<8>(&mut input)? != MAGIC
            || read_array::<32>(&mut input)? != expected_slot.cancel_sighash
            || read_array::<32>(&mut input)? != expected_slot.policy_digest
            || u16::from_be_bytes(read_array(&mut input)?) as usize != expected_m
            || u32::from_be_bytes(read_array(&mut input)?) as usize != roster.len()
        {
            return Err(Error::Manifest);
        }
        let d = expected_m / 2;
        let mut packages = Vec::with_capacity(roster.len());
        let mut commits = Vec::with_capacity(roster.len());
        let mut seeds = Vec::with_capacity(roster.len());
        let mut openings = Vec::with_capacity(roster.len());
        for &(expected_id, expected_point) in roster {
            let id = u32::from_be_bytes(read_array(&mut input)?);
            if id != expected_id || read_array(&mut input)? != encode_point(expected_point) {
                return Err(Error::Manifest);
            }
            let mut coefficients = vec![expected_point];
            for _ in 0..d {
                coefficients.push(decode_point(read_array(&mut input)?)?);
            }
            let possession = Signature::try_from(&read_array::<64>(&mut input)?[..])
                .map_err(|_| Error::Manifest)?;
            let mut rows = Vec::with_capacity(expected_m);
            for _ in 0..expected_m {
                let (header, remaining) = input
                    .split_at_checked(Capsule::WIRE_BYTES)
                    .ok_or(Error::Manifest)?;
                input = remaining;
                rows.push(Row {
                    header: Capsule::from_bytes(header).map_err(|_| Error::Manifest)?,
                    encrypted: read_array::<DEM_BYTES>(&mut input)?.to_vec(),
                });
            }
            packages.push(Contribution {
                id,
                coefficients,
                possession,
                rows,
            });
            commits.push(read_array(&mut input)?);
            seeds.push(read_array(&mut input)?);
            let mut audited = Vec::with_capacity(d);
            for _ in 0..d {
                let index = u16::from_be_bytes(read_array(&mut input)?) as usize;
                if index >= expected_m {
                    return Err(Error::Opening);
                }
                audited.push(Opening {
                    index,
                    value: read_array(&mut input)?,
                    coins: read_array(&mut input)?,
                });
            }
            openings.push(audited);
        }
        if !input.is_empty() {
            return Err(Error::Manifest);
        }
        let frozen = Frozen::new(expected_slot, roster, packages, expected_m)?;
        Ok(Self {
            frozen,
            commits,
            seeds,
            openings,
        })
    }

    pub fn open(&self, witness: [bool; 2]) -> Result<Vec<Scalar>, Error> {
        let challenge = self
            .frozen
            .lock_commits(&self.commits)?
            .challenge(&self.seeds)?;
        self.frozen
            .verify(&challenge, &self.openings)?
            .recover(witness)
    }
}

pub fn recover_public(
    bytes: &[u8],
    expected_slot: Slot,
    roster: &[(u32, ProjectivePoint)],
    expected_m: usize,
    witness: [bool; 2],
    expected_archive: [u8; 32],
) -> Result<Vec<Scalar>, Error> {
    Archive::decode(bytes, expected_slot, roster, expected_m, expected_archive)?.open(witness)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ceremony::{arm, create_coin};
    use rand::{rngs::StdRng, SeedableRng};

    #[test]
    fn identity_coefficients_have_one_encoding() {
        assert_eq!(
            decode_point(encode_point(ProjectivePoint::IDENTITY)).unwrap(),
            ProjectivePoint::IDENTITY
        );
        let mut malformed = [0; POINT_BYTES];
        malformed[POINT_BYTES - 1] = 1;
        assert!(decode_point(malformed).is_err());
        for point in [ProjectivePoint::GENERATOR, -ProjectivePoint::GENERATOR] {
            assert_eq!(decode_point(encode_point(point)).unwrap(), point);
        }
    }

    #[test]
    fn independent_challenger_rejects_mutations_and_replacement_contexts() {
        let slot = Slot::fixture([29; 32]);
        let m = 2;
        let share = Scalar::from(32u64);
        let roster = [(17, ProjectivePoint::GENERATOR * share)];
        let mut rng = StdRng::seed_from_u64(101907);
        let (package, private) = arm(&slot, roster[0].0, share, m, &mut rng).unwrap();
        let frozen = Frozen::new(slot, &roster, vec![package], m).unwrap();
        let (commit, coin) = create_coin(&frozen, 0, &mut rng).unwrap();
        let commits = [commit];
        let board = frozen.lock_commits(&commits).unwrap();
        let (seed, receipt) = coin.reveal(&board).unwrap();
        let seeds = [seed];
        let challenge = board.challenge(&seeds).unwrap();
        let audited = private.respond(&frozen, &challenge, 0, &receipt).unwrap();
        let unopened_index = 1 - audited[0].index;
        let wrong_subset = vec![Opening {
            index: unopened_index,
            value: audited[0].value,
            coins: audited[0].coins,
        }];
        assert!(encode_public(&frozen, &commits, &seeds, &[wrong_subset]).is_err());
        let bytes = encode_public(&frozen, &commits, &seeds, &[audited]).unwrap();
        drop(frozen);
        let id = archive_id(&bytes);
        assert_eq!(
            recover_public(&bytes, slot, &roster, m, [false, true], id).unwrap(),
            vec![share]
        );
        assert!(recover_public(&bytes, slot, &roster, m, [true, true], id).is_err());
        assert!(Archive::decode(&bytes, Slot::fixture([30; 32]), &roster, m, id).is_err());
        assert!(Archive::decode(&bytes, slot, &[(18, roster[0].1)], m, id).is_err());
        assert!(Archive::decode(&bytes, slot, &roster, m + 1, id).is_err());
        assert!(Archive::decode(&bytes, slot, &roster, m, [0; 32]).is_err());
        let mut modified = bytes.clone();
        modified.push(0);
        assert!(Archive::decode(&modified, slot, &roster, m, archive_id(&modified)).is_err());
        let shorter = &bytes[..bytes.len() - 1];
        assert!(Archive::decode(shorter, slot, &roster, m, archive_id(shorter)).is_err());
        let mut modified = bytes.clone();
        *modified.last_mut().unwrap() ^= 1;
        // Both the externally authenticated transcript and the internal audited
        // reencryption reject this mutation, even when testing them separately.
        assert!(Archive::decode(&modified, slot, &roster, m, id).is_err());
        assert!(matches!(
            recover_public(
                &modified,
                slot,
                &roster,
                m,
                [false, true],
                archive_id(&modified)
            ),
            Err(Error::Opening)
        ));
        let mut bad_seed = bytes;
        let last_seed_byte = bad_seed.len() - OPENING_BYTES - 1;
        bad_seed[last_seed_byte] ^= 1;
        assert!(matches!(
            recover_public(
                &bad_seed,
                slot,
                &roster,
                m,
                [false, true],
                archive_id(&bad_seed)
            ),
            Err(Error::Coin)
        ));
    }
}
