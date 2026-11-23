//! Offline cancellation of a synthetic UTXO using the reduced Praxis profile.
#[path = "../examples/support/mod.rs"]
mod support;

use bitcoin::{sighash::TapSighashType, Amount};
use pvugc_praxis::ceremony::{wire::recover_public, Slot};
use rand::{rngs::StdRng, SeedableRng};
use support::{cancellation, receipt_hash, setup, verify, Receipt};

#[test]
fn both_valid_witnesses_complete_the_same_fixed_taproot_cancellation() {
    let mut rng = StdRng::from_seed([0x72; 32]);
    let (receipt, archive) = setup(&mut rng, 2).unwrap();
    let bytes = receipt.to_bytes();
    let pinned = receipt_hash(&bytes);
    drop(receipt);
    assert!(Receipt::parse(&bytes, [0; 32]).is_err());
    let receipt = Receipt::parse(&bytes, pinned).unwrap();
    assert!(receipt.shares(&archive, [false, false]).is_err());
    assert!(receipt.shares(&archive, [true, true]).is_err());
    assert!(recover_public(
        &archive,
        Slot::fixture([0x55; 32]),
        &receipt.roster,
        receipt.rounds,
        [false, true],
        receipt.archive_hash
    )
    .is_err());
    let first = receipt.shares(&archive, [false, true]).unwrap();
    let second = receipt.shares(&archive, [true, false]).unwrap();
    assert_eq!(first, second);
    let signature = receipt.signature(&first).unwrap();
    assert_eq!(signature, receipt.signature(&second).unwrap());
    for omitted in 0..3 {
        let partial: Vec<_> = first
            .iter()
            .enumerate()
            .filter_map(|(i, &s)| (i != omitted).then_some(s))
            .collect();
        assert!(receipt.signature(&partial).is_err());
    }
    let (mut cancel, prevout) = cancellation(receipt.output_key);
    cancel.input[0].witness.push(signature.to_vec());
    let wire = cancel.input[0].witness.iter().next().unwrap();
    assert_eq!(wire.len(), 65);
    let parsed = bitcoin::taproot::Signature::from_slice(wire).unwrap();
    assert_eq!(parsed.hash_ty, TapSighashType::All);
    verify(&cancel, &prevout, &parsed).unwrap();
    let mut changed = cancel.clone();
    changed.output[0].value = Amount::from_sat(98_999);
    assert!(verify(&changed, &prevout, &parsed).is_err());
    cancel.input[0].previous_output.vout = 2;
    assert!(verify(&cancel, &prevout, &parsed).is_err());
}
