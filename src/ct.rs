use subtle::ConstantTimeEq;
use ark_serialize::CanonicalSerialize;
use ark_ec::pairing::Pairing;

/// Constant-time equality on GT by comparing canonical compressed encodings.
pub fn ct_eq_gt<E: Pairing>(a: &E::TargetField, b: &E::TargetField) -> bool {
    let mut ab = Vec::new();
    let mut bb = Vec::new();
    a.serialize_compressed(&mut ab).expect("serialize");
    b.serialize_compressed(&mut bb).expect("serialize");
    ab.ct_eq(&bb).unwrap_u8() == 1
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Bls12_381;

    #[test]
    fn ct_eq_gt_self() {
        let one = <Bls12_381 as Pairing>::TargetField::ONE;
        assert!(ct_eq_gt::<Bls12_381>(&one, &one));
    }
}
