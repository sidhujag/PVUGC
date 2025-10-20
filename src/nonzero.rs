use ark_ff::{PrimeField, Zero};
use zeroize::Zeroize;

/// A wrapper that guarantees a non-zero field element (zeroized on drop).
#[derive(Clone, Debug)]
pub struct NonZero<F: PrimeField>(F);

impl<F: PrimeField> NonZero<F> {
    pub fn new(value: F) -> Result<Self, &'static str> {
        if value.is_zero() {
            return Err("rho must be non-zero");
        }
        Ok(Self(value))
    }
    pub fn inner(&self) -> &F { &self.0 }
    pub fn into_inner(self) -> F { self.0 }
}

impl<F: PrimeField> Drop for NonZero<F> {
    fn drop(&mut self) { self.0.zeroize(); }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::Fr;
    use ark_ff::{Zero, One};

    #[test]
    fn rejects_zero() {
        assert!(NonZero::<Fr>::new(Fr::ZERO).is_err());
        assert!(NonZero::<Fr>::new(Fr::ONE).is_ok());
    }
}
