/// PVUGC Verifying Key wrapper exposed at deposit time

use ark_ec::pairing::Pairing;

#[derive(Clone, Debug)]
pub struct PvugcVk<E: Pairing> {
    pub beta_g2: E::G2Affine,
    pub delta_g2: E::G2Affine,
    /// Arc-wrapped to avoid expensive clones (BW6-761 has dozens of large G2 points)
    pub b_g2_query: std::sync::Arc<Vec<E::G2Affine>>,
    /// Per-column hints indicating whether the column is allowed to be armed.
    /// Hints must align 1:1 with `b_g2_query`.
    pub witness_zero_hints: std::sync::Arc<Vec<bool>>,
    /// Baked Quotient Points (Q_const)
    /// These allow the decapper to compute the constant quotient term H_const(x)
    /// and subtract it from the target, ensuring security against H-based attacks.
    /// q_const_points[0] is the constant term.
    /// q_const_points[1..] correspond to public inputs.
    pub q_const_points: std::sync::Arc<Vec<E::G1Affine>>,
}

impl<E: Pairing> PvugcVk<E> {
    /// Convenience constructor that marks every column as isolated.
    pub fn new_with_all_witnesses_isolated(
        beta_g2: E::G2Affine,
        delta_g2: E::G2Affine,
        b_g2_query: Vec<E::G2Affine>,
        q_const_points: Vec<E::G1Affine>,
    ) -> Self {
        let hints = vec![true; b_g2_query.len()];
        Self {
            beta_g2,
            delta_g2,
            b_g2_query: std::sync::Arc::new(b_g2_query),
            witness_zero_hints: std::sync::Arc::new(hints),
            q_const_points: std::sync::Arc::new(q_const_points),
        }
    }

    /// Ensure witness isolation hints cover all columns and mark the witness tail as safe.
    pub fn enforce_isolated_witness_block(
        &self,
        total_instance: usize,
    ) -> crate::error::Result<()> {
        if self.witness_zero_hints.len() != self.b_g2_query.len() {
            return Err(crate::error::Error::InvalidWitnessIsolationHints);
        }
        if self
            .witness_zero_hints
            .iter()
            .skip(total_instance)
            .any(|hint| !*hint)
        {
            return Err(crate::error::Error::UnsafeWitnessColumns);
        }
        Ok(())
    }
    /// Placeholder hook for the Gröbner-audit predicate. Once the symbolic
    /// remainder is known, evaluate it on `public_inputs` and error if it
    /// vanishes. Currently a no-op so the arming flow already enforces the
    /// guard location.
    pub fn enforce_public_residual_safe(
        &self,
        _public_inputs: &[E::ScalarField],
    ) -> crate::error::Result<()> {
        Ok(())
    }
}
