//! PVUGC witness extraction hooks for Winterfell verifier
//!
//! This module provides verifier-side hooks to extract FRI fold data and DEEP
//! composition witnesses during STARK verification for feeding into the hybrid
//! inner circuit.

#![cfg(feature = "pvugc-hooks")]

use crate::math::fields::f64::BaseElement;
use crate::math::FieldElement;
use crate::verifier::VerifierError;
use crate::Air;
use crate::crypto::Hasher;
use crate::Proof;
use crate::ProofOptions;

// Import default verifier components
use crate::verifier::channel::DefaultVerifierChannel;
use crate::verifier::fri::FriVerifier;

/// FRI fold triple for one layer, one query
#[derive(Default, Clone, Debug)]
pub struct FriFold {
    pub v_lo: BaseElement,
    pub v_hi: BaseElement,
    pub v_next: BaseElement,
}

/// Witness data extracted from STARK verification
#[derive(Default, Clone, Debug)]
pub struct WitnessLog {
    pub gl_commit_roots: Vec<[u8; 32]>,    // GL commitment roots
    pub query_positions: Vec<u64>,         // Domain positions
    pub x_points: Vec<BaseElement>,        // Query points (one per query)
    pub zeta: Option<BaseElement>,         // OOD point
    pub comp_claims: Vec<BaseElement>,     // p(x) used to seed FRI (one per query)
    pub fri_betas: Vec<BaseElement>,       // One per FRI layer
    pub fri_layers: Vec<Vec<FriFold>>,     // [layer][query] triples
}

/// Logging wrapper around DefaultVerifierChannel
///
/// Captures witness data during verification without changing verification semantics.
pub struct LoggingVerifierChannel<H: Hasher> {
    inner: DefaultVerifierChannel<H>,
    pub log: WitnessLog,
}

impl<H: Hasher> LoggingVerifierChannel<H> {
    pub fn new(proof: Proof, options: &ProofOptions) -> Result<Self, VerifierError> {
        let inner = DefaultVerifierChannel::<H>::new(proof, options)?;
        Ok(Self {
            inner,
            log: WitnessLog::default(),
        })
    }

    /// Read commitment and log GL root
    pub fn read_commitment(&mut self) -> Result<[u8; 32], VerifierError> {
        let r = self.inner.read_commitment()?;
        self.log.gl_commit_roots.push(r);
        Ok(r)
    }

    /// Read query positions and log them
    pub fn read_query_positions(&mut self) -> Result<Vec<u64>, VerifierError> {
        let pos = self.inner.read_query_positions()?;
        self.log.query_positions = pos.clone();
        Ok(pos)
    }

    /// Read OOD point and log zeta
    pub fn read_ood_point(&mut self) -> Result<BaseElement, VerifierError> {
        let z = self.inner.read_ood_point()?;
        self.log.zeta = Some(z);
        Ok(z)
    }

    /// Read composition evaluation at x (DEEP composition)
    pub fn read_composition_at_x(&mut self) -> Result<BaseElement, VerifierError> {
        // This reads the composition polynomial evaluation p(x) per query
        // which is used to seed FRI
        let px = self.inner.read_composition_at_x()?;
        self.log.comp_claims.push(px);
        Ok(px)
    }

    /// Get mutable access to inner channel for delegation
    pub fn inner_mut(&mut self) -> &mut DefaultVerifierChannel<H> {
        &mut self.inner
    }
}

/// Verify STARK proof and extract witness data
///
/// This runs normal Winterfell verification but captures FRI/DEEP witness data
/// needed for the hybrid inner circuit.
///
/// # Returns
/// WitnessLog containing all FRI folds, DEEP evaluations, and challenge data
pub fn verify_and_log<AIR, H: Hasher>(
    air: &AIR,
    proof: Proof,
    options: &ProofOptions,
) -> Result<WitnessLog, VerifierError>
where
    AIR: Air<BaseField = BaseElement>,
{
    let mut ch = LoggingVerifierChannel::<H>::new(proof, options)?;

    // 1) Read commitments (logs GL roots automatically)
    let _main = ch.read_commitment()?;
    // If proof has auxiliary trace commitment, add:
    // let _aux = ch.read_commitment()?;

    // 2) Read OOD point ζ
    let _zeta = ch.read_ood_point()?;

    // 3) Read query positions
    let positions = ch.read_query_positions()?;

    // 4) Build FRI verifier over our logging channel
    let mut fri = FriVerifier::<H>::new(air, ch.inner_mut())?;

    // 5) Process each query
    let num_layers = fri.num_layers();
    ch.log.fri_layers = vec![Vec::with_capacity(positions.len()); num_layers];

    for &pos in positions.iter() {
        // Map position to field element x
        let x = fri.index_to_field_element(pos);
        ch.log.x_points.push(x);

        // Read composition at x (logs p(x))
        let px = ch.read_composition_at_x()?;

        // Process FRI layers
        let mut _cur = px;
        for layer in 0..num_layers {
            // Get beta for this layer
            let beta = fri.read_layer_challenge(layer);
            if ch.log.fri_betas.len() <= layer {
                ch.log.fri_betas.push(beta);
            }

            // Read fold pair for this layer and position
            let (v_lo, v_hi) = fri.read_fold_pair(layer, pos)?;
            
            // Compute v_next = v_lo + beta * v_hi
            let v_next = v_lo + (beta * v_hi);

            ch.log.fri_layers[layer].push(FriFold { v_lo, v_hi, v_next });

            _cur = v_next;
        }
    }

    // Finalize FRI verification
    fri.finalize_verification()?;

    Ok(ch.log)
}
