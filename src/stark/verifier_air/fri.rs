//! FRI Verification for Verifier AIR
//!
//! Implements FRI (Fast Reed-Solomon Interactive Oracle Proof) verification.
//! This is the core low-degree test in STARK proofs.
//!
//! ## FRI Protocol Overview
//!
//! FRI proves that a polynomial has degree < d by iteratively folding:
//! 1. Start with evaluations of f(x) over domain D
//! 2. For each layer, fold: g(x²) = (f(x) + f(-x))/2 + β·(f(x) - f(-x))/(2x)
//! 3. Each layer halves the domain size
//! 4. Final layer: check that remainder is constant (or low-degree poly)

use winterfell::math::{fields::f64::BaseElement, FieldElement};

use super::merkle::{BatchMerkleVerifier, MerkleDigest, MerklePath};

// ============================================================================
// FRI LAYER
// ============================================================================

/// A single FRI layer's query data
#[derive(Clone, Debug)]
pub struct FriLayerQuery {
    /// Evaluation f(x) at query point
    pub f_x: BaseElement,
    /// Evaluation f(-x) at conjugate point
    pub f_neg_x: BaseElement,
    /// Merkle path for f(x)
    pub merkle_path: MerklePath,
    /// Position in layer domain
    pub position: usize,
}

/// Complete FRI layer proof data
#[derive(Clone, Debug)]
pub struct FriLayer {
    /// Commitment to layer evaluations
    pub commitment: MerkleDigest,
    /// Query responses
    pub queries: Vec<FriLayerQuery>,
}

// ============================================================================
// FRI VERIFIER
// ============================================================================

/// Configuration for FRI verification
#[derive(Clone, Debug)]
pub struct FriConfig {
    /// Folding factor (typically 2)
    pub folding_factor: usize,
    /// Initial domain size
    pub initial_domain_size: usize,
    /// Domain generator (for computing x coordinates)
    pub domain_generator: BaseElement,
    /// Domain offset
    pub domain_offset: BaseElement,
    /// Number of FRI layers
    pub num_layers: usize,
    /// Maximum remainder degree (0 = constant)
    pub max_remainder_degree: usize,
}

impl FriConfig {
    /// Compute domain size after given number of folds
    pub fn domain_size_at_layer(&self, layer: usize) -> usize {
        self.initial_domain_size >> (layer * self.folding_factor.trailing_zeros() as usize)
    }

    /// Compute generator for layer domain
    pub fn generator_at_layer(&self, layer: usize) -> BaseElement {
        let mut g = self.domain_generator;
        for _ in 0..layer {
            // g^{2^folding} for binary folding
            for _ in 0..self.folding_factor.trailing_zeros() {
                g = g * g;
            }
        }
        g
    }
}

/// FRI verification result
#[derive(Clone, Debug)]
pub struct FriVerificationResult {
    /// Whether all layers verified successfully
    pub success: bool,
    /// Final folded values (should be consistent with remainder)
    pub final_values: Vec<BaseElement>,
    /// Any error message
    pub error: Option<String>,
}

/// Verify a complete FRI proof
pub fn verify_fri(
    config: &FriConfig,
    layers: &[FriLayer],
    initial_evals: &[BaseElement],
    initial_positions: &[usize],
    betas: &[BaseElement],
    remainder: &[BaseElement],
) -> FriVerificationResult {
    if layers.len() != betas.len() {
        return FriVerificationResult {
            success: false,
            final_values: vec![],
            error: Some("Layer count mismatch with betas".into()),
        };
    }

    if layers.len() != config.num_layers {
        return FriVerificationResult {
            success: false,
            final_values: vec![],
            error: Some("Layer count mismatch with config".into()),
        };
    }

    // Current folded values and positions
    let mut current_values = initial_evals.to_vec();
    let mut current_positions = initial_positions.to_vec();

    // Verify each layer
    for (layer_idx, (layer, beta)) in layers.iter().zip(betas.iter()).enumerate() {
        let layer_domain_size = config.domain_size_at_layer(layer_idx);
        let layer_generator = config.generator_at_layer(layer_idx);

        // Create Merkle verifier for this layer
        let merkle_depth = (layer_domain_size as f64).log2() as usize;
        let verifier = BatchMerkleVerifier::new(layer.commitment, merkle_depth);

        // For each query, verify Merkle path and compute fold
        let mut next_values = Vec::with_capacity(current_values.len());
        let mut next_positions = Vec::with_capacity(current_positions.len());

        for (i, query) in layer.queries.iter().enumerate() {
            // Verify position matches
            let expected_pos = current_positions[i] % layer_domain_size;
            if query.position != expected_pos {
                return FriVerificationResult {
                    success: false,
                    final_values: vec![],
                    error: Some(format!(
                        "Position mismatch at layer {}: expected {}, got {}",
                        layer_idx, expected_pos, query.position
                    )),
                };
            }

            // Verify Merkle path for f(x)
            let leaf = query_to_leaf(query.f_x, query.f_neg_x);
            if !verifier.verify_leaf(&leaf, &query.merkle_path) {
                return FriVerificationResult {
                    success: false,
                    final_values: vec![],
                    error: Some(format!(
                        "Merkle verification failed at layer {}, query {}",
                        layer_idx, i
                    )),
                };
            }

            // Compute x coordinate for this position
            let x = compute_domain_point(query.position, layer_generator, config.domain_offset);

            // Verify consistency: current value should equal what we expect
            if layer_idx > 0 {
                // After first layer, check that query.f_x matches our computed fold
                let expected = current_values[i];
                if query.f_x != expected {
                    return FriVerificationResult {
                        success: false,
                        final_values: vec![],
                        error: Some(format!(
                            "Fold consistency failed at layer {}, query {}",
                            layer_idx, i
                        )),
                    };
                }
            }

            // Compute folded value: g(x²) = (f(x) + f(-x))/2 + β·(f(x) - f(-x))/(2x)
            let folded = fold_evaluation(query.f_x, query.f_neg_x, x, *beta);
            next_values.push(folded);
            next_positions.push(query.position / 2);
        }

        current_values = next_values;
        current_positions = next_positions;
    }

    // Final check: all folded values should be consistent with remainder polynomial
    if !verify_remainder(&current_values, &current_positions, remainder, config) {
        return FriVerificationResult {
            success: false,
            final_values: current_values,
            error: Some("Remainder verification failed".into()),
        };
    }

    FriVerificationResult {
        success: true,
        final_values: current_values,
        error: None,
    }
}

// ============================================================================
// HELPER FUNCTIONS
// ============================================================================

/// Fold evaluation: g(x²) = (f(x) + f(-x))/2 + β·(f(x) - f(-x))/(2x)
pub fn fold_evaluation(
    f_x: BaseElement,
    f_neg_x: BaseElement,
    x: BaseElement,
    beta: BaseElement,
) -> BaseElement {
    let two = BaseElement::new(2);
    let two_x = two * x;

    let sum = f_x + f_neg_x;
    let diff = f_x - f_neg_x;

    // g = sum/2 + beta * diff / (2x)
    sum / two + beta * diff / two_x
}

/// Convert query values to Merkle leaf (4-element digest)
fn query_to_leaf(f_x: BaseElement, f_neg_x: BaseElement) -> MerkleDigest {
    // Pack two values into a 4-element digest
    // In production, use proper serialization
    [f_x, f_neg_x, BaseElement::ZERO, BaseElement::ZERO]
}

/// Compute domain point: offset · g^position
fn compute_domain_point(
    position: usize,
    generator: BaseElement,
    offset: BaseElement,
) -> BaseElement {
    offset * generator.exp((position as u64).into())
}

/// Verify remainder polynomial evaluation
fn verify_remainder(
    final_values: &[BaseElement],
    final_positions: &[usize],
    remainder: &[BaseElement],
    config: &FriConfig,
) -> bool {
    if remainder.is_empty() {
        // Constant remainder: all values should be equal
        if final_values.is_empty() {
            return true;
        }
        let first = final_values[0];
        final_values.iter().all(|&v| v == first)
    } else {
        // Polynomial remainder: evaluate P(x) at each position
        let _final_domain_size = config.domain_size_at_layer(config.num_layers);
        let final_generator = config.generator_at_layer(config.num_layers);

        for (i, &value) in final_values.iter().enumerate() {
            let x = compute_domain_point(final_positions[i], final_generator, config.domain_offset);
            let expected = evaluate_poly(remainder, x);
            if value != expected {
                return false;
            }
        }
        true
    }
}

/// Evaluate polynomial at point using Horner's method
fn evaluate_poly(coeffs: &[BaseElement], x: BaseElement) -> BaseElement {
    if coeffs.is_empty() {
        return BaseElement::ZERO;
    }

    let mut result = coeffs[coeffs.len() - 1];
    for i in (0..coeffs.len() - 1).rev() {
        result = result * x + coeffs[i];
    }
    result
}

// ============================================================================
// TESTS
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fold_evaluation_symmetric() {
        // When f(x) = f(-x), folding gives (f(x) + f(-x))/2 = f(x)
        let f_x = BaseElement::new(42);
        let f_neg_x = BaseElement::new(42);
        let x = BaseElement::new(7);
        let beta = BaseElement::ZERO;

        let result = fold_evaluation(f_x, f_neg_x, x, beta);
        assert_eq!(result, f_x);
    }

    #[test]
    fn test_fold_evaluation_antisymmetric() {
        // When f(x) = -f(-x), folding gives beta * f(x) / x
        let f_x = BaseElement::new(10);
        let f_neg_x = BaseElement::ZERO - f_x; // -10
        let x = BaseElement::new(5);
        let beta = BaseElement::new(1);

        let result = fold_evaluation(f_x, f_neg_x, x, beta);
        // sum = 0, diff = 20
        // g = 0 + 1 * 20 / 10 = 2
        assert_eq!(result, BaseElement::new(2));
    }

    #[test]
    fn test_evaluate_poly() {
        // P(x) = 1 + 2x + 3x²
        let coeffs = [BaseElement::new(1), BaseElement::new(2), BaseElement::new(3)];
        let x = BaseElement::new(2);

        // P(2) = 1 + 4 + 12 = 17
        let result = evaluate_poly(&coeffs, x);
        assert_eq!(result, BaseElement::new(17));
    }

    #[test]
    fn test_fri_config_domain_size() {
        let config = FriConfig {
            folding_factor: 2,
            initial_domain_size: 64,
            domain_generator: BaseElement::new(7),
            domain_offset: BaseElement::ONE,
            num_layers: 3,
            max_remainder_degree: 0,
        };

        assert_eq!(config.domain_size_at_layer(0), 64);
        assert_eq!(config.domain_size_at_layer(1), 32);
        assert_eq!(config.domain_size_at_layer(2), 16);
        assert_eq!(config.domain_size_at_layer(3), 8);
    }
}
