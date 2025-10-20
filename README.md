# PVUGC: Proof-Agnostic Verifiable Unique Group Commitments

**Status:** Experimental Research Implementation

## 1. Overview

This repository contains an implementation of PVUGC, a cryptographic protocol for extracting Key Encapsulation Mechanism (KEM) secrets from zero-knowledge proofs in a statement-dependent, proof-agnostic manner. The protocol enables decentralized key extraction without requiring trusted committees or knowledge of the masking secret.

The implementation specializes the Groth-Sahai commitment framework to Groth16 verification, yielding a simplified one-sided construction that achieves comparable security guarantees with reduced computational overhead.


## 2. Protocol Properties

PVUGC satisfies the following cryptographic properties:

- **Proof-Agnosticism:** Different valid proofs π₁, π₂ for the same statement extract identical keys K₁ = K₂
- **Witness-Independence:** Extracted keys depend only on the statement (vk, public_inputs), not on witness values
- **Gating:** Key extraction is impossible without a valid proof
- **Permissionless Extraction:** No committee, threshold cryptography, or additional coordination required at extraction time
- **Statement-Only Setup:** Armed bases depend only on public verification keys and a single secret scalar ρ
- **Offline Arming:** One-time setup phase; armer goes offline permanently

## 3. Technical Approach

### 3.1 One-Sided Groth-Sahai Framework

The protocol employs a specialized Groth-Sahai construction optimized for Groth16 verification. Unlike traditional two-sided approaches requiring rank decomposition of coefficient matrices, the one-sided variant leverages the fact that Groth16 verifying key components (β, δ, and b_g2_query) can serve as statement-only pairing bases.

The verification equation becomes:

```
∑_ℓ e(C_ℓ, U_ℓ) + e(θ, δ) = R(vk, x)
```

where C_ℓ are commitments to proof elements, U_ℓ are aggregations of VK bases, and δ is the Groth16 discrete logarithm base.

### 3.2 Three-Phase Execution

**Phase 1: Offline Arming (Deposit)**
- ARMER generates secret ρ, derives statement-only bases from Groth16 VK
- Computes armed bases: U_ℓ^ρ, δ^ρ
- Publishes armed bases; ρ never leaves ARMER

**Phase 2: Online Proving (Spend)**
- PROVER generates valid Groth16 proof π
- Creates proof elements commitments with randomness
- Generates Schnorr proofs demonstrating coefficient consistency
- Publishes complete attestation

**Phase 3: Key Extraction (Runtime)**
- DECAPPER receives attestation, validates all proofs
- Extracts K = R^ρ using paired commitment and armed bases
- No knowledge of ρ required; security via pairing hardness

### 3.3 Comparison with Traditional Two-Sided Approach

| Property | One-Sided | Two-Sided |
|----------|-----------|-----------|
| **Setup** | VK-derived, statement-only | CRS-based, per-statement |
| **Coefficient Matrix** | Thin aggregation | Full rank decomposition |
| **Bases Required** | O(n) | O(rank²) |
| **Proof Elements** | Single (θ) | Multiple (θ, π per rank) |
| **Integration** | Native to Groth16 | Via auxiliary recomposition |
| **Randomness Cancellation** | Possible | Not Possible |

## 4. Mathematical Foundation

For the complete mathematical specification including theorems, proofs, security analysis, and design rationale, see [TECHNICAL.md](TECHNICAL.md).

Key results:

- **Soundness:** Discrete log hardness in G₂ ensures K cannot be computed without valid proof
- **Completeness:** Every valid Groth16 proof enables extraction of K = target^ρ
- **Proof-Agnosticism:** Extraction depends only on PPE verification result, not proof structure

## 5. Implementation Architecture

### 5.1 Core Modules

```
src/
  ├── lib.rs                  # Crate root; module declarations
  ├── arming.rs              # Base aggregation and arming logic
  ├── ppe.rs                 # PPE target computation from Groth16 VK
  ├── api.rs                 # High-level verification and extraction API
  ├── decap.rs               # Decapsulation algorithm
  ├── dlrep.rs               # Schnorr proofs for coefficient consistency
  ├── coeff_recorder.rs      # Hook for coefficient capture in Groth16 prover
  ├── poce.rs                # Proof of consistent encryption across arms
  └── ctx.rs                 # Context binding utilities

ark-groth16-pvugc/           # Modified Groth16 implementation with coefficient hooks
```

### 5.2 Build and Test

```bash
cargo build --release
cargo test

# Run with output
cargo test -- --nocapture

# Run specific test suites
cargo test test_one_sided_pvugc_e2e -- --nocapture
cargo test test_one_sided_security -- --nocapture
```

## 6. Usage

### 6.1 Setup and Arming

```rust
use arkworks_groth16::{OneSidedPvugc, build_row_bases_from_vk};

// Derive statement-only bases from Groth16 VK
let y_bases = extract_y_bases(&pvugc_vk);

// Aggregate bases using deterministic Γ matrix
let rows = build_row_bases_from_vk(&y_bases, delta_g2, gamma);

// Arm bases at deposit time (one-time)
let rho = Fr::rand(&mut rng);
let arms = arm_rows(&rows, &rho);

// Publish: arms, R = target^1 (computable from vk + public_inputs)
// Secret: rho
```

### 6.2 Verification and Extraction

```rust
// Prover generates complete attestation
let bundle = PvugcBundle {
    groth16_proof,
    dlrep_b,
    dlrep_tie,
    gs_commitments,
};

// Verifier validates all components
let valid = OneSidedPvugc::verify(&bundle, &pvugc_vk, &vk, &public_inputs, &gamma);

if valid {
    // Extract key
    let k = OneSidedPvugc::decapsulate(&bundle.gs_commitments, &arms);
    // k = R^ρ (same for any valid proof of same statement)
}
```

See tests for complete working examples.

## 7. Security Assumptions

The protocol relies on standard assumptions in pairing-based cryptography:

1. **Discrete Logarithm Problem (DLP):** Hard in both G₁ and G₂
2. **Pairing Hardness:** Computation of pairings is efficient; extracting discrete logs from pairings is hard
3. **Groth16 Knowledge Soundness:** Only proofs generated with knowledge of witnesses are accepted
4. **Collision Resistance:** SHA256 for Fiat-Shamir challenges

For detailed security analysis including attack vectors and mitigations, see [TECHNICAL.md](TECHNICAL.md#6-security-analysis).

## 8. Current State

This is an experimental research implementation. Aspects include:

- Complete one-sided PVUGC construction with all verification checks
- End-to-end tests demonstrating proof-agnostic extraction
- Security property tests validating statement-dependence
- Hook infrastructure for capturing coefficients from Groth16 prover

Known limitations and areas for future work:

- Tie proof aggregation should use explicit Fiat-Shamir challenge vector
- Extension to other SNARK schemes requires per-scheme PPE derivation
- Performance optimization of pairing operations

## 9. Testing

The test suite validates both functional correctness and security properties:

```bash
# End-to-end flow: Groth16 proof generation through key extraction
cargo test test_one_sided_pvugc_e2e

# Security properties: proof-agnosticism, statement-dependence
cargo test test_one_sided_security
```

## 10. References

See [TECHNICAL.md](TECHNICAL.md#references) for complete references and background on Groth-Sahai proofs, PVUGC, and related work.

### Primary Sources

- Groth, J., & Sahai, A. (2008). "Efficient non-interactive proof systems for bilinear groups." *EUROCRYPT 2008*.
- Groth, J. (2016). "On the size of pairing-based non-interactive arguments." *EUROCRYPT 2016*.

### Implementation Foundation

- arkworks: Elliptic curves, pairings, and zero-knowledge proof framework
- BLS12-381: Pairing-friendly elliptic curve

## 11. License

MIT or Apache 2.0

## 12. Citation

If you use this implementation in academic work, please cite:

```
@software{pvugc_2024,
  title={PVUGC: One-Sided Groth-Sahai Implementation},
  author={[Contributors]},
  year={2024},
  url={https://github.com/[repository]}
}
```
