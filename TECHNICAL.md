# Technical Specification: One-Sided Groth-Sahai PVUGC

## Abstract

This document provides the mathematical foundation and design rationale for the one-sided Groth-Sahai approach to Proof-Agnostic Verifiable Unique Group Commitments (PVUGC). We demonstrate how specializing the Groth-Sahai framework to Groth16 verification enables a simplified construction that achieves complete decentralization without trusted committees while maintaining cryptographic soundness and completeness.

## 1. Introduction and Motivation

### 1.1 The PVUGC Problem

PVUGC addresses a fundamental challenge in threshold cryptography: extracting a unique, deterministic key from a proof of a cryptographic statement such that:

1. **Proof-Agnosticism**: Different proofs π₁, π₂ for the same statement yield identical keys K₁ = K₂
2. **Witness-Independence**: The key depends only on the statement, not on the witness used to generate the proof
3. **Gating**: The key cannot be computed without a valid proof
4. **Permissionless**: No trusted parties required at extraction time

### 1.2 Historical Approach: Two-Sided GS

Traditional Groth-Sahai commitments employ a two-sided architecture:

**Two-Sided PPE:**
```
∑_{i,j} Γ_{i,j} · e(X_i, Y_j) = target

where:
  X_i committed on G₁ side with randomness: C₁_i = (X_i^r_i)·U₁^(r'_i)
  Y_j committed on G₂ side with randomness: C₂_j = (Y_j^s_j)·U₂^(s'_j)
```

The verifier reconstructs the target using four pairing buckets that algebraically cancel randomness:

```
M = ∑ e(C₁_i, U_i) + ∑ e(V_j, C₂_j) + ∑ e(θ_a, W_a) + ∑ e(Z_j, π_j)
  = target + (randomizer terms that cancel)
```

**Why Two-Sided Fails for PVUGC:**

For PVUGC, all bases must be statement-only (derivable from public verification keys without witness knowledge). However, the two-sided approach requires:

1. **U₁, U₂ from CRS**: These are generated per statement during "phase 1" setup but depend on the CRS itself, not the statement. Different statements require different CRS, breaking statement-only property.

2. **Both sides randomized**: X_i and Y_j both have randomness (r_i, s_j), requiring two independent randomness cancellation mechanisms (via θ and π proofs). This forces:
   - Rank decomposition Γ = ∑_a u^(a) · v^(a)^T to decompose the certificate matrix
   - Four proof elements per row (adding quadratic overhead)
   - Complex base construction from rank factors

3. **ρ-powered bases proliferate**: For PVUGC, must arm both sides: U₁^ρ, U₂^ρ, V^ρ, W^ρ, Z^ρ. This creates confusion about which bases are meant to be statement-only.

### 1.3 Insight: One-Sided Specialization

**Key Observation:** When the statement is a Groth16 verification target, the two sides play fundamentally different roles:

- **G₂ side (Y_j)**: Can be extracted directly from the Groth16 verifying key (VK)
  - Groth16 VK contains: α, β, γ, δ (all public)
  - We can construct Y_j = {β, [δb_i]₂ for i in b_g2_query}
  - These are statement-only by definition

- **G₁ side (X_i)**: The prover contributes A, C through the proof
  - A and C are witness-dependent but serve as the "X" variables
  - We can commit to these with randomness on the prover side

**One-Sided Architecture:**

Instead of randomizing both sides, we randomize only G₁:

```
∏ e(X^(B)_j, Y_j) · e(C, δ) = R(vk, x)

where:
  X^(B)_j = A^{b_j} is computed from proof elements
  Y_j ∈ G₂ extracted from VK (statement-only!)
  δ ∈ G₂ from VK (statement-only!)
  R(vk, x) = e(α, β) · e(L(x), γ) from VK + public_inputs
```

The commitment structure becomes:

```
C_row = (C_row^(0), C_row^(1)) = committed row with two limbs
θ = (θ^(0), θ^(1)) = theta proof elements
```

Both limbs are paired against the same statement-only Y_j or δ^ρ, achieving randomness cancellation without requiring rank decomposition.

## 2. Mathematical Framework

### 2.1 Groth16 Verification as PPE

Groth16 verification equation:

```
e(A, B) + e(C, δ) = e(α, β) + e(L(x), γ)

where:
  L(x) = [γ_0]₁ + ∑_i x_i·[γ_{i+1}]₁ (partial input aggregation)
```

This can be rewritten as a PPE:

```
e(A, [β]₂) + e(C, [δ]₂) = target

where target = e(α, β) + e(L(x), γ) is statement-dependent
```

### 2.2 One-Sided Commitment Structure

Define the commitment to proof elements as:

```
C_ℓ = (C_ℓ^(rand), C_ℓ^(var)) ∈ G₁ × G₁

where C_ℓ encodes row ℓ of the aggregated proof elements
```

Pairing evaluation:

```
∑_ℓ [e(C_ℓ^(rand), U_ℓ^ρ) + e(C_ℓ^(var), U_ℓ^ρ)] + [e(θ^(rand), δ^ρ) + e(θ^(var), δ^ρ)]
= ∑_ℓ e(C_ℓ^(rand) + C_ℓ^(var), U_ℓ^ρ) + e(θ^(rand) + θ^(var), δ^ρ)
= ∑_ℓ e(C_ℓ, U_ℓ^ρ) + e(θ, δ^ρ)
= (∑_ℓ e(C_ℓ, U_ℓ) + e(θ, δ))^ρ
= target^ρ
= K
```

The critical property: **randomness in C_ℓ^(rand) and C_ℓ^(var) is absorbed by pairing with the same G₂ element U_ℓ^ρ**, achieving cancellation without decomposing the coefficient matrix Γ.

### 2.3 Armed Bases

At deposit time, the armer publishes:

```
Arms = {U_ℓ^ρ for ℓ ∈ [1, m], δ^ρ}

where:
  U_ℓ = ∑_j Γ_{ℓj} · Y_j (aggregation of statement-only bases)
  Y_j ∈ {β, b_1, b_2, ..., b_n} extracted from Groth16 VK
  Γ is a thin matrix (typically m << n) with deterministic entries
```

The matrix Γ is derived deterministically from the VK digest via Fiat-Shamir:

```
Γ_seed = SHA256("PVUGC/GAMMA/v1" || VK_digest || beta_digest || delta_digest)
```

This ensures:
- Same VK always produces same Γ
- Statement-only (no witness dependence)
- Deterministic but seemingly random (Rademacher-distributed entries)

### 2.4 Proof-Agnostic Extraction

**Theorem (Proof-Agnosticism):** For any two distinct valid Groth16 proofs π₁ = (A₁, B₁, C₁) and π₂ = (A₂, B₂, C₂) of the same statement (vk, x), the decapsulation extracts identical keys:

```
decap(commitments₁, arms) = decap(commitments₂, arms)
```

**Proof Sketch:**

1. Both π₁ and π₂ satisfy the Groth16 verification equation:
   ```
   e(A₁, B₁) + e(C₁, δ) = target
   e(A₂, B₂) + e(C₂, δ) = target
   ```

2. The verifier creates commitments C₁, C₂ from the proofs, both satisfying:
   ```
   ∑_ℓ e(C₁_ℓ, U_ℓ) + e(θ₁, δ) = target
   ∑_ℓ e(C₂_ℓ, U_ℓ) + e(θ₂, δ) = target
   ```

3. The decapsulation computes:
   ```
   K₁ = ∑_ℓ e(C₁_ℓ, U_ℓ^ρ) + e(θ₁, δ^ρ)
      = (∑_ℓ e(C₁_ℓ, U_ℓ) + e(θ₁, δ))^ρ
      = target^ρ

   K₂ = ∑_ℓ e(C₂_ℓ, U_ℓ^ρ) + e(θ₂, δ^ρ)
      = (∑_ℓ e(C₂_ℓ, U_ℓ) + e(θ₂, δ))^ρ
      = target^ρ
   ```

Therefore K₁ = K₂ = target^ρ, and the extraction is proof-agnostic. ∎

## 3. Comparison with Two-Sided Approach

| Aspect | Two-Sided (Rank-Decomp) | One-Sided (Groth16-Specialized) |
|--------|--------------------------|--------------------------------|
| **CRS Dependency** | Per-statement CRS required | No CRS; uses VK directly |
| **Coefficient Matrix** | Full rank decomposition Γ = ∑ u^(a)·v^(a)^T | Thin matrix (sparse aggregation) |
| **Base Construction** | Four types: U, V, W, Z (from rank factors) | Two: U_ℓ (G₂ aggregation), δ |
| **Proof Elements** | Multiple (θ, π per rank component) | Single (θ for randomness cancellation) |
| **Arming Overhead** | O(rank²) bases armed | O(m) bases armed (m << n) |
| **Randomness Cancellation** | Two independent mechanisms | Single mechanism (pairing absorbs both limbs) |
| **Setup Complexity** | Phase-based (7 phases) | Direct (deposit-only) |
| **Groth16 Integration** | Via auxiliary 4-term reconstruction | Native (PPE is Groth16 equation) |

**Key Advantages of One-Sided:**
1. **No CRS**: Eliminates trusted setup per statement
2. **Simpler structure**: One aggregation instead of rank decomposition
3. **Direct VK usage**: Statement-only bases derived mechanically
4. **Lower overhead**: Armed bases scale with VK size (typically 50-200), not matrix rank

## 4. Cryptographic Properties

### 4.1 Soundness

**Theorem (Soundness):** If Groth16 is sound and discrete log is hard in G₂, then an adversary cannot compute K without a valid proof.

**Proof Sketch:**

1. **Suppose adversary computes K = target^ρ.**
2. **Known:** Arms = {U_ℓ^ρ, δ^ρ} and target (all public).
3. **To compute K from arms:**
   - Option A: Extract ρ from U_ℓ^ρ → requires solving DLP in G₂ ✗ (hard)
   - Option B: Use ρ directly → requires knowing ρ ✗ (secret)
   - Option C: Forge commitments satisfying PPE without valid proof
     - Requires e(C_ℓ, U_ℓ) + e(θ, δ) = target
     - But verification checks this equation and requires proof structure
     - Groth16 soundness ensures only valid proofs produce consistent (A, B, C)
4. **Conclusion:** Adversary must have valid proof. ∎

### 4.2 Completeness

**Theorem (Completeness):** For every valid Groth16 proof π of statement (vk, x), the decapsulation extracts K = target^ρ ≠ 0.

**Proof:** Follows from proof-agnosticism (Section 2.4). Every valid proof π satisfies the verification equation, and decapsulation always computes target^ρ. ∎

### 4.3 Statement-Only Property

**Theorem (Statement-Only Bases):** The armed bases {U_ℓ^ρ, δ^ρ} depend only on (vk, x, ρ), not on the proof π or witness w.

**Proof:**
- U_ℓ = ∑_j Γ_{ℓj} · Y_j where Y_j ∈ VK (public)
- Γ derived from VK digest (deterministic, public)
- δ ∈ VK (public)
- ρ is the armer's secret
- No reference to π or w in arms construction. ∎

## 5. Implementation Details

### 5.1 Coefficient Extraction

The prover exposes coefficients {b_j, c_i} through a hook in the Groth16 prover:

```
B = [β]₂ + ∑_j b_j·[b_j^query]₂
C = [δ]₁ + ∑_i c_i·[h_i]₁
```

These coefficients are used to construct:
- DLREP_B proof: demonstrates B = β + ∑ b_j·Y_j
- Tie proof: demonstrates same {b_j} used in both MSMs
- GS commitment: encodes the proof structure for PPE verification

### 5.2 Verification Flow

1. **Groth16 Verification:** e(A, B) + e(C, δ) = target (standard)
2. **DLREP_B Verification:** Schnorr proof that B decomposes correctly
3. **Tie Verification:** Cross-group DL equality of coefficients
4. **PPE Verification:** ∑ e(C_ℓ, U_ℓ) + e(θ, δ) = target (one-sided)
5. **Decapsulation:** K = ∑ e(C_ℓ, U_ℓ^ρ) + e(θ, δ^ρ) = target^ρ

### 5.3 Γ Matrix Derivation

The matrix Γ is derived deterministically via Fiat-Shamir to ensure reproducibility:

```rust
seed = SHA256("PVUGC/GAMMA/v1" || serialize(vk) || serialize(beta) || serialize(delta))

For each row ℓ, each column j:
  hash = SHA256(seed || ℓ || j)
  Γ_{ℓj} ∈ {-1, 0, +1} based on hash mod 3
```

Properties:
- Same VK always produces same Γ
- Entries are Rademacher-distributed (symmetric, sparse)
- Avoids all-zero rows for robustness

## 6. Security Analysis

### 6.1 Hardness Assumptions

1. **SXDH in (G₁, G₂, G_T):** Symmetric External Diffie-Hellman
   - Discrete log in G₁ and G₂ are both hard
   - Pairing is efficiently computable
2. **Groth16 Knowledge Soundness:** Valid proofs only from knowledge of witnesses
3. **Collision Resistance of SHA256:** For Fiat-Shamir challenges and Γ derivation

### 6.2 Attack Vectors and Mitigations

| Attack | Vector | Mitigation |
|--------|--------|-----------|
| **Forge K without proof** | Compute target^ρ from arms | DLP hardness |
| **Extract ρ from arms** | Solve G₂ DLP on U_ℓ^ρ | DLP hardness |
| **Invalid proof → extract K** | Skip Groth16 verification | Verification gates extraction |
| **Different statements → same K** | Manipulate VK or public input | Statement-only bases ensure K ≠ K' |
| **Tie proof forging** | Prove false coefficient consistency | Schnorr soundness + FS collision resistance |
| **Subgroup attack** | Inject small-order elements | Explicit subgroup membership checks |

## 7. Advantages and Limitations

### 7.1 Advantages

1. **Complete Decentralization:** No committee, no trusted parties at spend time
2. **Simple Construction:** One aggregation instead of rank decomposition
3. **Efficient Arming:** O(n) bases where n is VK size (~50-200 for typical circuits)
4. **Native Groth16 Integration:** PPE is the Groth16 equation itself
5. **Proof-Agnostic:** Different proofs extract identical keys
6. **Statement-Only:** Bases derived entirely from public VK

### 7.2 Limitations

1. **Groth16-Specific:** Construction tailored to Groth16; different SNARKs need different PPEs
2. **Matrix Size:** Γ must be at least m × n where m ≥ rank of PPE; typically m = O(√n)
3. **Verifier Overhead:** Four verification checks (Groth16, DLREP, Tie, PPE) vs. one for traditional GS
4. **Fiat-Shamir Challenges:** Tie proof aggregation should use proper FS challenge vector (minor implementation detail)

## 8. Conclusion

The one-sided Groth-Sahai specialization provides a natural, efficient path to PVUGC by:

1. **Recognizing asymmetry:** Statement-only G₂ bases can be extracted from VK
2. **Simplifying structure:** One-sided commitment eliminates rank decomposition complexity
3. **Achieving proof-agnosticism:** Decapsulation extracts only from PPE value, not proof randomness
4. **Enabling decentralization:** No trusted setup or committee required

This approach demonstrates that PVUGC is not merely a theoretical construct but a practical cryptographic primitive suitable for real-world applications in threshold signatures, Bitcoin integration, and threshold encryption.

## References

- Groth, J., & Sahai, A. (2008). "Efficient non-interactive proof systems for bilinear groups." EUROCRYPT.
- Groth, J. (2016). "On the size of pairing-based non-interactive arguments." EUROCRYPT.
- arkworks contributors. "arkworks: A Rust Ecosystem for Zero-Knowledge Proofs."

