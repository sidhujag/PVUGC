# PVUGC: Proof-Agnostic Verifiable Unique Group Commitments

## A Technical Overview of Designs, No-Go Results, and the Final Algebraic Construction

---

## TL;DR

Most "obvious" routes to PVUGC fail for fundamental algebraic reasons. The only algebraic construction that satisfies all requirements—without Witness Encryption and without a spend-time committee—is a **one-sided Groth-Sahai attestation specialized to Groth16's verifier equation**, with:

- **G₂ side** built only from statement-only bases in the Groth16 verifying key (VK)
- **G₁ side** carrying prover coefficients as group elements (never raw scalars)
- **Deposit-only arms** {U_ℓ^ρ, δ₂^ρ} without any anchor-arm leak
- **Decapsulation** computing K = R(vk,x)^ρ, where R is Groth16's public GT constant

---

## 1. Requirements & Threat Model

### R1 — Proof-Agnostic
Any two valid proofs π₁, π₂ of statement (vk, x) extract the same key K.

### R2 — Witness-Independent  
K depends only on (vk, x), not on witness w or proof randomness r, s.

### R3 — Gating
Without a valid proof, K must be infeasible to derive from published data.

### R4 — Permissionless Spend
No online party or committee required at extraction time; anyone can verify and decapsulate.

### R5 — Deposit-Only Arming
Statement-only G₂ arms published once at deposit; no trapdoors; no anchor-arm leakage (e.g., no T₀^ρ).

---

## 2. What Does Not Work (with Formal Reasons)

### 2.1 Two-Sided GS Over Groth16 (Direct)

**Idea:** Encode Groth16's pairing product as a standard two-sided GS PPE and arm both sides.

**Why it fails:**

Groth16's proof element B ∈ G₂ is proof-randomized. Any two-sided PPE necessarily includes proof-side G₂ terms. With statement-only G₂ arms, the randomness cannot be canceled. Attempts either:
- Leave a residual term (breaks completeness)
- Require per-proof arms (violates R5)
- Leak gates via an anchor-arm (violates R3)

**Formal barrier (Pairing-Preimage Lemma §4.1):** 
With statement-only bases B_j = HashToG₂(vk, x), if any B_j correlates with a public anchor T₀, then publishing T₀^ρ leaks M^ρ = e(H₁, T₀^ρ) ⇒ gating fails. If all B_j are independent, satisfying the PPE requires a discrete log in G_T ⇒ completeness dies.

---

### 2.2 Anchored KZG / Anchored PLONK

**Idea:** Change KZG's verifying equation target from 1 to a public anchor M.

**Why it fails:**

KZG's identity is rigid: e(W, Z) = e(C - y[1]₂, [1]₂). Multiplying by an anchor just rephrases "= 1". Decapsulation still lifts to 1^ρ (no key).

For PLONK: changing the final product to M without changing the prover breaks honest-proof completeness. Even if you fix the prover, the ρ-lift still yields 1^ρ. Thus decap gives no usable key.

---

### 2.3 One-Sided GS with External Anchor M = e(H₁, T₀)

**Idea:** Pick independent B_j, publish a one-sided PPE target M = e(H₁, T₀), and arm T₀^ρ.

**Why it fails:**

- **Gating leak:** If T₀^ρ is published, anyone computes M^ρ = e(H₁, T₀^ρ) without a proof ⇒ R3 fails.
- **Completeness loss:** If T₀^ρ is hidden and B_j ⟂ T₀, then satisfying ∑ Γ_{ij} e(X_i, B_j) = M requires a pairing preimage ⇒ impossible.

**There is no third door.**

---

### 2.4 Interlocked Anchor (Without Extra Secret)

**Idea:** Publish T₀^ρ directly; let decappers pair it with public H₁.

**Why it fails:**

Breaks gating: anyone computes M^ρ with no proof. Only viable if you add a private pre-signature or threshold unblinding (changes model; adds spend-time party ⇒ violates R4).

---

### 2.5 Alternatives That Do Work (But Relax Assumptions)

**Masked anchor + threshold-VRF unblinding:** Works, but requires a spend-time committee event ⇒ violates R4.

**Witness Encryption (WE) capsule for T₀^ρ:** Works under WE/iO/LWE; introduces stronger assumptions and larger artifacts.

---

## 3. The Algebraic Construction That Works

### 3.1 Use the Groth16 Verifier Equation as the Target

Define the Groth16 verifier target:

$$R(\mathsf{vk},x) \;=\; e(\alpha_1,\beta_2) \cdot e(L(x),\gamma_2)$$

where $L(x) = [\gamma_0]_1 + \sum_i x_i[\gamma_{i+1}]_1$.

Groth16's check (normalized):

$$\boxed{e(A,B) \cdot e(-C,\delta_2) \;=\; R(\mathsf{vk},x)}$$

### 3.2 One-Sided GS: All G₂ Bases Are Statement-Only

**Build a public G₂ basis from the verifying key:**

- $Y_j$: columns from which B is assembled (includes $\beta_2$ and $b_{g2\_query}$)
- $\delta_2$: single base for the C-side term
- **CRITICAL: $\gamma_2$ is deliberately EXCLUDED from armed bases**

**Column-based arming (no Γ matrix needed):**

Publish $\{Y_j^\rho\}$ and $\delta_2^\rho$ plus a single **PoCE-A** proof showing they share the same ρ ≠ 0.

Note: Column approach directly arms each Y_j without aggregation, eliminating the need for Γ matrices.

**These are statement-only; no anchor-arm like T₀^ρ is ever published.**

**Security property (γ₂ exclusion):**
The target R(vk,x) = e(α, β) · e(L(x), γ) contains [γ]₂ in the second factor. Since [γ]₂^ρ is never armed, computing R^ρ from {Y_j^ρ, δ₂^ρ} alone is infeasible (requires either discrete log in 𝔾₂ to recover ρ, or access to γ₂^ρ which is never published). This is standard bilinear hardness, not a novel assumption.

---

### 3.3 Carry Prover Coefficients on the G₁ Side

The Groth16 prover knows the scalars used to form B and C. Without ever revealing scalars:

- Compute $X_j^{(B)} := b_j A \in \mathbb{G}_1$ for each column
- C-side point: $-C \in \mathbb{G}_1$

**Small Schnorr/DLREP proofs** (no pairings) verify:
- $B = \beta_2 + \sum_j b_j Y_j$
- The published point equals $-C$

---

### 3.4 Verifier Equality (One-Sided PPE)

$$\boxed{\prod_j e(X_j^{(B)}, Y_j) \cdot e(-C,\delta_2) \;\stackrel{?}{=}\; R(\mathsf{vk},x)}$$

**By bilinearity:** The LHS = $e(A,B) \cdot e(-C,\delta_2)$, so the equality holds if and only if Groth16 verifies.

---

### 3.5 Decapsulation (Permissionless, Proof-Agnostic, Witness-Independent)

$$\boxed{K \;=\; \left(\prod_j e(X_j^{(B)}, Y_j^\rho)\right) \cdot e(-C,\delta_2^\rho) \;=\; \big(R(\mathsf{vk},x)\big)^\rho}$$

**Properties:**

| Property | Satisfied | Reason |
|----------|-----------|--------|
| **Proof-Agnostic** | ✓ | Different valid proofs → same R ⇒ same K |
| **Witness-Independent** | ✓ | R depends only on (vk, x) |
| **Gated** | ✓ | Without valid proof bundle, cannot produce consistent {C_ℓ}, -C |
| **Permissionless** | ✓ | Decap is pure pairing arithmetic; no committee |
| **Deposit-Only Arms** | ✓ | Arms are statement-only; no anchor-arm leak |

---

## 4. Why Other Designs Fail (Formal No-Go Sketches)

### 4.1 Two-Sided GS with Statement-Only Arms — Pairing-Preimage Lemma

**Claim:** With statement-only G₂ bases B_j, you cannot simultaneously achieve completeness and gating.

**Proof sketch:**

Suppose $\Phi(\{X_i\}) = \sum_{i,j} \Gamma_{ij} e(X_i, B_j)$ and the prover must satisfy $\Phi = M$.

- **Case 1:** If some $B_j$ is correlated with a public anchor (e.g., $B_1 = T_0$), then publishing $B_1^\rho = T_0^\rho$ leaks $M^\rho = e(H_1, T_0^\rho)$ → **gating fails**.
- **Case 2:** If all $B_j$ are independent of the anchor, then computing $\log_{e(g_1, B)} M$ in $\mathbb{G}_T$ is required → **infeasible by DLP** → **completeness fails**.

**No third door exists.** ∎

### 4.2 KZG/PLONK Anchoring — Rigidity

KZG's verifier computes $e(W, Z) \stackrel{?}{=} e(C - y[1]_2, [1]_2) = e(\text{stuff}, 1)$.

Any "anchor" multiplication just rephrases the comparison to 1. Thus $K = 1^\rho$ (no key).

---

## 5. Implementation Notes

### Prover Hook
Expose only group points {C_ℓ} and -C, plus Schnorr ties. **Never publish scalar coefficients.**

### Row Compression
Choose Γ (e.g., Rademacher entries via Fiat-Shamir) so |{U_ℓ}| ≈ 16–32, independent of circuit size.

### Arming Bundle
Publish {U_ℓ^ρ}, δ₂^ρ + one PoCE-Across (proving same ρ). Use PoCE-Across to ensure ρ consistency across all arms.

### Context Binding
Bind VK digest, exact Y^{(B)} list and order, Γ, and transcript hashes into a single ctx_hash. Use for Fiat-Shamir challenges in DLREP and PoCE.

### Checks
- Subgroup and cofactor validation
- Reject degenerate R = 1
- Verify all Schnorr/DLREP ties before accepting commitments

### Optional: Transparent GS-Lite Commitments
Hide {C_ℓ}, -C under hash-derived commitments; open with Schnorr. No CRS or trapdoors required.

---

## 6. Security Summary

### Assumptions
- **DLP/SXDH** in (G₁, G₂, G_T)
- **Groth16 Knowledge-Soundness** (standard)
- **Random Oracle** for Fiat-Shamir

### Soundness
Forging a decap key without a valid proof bundle implies breaking Groth16, DLREP, or solving a discrete log in an adversarial setting.

### Proof-Agnosticism
$K = R^\rho$ depends only on (vk, x); any valid proof yields the same R.

### Privacy
- No scalar leakage
- Only group elements published
- Arms reveal nothing about ρ

---

## 7. Alternatives (When You Relax Assumptions)

### Masked Anchor + Threshold-VRF Unblinding
Meets all PVUGC goals except R4 (permissionless spend). Requires a spend-time committee to unbind the anchor.

### Witness Encryption Capsule for T₀^ρ
Meets all PVUGC goals but relies on WE/iO/LWE assumptions. Larger artifacts; heavier to implement.

**Use these only when operational or assumption trade-offs are acceptable.**

---

## 8. Minimal API Surface (Suggested)

```rust
// Armer (offline, one-time)
fn setup_and_arm(
    pvugc_vk: &PvugcVk<E>,
    groth16_vk: &VerifyingKey<E>,
    public_inputs: &[E::ScalarField],
    rho: &E::ScalarField,
) -> Result<(
    ColumnBases<E>,
    ColumnArms<E>,
    PairingOutput<E>,
    PairingOutput<E>,
)>

// Prover (online, repeatable)
fn produce_bundle(
    groth16_proof: &Proof<E>,
    vk: &VerifyingKey<E>,
    public_inputs: &[E::ScalarField],
) -> PvugcBundle<E>

// Verifier (online, repeatable)
fn verify(
    bundle: &PvugcBundle<E>,
    pvugc_vk: &PvugcVk<E>,
    vk: &VerifyingKey<E>,
    public_inputs: &[E::ScalarField],
) -> bool

// Decapper (online, permissionless)
fn decap(
    commitments: &OneSidedCommitments<E>,
    arms: &Arms<E>,
) -> PairingOutput<E>  // K = R^ρ
```

---

## 9. Conclusion

### The Algebraic Landscape

| Approach | Proof-Agnostic | Gated | Permissionless | Deposit-Only | Additional Assumptions |
|----------|---|---|---|---|---|
| Two-Sided GS | ✗ | ✗ | ✓ | ✗ | (breaks on pairing preimage) |
| Anchored KZG | ✗ | ✗ | ✓ | ✓ | (rigidity: yields 1^ρ) |
| External-Anchor One-Sided | ✗ | ✗ | ✓ | ✗ | (gating leak or preimage) |
| **One-Sided GS (This Work)** | **✓** | **✓** | **✓** | **✓** | **None (algebraic only)** |
| Masked Anchor + VRF | ✓ | ✓ | ✗ | ✓ | Spend-time committee |
| WE Capsule | ✓ | ✓ | ✓ | ✓ | WE/iO/LWE |

#### Why Two-Sided Fails: The Randomness Cancellation Problem

| Aspect | One-Sided GS | Two-Sided GS |
|--------|---|---|
| **Randomness Sources** | Only G₁ side (prover's commitments) | Both G₁ and G₂ (both randomized) |
| **Cancellation Mechanism** | Single: e(C_ℓ^(rand), U_ℓ) + e(C_ℓ^(var), U_ℓ) both pair with **same** G₂ element U_ℓ | Dual: requires separate θ and π proof elements for **each rank component** |
| **Statement-Only Arms** | Achievable: U_ℓ, δ₂ derived from VK only | **Infeasible**: would need rank² armed bases; each rank component's cancellation requires per-rank proof |
| **Gating Consequence** | Safe: no anchor-arm leakage (R5 satisfied) | **Broken**: publishing armed bases for rank decomposition leaks T₀^ρ-like terms (R5 violated) |
| **Why It Fails** | N/A | Pairing-preimage lemma: statement-only G₂ bases cannot simultaneously achieve completeness AND gating with dual randomness sources |

### Final Statement

**Two-sided GS, anchored KZG/PLONK, and external-anchor one-sided GS all fail under strict PVUGC constraints due to hard algebraic barriers (pairing-preimage or rigidity) or gating leakage.**

**The one-sided GS specialized to the Groth16 verifier equation is the only algebraic solution providing:**
- Deposit-only arming with statement-only bases
- Permissionless decapsulation
- Proof-agnostic key extraction
- Witness-independent keys
- Gating against forgery

**…without Witness Encryption and without a spend-time committee.**

---

## References

- Groth, J., & Sahai, A. (2008). "Efficient non-interactive proof systems for bilinear groups." *EUROCRYPT*.
- Groth, J. (2016). "On the size of pairing-based non-interactive arguments." *EUROCRYPT*.
- arkworks contributors. "arkworks: A Rust Ecosystem for Zero-Knowledge Proofs."

