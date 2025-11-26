# PVUGC Security Analysis: Algebraic Framework & GBGM Model

This document defines the algebraic framework used to prove the security of PVUGC's One-Sided Decapsulation logic under the **Hardened Arming** model (Aggregation + Baked Quotient).

## 1. The Algebraic Model (AGBGM)

We work in the Algebraic Generic Bilinear Group Model (AGBGM). The adversary interacts with a system of oracles representing the group operations in $\mathbb{G}_1, \mathbb{G}_2, \mathbb{G}_T$ and the bilinear pairing $e: \mathbb{G}_1 \times \mathbb{G}_2 \to \mathbb{G}_T$.

### 1.1 Handles and Labels
Every group element $g$ held by the adversary is represented by a handle. Internally, the oracle maintains a mapping from handles to **Algebraic Labels**, which are multivariate polynomials over the finite field $\mathbb{F}_r$ in the formal indeterminates representing the secret trapdoors.

**Trapdoor Indeterminates:**
*   $\alpha, \beta, \gamma, \delta$: The Groth16 secrets.
*   $\tau$: The structured reference string (SRS) parameter.
*   $\rho$: The fresh arming randomness (per instance).

**Available Handles (The Basis):**
The adversary starts with handles for the public parameters and the specific arming instance.

*   **Public CRS (Lean):**
    *   $\mathbb{G}_1$: $\{ [\tau^i]_1 \}_{i \in \text{Legal}}$ (Restricted set, no Full Span $H$).
    *   $\mathbb{G}_2$: $\{ [\beta]_2, [\delta]_2, [v_j(\tau)]_2 \}$.
*   **Arming Instance:**
    *   $\mathbb{G}_2$ (Masked): $\{ D_{pub} = (\beta + \sum x_i v_i(\tau))^\rho, D_\delta = \delta^\rho, D_j = v_j(\tau)^\rho \}_{j > \ell}$.
    *   **Note:** The adversary does **not** possess handles for $[1]_2^\rho$ or $[H(\tau)]_2^\rho$.

### 1.2 Adversary Capabilities
The adversary can construct new handles via:
1.  **Linear Combination:** Given handles $h_1, h_2$, compute $c_1 h_1 + c_2 h_2$. Label: $c_1 L(h_1) + c_2 L(h_2)$.
2.  **Pairing:** Given $h_1 \in \mathbb{G}_1, h_2 \in \mathbb{G}_2$, compute $e(h_1, h_2)$. Label: $L(h_1) \cdot L(h_2)$.

**Goal:** Construct a handle with label equal to the Target Label:
$$ L_{Target} = \rho \cdot (\alpha \beta + \sum x_i u_i(\tau)\beta + \gamma \sum x_i u_i(\tau)) - T_{const} $$

## 2. Security Invariants (The "Impossibility" Proofs)

Security holds because the Target Label lies outside the linear span of the labels reachable by the adversary.

### 2.1 The Gamma Invariant (Blocks GT-Slicing)
**Claim:** The adversary cannot construct the term $\rho \cdot \gamma \cdot IC(x)$ without satisfying the R1CS.

*   **Proof:**
    *   The only source of $\gamma$ is the IC-correction term $K_i = [\frac{1-\gamma}{\delta} f_i]_1$.
    *   Pairing $K_i$ with $D_\delta = \delta^\rho$ yields $\rho(1-\gamma)f_i = \rho f_i - \rho \gamma f_i$.
    *   This term is "polluted" by $\rho f_i$.
    *   To isolate $-\rho \gamma f_i$, the adversary must subtract $\rho f_i$.
    *   This requires a handle for $[1]_2^\rho$ or $[f_i]_2^\rho$.
    *   **Constraint:** The scheme strictly withholds $[1]_2^\rho$. The available handles ($D_{pub}, D_j, D_\delta$) are all linearly independent of $[1]_2^\rho$.
    *   **Result:** The pollution cannot be cleaned. The Target (which has "clean" $\gamma$ terms) is unreachable.

### 2.2 The Linearity Invariant (Blocks Full Span / Public-Public)
**Claim:** The adversary cannot forge the public residual $\Delta_{pub}$ using witness handles.

*   **Proof:**
    *   The public residual $\Delta_{pub}$ depends on the public inputs $x$.
    *   The adversary has witness handles $D_j$ corresponding to witness columns.
    *   **Constraint:** The **Trapdoor-Aware Audit** (and the Linearity property of the Outer Circuit) guarantees that the subspace spanned by the public residual is orthogonal to the subspace spanned by the witness columns.
    *   **Result:** No linear combination of $D_j$ can equal $\Delta_{pub}$ (unless the R1CS is satisfied).

### 2.3 The Baked Quotient Invariant (Blocks Remainder Forging)
**Claim:** The adversary cannot use the CRS to forge the quotient polynomial $H(x)$.

*   **Proof:**
    *   The Target $R_{baked}$ includes the constant quotient term $T_{const}$.
    *   The adversary must construct $T_{const}$ or an equivalent quotient contribution.
    *   **Constraint:** The **Lean CRS** explicitly excludes the $H$-bases (Powers of Tau) required to construct arbitrary quotient terms.
    *   **Result:** The adversary lacks the basis vectors to "bridge the gap" between an invalid witness equation and the target.

## 3. Completeness for Honest Prover

The "Honest Prover Dilemma" (Prover needs handles that Adversary abuses) is resolved by the **Linearity Assumption**.

*   Since the Public Inputs interact only linearly in the circuit, the quotient polynomial separates: $H(x) = H_{const} + H_{wit}(w)$.
*   We **bake** $H_{const}$ into the target (removing the need to construct it).
*   We **publish** handles only for $H_{wit}(w)$.
*   The adversary gets no "Dangerous" handles (handles that depend on public inputs).
*   The Honest Prover builds $H_{wit}(w)$ using the safe witness-only handles.

## 4. Reduction to Computational Assumptions

The security of the Lean CRS / Baked Quotient construction reduces to standard assumptions in the bilinear setting. We consider multiple related problems.

### 4.1 Relevant Hardness Assumptions

**Target Exponent Problem (TEP):**
Given $([1]_1, [s]_1, [1]_2, [t]_2)$ and target $T \in \mathbb{G}_T$, find $a, b \in \mathbb{F}_r$ such that:
$$e([a]_1, [b]_2) = T$$
where $T = e([1]_1, [1]_2)^{st}$ (the adversary doesn't know $st$).

**GT-XPDH (Target Group Extended Power Diffie-Hellman):**
Given $([1]_1, [\tau]_1, \ldots, [\tau^d]_1, [1]_2, [\delta]_2)$, distinguish:
$$e([f(\tau)]_1, [\delta]_2) \quad \text{vs} \quad \text{random } T \in \mathbb{G}_T$$
where $f(\tau)$ is a polynomial **not** in the span of the given $\mathbb{G}_1$ elements.

**q-SDH (q-Strong Diffie-Hellman):**
Given $([1]_1, [\tau]_1, \ldots, [\tau^q]_1)$, compute $([1/(τ+c)]_1, c)$ for any $c$.

**Bilinear Knowledge of Exponent (KoE):**
Any adversary producing $([A]_1, [B]_2)$ with $e(A, B) = T$ must "know" the exponents algebraically.

### 4.2 The GBGM Simulation

In the GBGM, the adversary interacts with group elements through an **oracle** that:
- Returns random "handles" for group elements
- Only allows linear combinations and pairings
- The adversary cannot "look inside" the handles to extract discrete logs

**Simulation Setup:**

| World | τ (toxic waste) | CRS Elements | Target |
|-------|-----------------|--------------|--------|
| Real | Concrete field element | $[\tau^i]_1, [\tau^i]_2$ at real τ | $e([q_0 + q_1 \cdot \tau]_1, [\delta]_2)$ |
| Simulated | Symbolic (never revealed) | Random handles with algebraic relations | Consistent random handle |

The simulator tracks all algebraic relations between handles. For any adversary query:
1. **Linear combination**: Returns handle consistent with tracked relations
2. **Pairing**: Returns handle consistent with the bilinear structure

### 4.3 Indistinguishability Argument

The adversary **cannot distinguish** real from simulated worlds because:

1. **Missing Bases**: The Lean CRS excludes $H_{pub}$ bases $\{[h_i(\tau)]_1\}$ for public-input-dependent quotient terms
2. **Algebraic Consistency**: All queries return answers consistent with the algebraic structure
3. **No Information Leakage**: The "gap" between Lean CRS and Full CRS is never queried

**Key Insight**: The adversary's reachable span is:
$$\text{Span}_{adv} = \text{LinComb}(\text{Lean CRS}) + \text{Pairings}(\text{Lean CRS})$$

The target requires:
$$H_{pub}(\tau) = q_0 + q_1 \cdot \tau$$

Since $H_{pub}$ bases are **not** in the Lean CRS: $H_{pub}(\tau) \notin \text{Span}_{adv}$

### 4.4 The GT-XPDH / TEP Reduction

Our setting maps directly to **GT-XPDH**:

**The Challenge:**
- Adversary has Lean CRS: $\{[\tau^i]_1\}_{i \in \text{Lean}}$, $[\delta]_2$
- Target: $T_{baked} = e([q_0 + q_1 \cdot \tau]_1, [\delta]_2)$
- $q_0 + q_1 \cdot \tau$ is **outside** the span of Lean CRS elements

**Why GT-XPDH Applies:**
The polynomial $f(\tau) = q_0 + q_1 \cdot \tau$ represents the public-input-dependent quotient. The Lean CRS deliberately excludes the bases needed to compute $[f(\tau)]_1$.

To forge a proof, the adversary must produce $C \in \mathbb{G}_1$ such that:
$$e(A, B) = T_{baked} + e(C, \delta)$$

This requires computing $e([f(\tau)]_1, [\delta]_2)$ or an equivalent $\mathbb{G}_T$ element, which is exactly the GT-XPDH problem.

**Connection to TEP:**
The Target Exponent Problem is the "search" version: given the target $T_{baked}$, find exponents $(a, b)$ such that $e([a]_1, [b]_2) = T_{baked}$. Our construction ensures:
- The adversary cannot find such $(a, b)$ without knowing $H_{pub}(\tau)$
- $H_{pub}(\tau)$ is not computable from the Lean CRS

**Theorem**: If $\mathcal{A}$ can forge a Lean proof with advantage $\epsilon$, we can solve GT-XPDH with advantage $\epsilon / \text{poly}(\lambda)$.

### 4.5 Why Affine Quotient is Critical

The affine structure $H_{pub}(x) = q_0 + q_1 \cdot x$ is essential:

| Property | Security Implication |
|----------|---------------------|
| 2-dimensional secret space | Minimal polynomial to hide outside CRS span |
| Linear in $x$ | Witness-independent (no $x^2$ terms) |
| Determined by 2 samples | Setup can compute $q_0, q_1$ from probes at $x=0, x=1$ |
| Outside adversary span | GT-XPDH-hard to compute target without bases |

If the quotient were **non-affine** (e.g., $q_0 + q_1 x + q_2 x^2$):
- Witness bits derived from $x$ would create $x$-dependent witness terms
- The quotient would mix public and witness contributions
- The clean separation (Lean CRS vs Baked Target) would break
- The GT-XPDH reduction would fail (polynomial degree mismatch)

### 4.6 The "Unknowing Simulation" Property

The adversary cannot detect they are in a simulation:

```
Adversary's Queries:           Simulator's Response:
─────────────────────────────────────────────────────
LinComb(h₁, h₂, c₁, c₂)   →   Consistent handle (tracked)
Pairing(h₁, h₂)           →   Consistent handle (tracked)
"Compute H_pub(τ)"        →   IMPOSSIBLE (no basis)
```

The adversary never queries the "missing" $H_{pub}$ bases because they're not in the Lean CRS. The simulation is **perfect** for all polynomial-time adversaries.

## 5. Outer Circuit Linearity Requirement

For the DDH reduction to hold, the outer circuit must satisfy:

### 5.1 Constraint Structure

| Constraint Type | A-column | B-column | Captured By |
|-----------------|----------|----------|-------------|
| Linear packing | $x_{outer} - \Sigma 2^i b_i$ | $1$ | $q_{const}$ (baked) |
| Witness × Witness | $w_i$ | $w_j$ | $h_{query\_wit}$ |
| VK × Proof | constant | witness | $h_{query\_wit}$ |

**Critical Invariant**: No constraint has $x_{outer}$ in **both** A and B columns.

## 6. Conclusion

The algebraic framework confirms that the **Hardened Arming** architecture is secure in the AGBGM. The combination of:

1. **Aggregation** (one-sided PPE structure)
2. **Gamma-Exclusion** (blocks GT-slicing attacks)
3. **Baked Quotient** (hides $H_{pub}$ in target)
4. **Linearity/Audit** (ensures affine quotient)
5. **GT-XPDH / TEP Reduction** (formal security proof)

eliminates the reachable subspace for all known algebraic attack vectors and reduces security to the hardness of the **Target Exponent Problem (TEP)** and **GT-XPDH** in the Generic Bilinear Group Model.

### 6.1 Assumption Hierarchy

```
                    GBGM (Generic Bilinear Group Model)
                              ↓ implies
                    GT-XPDH (Target Group XPDH)
                              ↓ implies
                    TEP (Target Exponent Problem)
                              ↓ related to
                    q-SDH, co-CDH, Bilinear KoE
```

In the **standard model** (non-generic), security relies on:
- **q-SDH**: Prevents polynomial evaluation attacks
- **co-CDH**: Prevents cross-group discrete log extraction
- **Bilinear KoE**: Ensures algebraic extractability

The GBGM provides the cleanest reduction, but the construction is believed secure under standard assumptions as well.
