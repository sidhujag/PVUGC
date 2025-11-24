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

## 4. Conclusion

The algebraic framework confirms that the **Hardened Arming** architecture is secure in the AGBGM. The combination of **Aggregation**, **Gamma-Exclusion**, **Baked Quotient**, and **Linearity/Audit** eliminates the reachable subspace for all known algebraic attack vectors.
