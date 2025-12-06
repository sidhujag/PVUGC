# PVUGC Security Analysis: Algebraic Framework & GBGM Model

This document defines the algebraic framework used to prove the security of PVUGC's One-Sided Decapsulation logic. Security rests on four pillars:

1. **W-Span Separation** — $W_{pub} \perp W_{wit}$ (verified by circuit audit; U/V-span trivially satisfied)
2. **Lean CRS** — No Powers of Tau; baked quotient $Q_{const}$ in $\mathbb{G}_T$ only
3. **Linear Circuit Design** — No constraint places a public input in A or B
4. **Public Inputs in C-Matrix** — Statement binding via W-polynomial ($IC_i = w_i/\gamma$)

**Notation:** We write the group law in $\mathbb{G}_T$ multiplicatively. The target is:
$$R_{baked}(vk, x) = e([\alpha]_1, [\beta]_2) \cdot e(IC(x), [\gamma]_2) \cdot T_{const}(x)$$
where $T_{const}(x) = \prod_i T_i^{x_i} = e(Q_{const}(x), [\delta]_2)$ is the baked quotient correction.

**Architecture:** Public inputs are bound in the C-matrix only ($v_{pub} = 0$, $u_{pub} = 0$). This:
- Eliminates $(wit,pub)$ cross-terms in the quotient
- Makes U-span and V-span separation trivially satisfied
- Shifts statement binding to the W-polynomial via $IC_i = w_i/\gamma$

## 1. The Algebraic Model (AGBGM)

We work in the Algebraic Generic Bilinear Group Model (AGBGM). The adversary interacts with a system of oracles representing the group operations in $\mathbb{G}_1, \mathbb{G}_2, \mathbb{G}_T$ and the bilinear pairing $e: \mathbb{G}_1 \times \mathbb{G}_2 \to \mathbb{G}_T$.

### 1.1 Handles and Labels
Every group element $g$ held by the adversary is represented by a handle. Internally, the oracle maintains a mapping from handles to **Algebraic Labels**, which are multivariate polynomials over the finite field $\mathbb{F}_r$ in the formal indeterminates representing the secret trapdoors.

**Trapdoor Indeterminates:**
*   $\alpha, \beta, \gamma, \delta$: The Groth16 secrets.
*   $\tau$: The structured reference string (SRS) parameter.
*   $\rho$: The fresh arming randomness (per instance).

**Available Handles (The Basis):**
The adversary starts with handles for the public parameters (Lean CRS + Verification Key) and the specific arming instance. We list the explicit algebraic labels because the poisoning is the source of every security invariant.

*   **Public CRS / VK (unarmed):**
    *   $\mathbb{G}_1$ — circuit queries
        *   $A_k$ ($k > \ell$): $u_k(\tau)$ (clean witness-column bases, no $\rho$)
        *   $B^{(1)}_k$ ($k > \ell$): $v_k(\tau)$ in $\mathbb{G}_1$
        *   $L_k$ ($k > \ell$): $\frac{\beta u_k(\tau) + \alpha v_k(\tau) + w_k(\tau)}{\delta}$ (witness-only, poisoned by $\alpha,\beta,\delta^{-1}$)
        *   $IC_i$ ($i \le \ell$): $\frac{\beta u_i(\tau) + \alpha v_i(\tau) + w_i(\tau)}{\gamma}$ (public-input coefficients, poisoned by $\gamma^{-1}$)
        *   $H_{wit}$: $H_{i,j}(\tau)$ where at least one of $i,j$ indexes a witness column
    *   $\mathbb{G}_2$ — verification key elements
        *   $[\beta]_2, [\gamma]_2, [\delta]_2$
        *   $B^{(2)}_k = [v_k(\tau)]_2$ (clean, unmasked)
    *   $\mathbb{G}_T$ — GT-baked public quotient correction
        *   $T_i = e(Q_i(\tau), \delta)$ for $0 \le i \le \ell$, where $Q_{const}(x,\tau) = \sum_{i=0}^{\ell} x_i Q_i(\tau)$
        *   $T_{const}(x) = e(Q_{const}(x,\tau), \delta) = \prod_{i=0}^{\ell} T_i^{x_i}$ is publicly computable in $\mathbb{G}_T$
        *   Note: $Q_{const}$ is the gap between standard and lean proofs, not the full quotient polynomial
*   **Explicit Exclusions (Lean CRS):**
    *   No clean polynomial bases for public columns (only witness-column $A_k/B_k$ are published); no stand-alone Powers-of-$\tau$ ladder
    *   No public-only $H$ bases in $\mathbb{G}_1$ (the constant quotient polynomials $H_i(\tau)$ never appear as $\mathbb{G}_1$ handles)
    *   No armed $[\gamma]_2^\rho$, $[1]_2^\rho$, or $[H(\tau)]_2^\rho$
*   **Arming Instance (masked by $\rho$):**
    *   $[\beta]_2^\rho = \rho \cdot \beta$ (constant; $v_{pub} = 0$ means no public B-columns to aggregate)
    *   $[\delta]_2^\rho = \rho \cdot \delta$
    *   $[v_j(\tau)]_2^\rho = \rho \cdot v_j(\tau)$ for all witness columns $j > \ell$

Even though the Lean CRS exposes clean witness-column bases ($A_k$, $B_k$), they span only the witness subspace. Because public-only $H$ bases and Powers-of-$\tau$ elements are withheld, and because the circuit is audited to keep public columns linear, those witness handles remain orthogonal to the baked public quotient. This is the core "span separation" analyzed in §2.1 and §2.3.

### 1.2 Adversary Capabilities
The adversary can construct new handles via:
1.  **Linear Combination:** Given handles $h_1, h_2$, compute $c_1 h_1 + c_2 h_2$. Label: $c_1 L(h_1) + c_2 L(h_2)$.
2.  **Pairing:** Given $h_1 \in \mathbb{G}_1, h_2 \in \mathbb{G}_2$, compute $e(h_1, h_2)$. Label: $L(h_1) \cdot L(h_2)$.

**Goal:** Construct a handle with label equal to the Target Label. With $u_{pub} = v_{pub} = 0$:
$$ L(K_{core}) = \rho \cdot (\alpha\beta + W_{pub}) $$

where $W_{pub}$ is the public-input contribution to the C-polynomial (since $U_{pub} = V_{pub} = 0$). The Lean CRS bakes the public quotient correction into $\mathbb{G}_T$, so the effective baked target becomes:
$$ L_{Target} = \rho \cdot \left(\alpha\beta + W_{pub} + Q_{const}\delta\right) $$

where $Q_{const}(x)$ is the affine correction computed from the gap between standard and lean proofs.

**Why [α]₁ can be public:** Even though the adversary has $[\alpha]_1$, they cannot extract $K_{core}$ because:
- With $v_{pub} = 0$, pairing $[\alpha]_1$ with armed B-handles yields no statement-dependent pollution
- The adversary cannot synthesize $\rho W_{pub}$ from witness handles (blocked by W-span separation)
- Statement binding is through $R(\mathsf{vk}, x)$ via $IC_i = w_i/\gamma$, not through armed B-handles

## 2. Security Invariants (The "Impossibility" Proofs)

We argue security entirely inside the Algebraic Generic Bilinear Group Model. A WE adversary may issue arbitrary linear-combination and pairing queries—it is not constrained to produce Groth16-style $(A,B,C)$ tuples. Security holds because the Target Label lies outside the algebraic span reachable from the Lean CRS handles.

### 2.1 Attack Vector Analysis

With public inputs in C-matrix only ($v_{pub} = 0$, $u_{pub} = 0$), the attack surface is simplified:

**Attack A: Residue Synthesis (W-Span Attack)**
- The adversary tries to synthesize: $Residue = \rho \cdot W_{pub}$
- Available witness handles generate only $\rho W_{wit}$
- **Blocked by:** W-span separation ($W_{pub} \perp W_{wit}$)

**Attack B: Baked Quotient Synthesis**
- The adversary has $H_{ij}$ bases for $(const, wit)$ and $(wit, wit)$ pairs
- The baked quotient $T_{const}$ encodes $W_{pub}/Z$ in $\mathbb{G}_T$
- Since $u_{pub} = v_{pub} = 0$, $H_{ij}$ only encodes $(U_{wit} \cdot V_{wit})/Z$
- **Blocked by:** Span membership check ($Q_{const} \notin \text{span}(H_{ij})$, verified by audit)

**Note:** With $v_{pub} = 0$, pairing $[\alpha]_1$ with any armed B-handle yields no statement-dependent "pollution" term. This eliminates the classic V-span attack vector entirely by architectural design.

### 2.2 The Gamma Invariant (Supplementary Barrier)
**Claim:** (Supplementary) The adversary cannot construct the term $\rho \cdot \gamma \cdot IC(x)$ without satisfying the R1CS. This barrier is not relied upon for the main span-separation argument but provides additional algebraic separation.

**Proof (degree argument):**

We track the degrees of the independent indeterminates $\rho$ (arming secret) and $\gamma$ (Groth16 trapdoor) inside every handle. Although the baked target used in PVUGC involves only $\rho$ (the $\gamma$ factors cancel for honest users), it is useful to note that any adversarial attempt to recreate a $\rho \cdot \gamma$ term—by arming the IC bases themselves—fails for algebraic reasons.

| Handle Type | Group | $Deg_\rho$ | $Deg_\gamma$ | Notes |
|-------------|:-----:|:----------:|:------------:|-------|
| $A_k$, $L_k$, $H_{wit}$ | $\mathbb{G}_1$ | 0 | 0 | witness-column bases (no $\gamma$ factor) |
| $IC_i$ | $\mathbb{G}_1$ | 0 | -1 | only source with $\gamma^{-1}$ |
| VK constants $[\beta]_2, [\gamma]_2, [\delta]_2$ | $\mathbb{G}_2$ | 0 | $\le 1$ | unarmed |
| Armed handles $[\beta]_2^\rho, [\delta]_2^\rho, [v_j]_2^\rho$ | $\mathbb{G}_2$ | 1 | 0 | carry $\rho$, never $\gamma$ |

When the adversary forms a pairing $E = e(H_1, H_2)$, the degrees add:

1. If $H_2$ is armed ($Deg_\rho = 1$), then $Deg_\gamma(E) = Deg_\gamma(H_1) \le 0$ because no $\mathbb{G}_1$ handle has positive $\gamma$ degree.
2. If $H_2$ is unarmed ($Deg_\rho = 0$), then $Deg_\rho(E) = Deg_\rho(H_1) = 0$.

Thus no pairing (nor any linear combination thereof) can yield a handle with $Deg_\rho = 1$ **and** $Deg_\gamma = 1$. Even if an adversary tried to arm the IC bases directly, the $\rho \cdot \gamma$ monomial would remain algebraically unreachable.

### 2.3 Full Span Separation (Primary Defense)
**Claim:** The adversary cannot forge the public residual using witness handles because the public and witness subspaces are orthogonal.

**The Three Span Separations:**

| Matrix | Separation | Status | Notes |
|--------|------------|--------|-------|
| U (A-matrix) | $U_{pub} \perp U_{wit}$ | **TRIVIAL** | $u_{pub} = 0$ (public not in A) |
| V (B-matrix) | $V_{pub} \perp V_{wit}$ | **TRIVIAL** | $v_{pub} = 0$ (public not in B) |
| W (C-matrix) | $W_{pub} \perp W_{wit}$ | **VERIFIED** | Primary defense; $w_{pub} \neq 0$ for statement binding |

**Proof:**
- Public inputs bound via `1 * reconstructed = x_pub` (C-matrix only)
- This sets $u_{pub} = 0$ and $v_{pub} = 0$ for all public columns
- Statement binding via $IC_i = w_i/\gamma$ where $w_i \neq 0$
- The adversary has witness handles $A_k$, $B_k$, $L_k$, $H_{wit}$, and armed $D_j$—all tied solely to witness columns
- The **Circuit Audit** verifies:
  1. $u_{pub} = 0$ (no public in A-matrix)
  2. $v_{pub} = 0$ (no public in B-matrix)
  3. $W_{pub} \perp W_{wit}$ (disjoint row support in C-matrix)
- Result: W-span separation is the sole active defense; U/V-span are trivially satisfied

### 2.4 The Baked Quotient Invariant (Blocks Quotient Forging)
**Claim:** The adversary cannot use the CRS to forge the quotient correction $Q_{const}(x)$ or its armed equivalent.

*   **What the Adversary CAN Do:**
    *   The adversary **can** compute $T_{const}(x) = \prod_{i=0}^{\ell} T_i^{x_i}$ in $\mathbb{G}_T$ from the public GT-baked handles $T_i$ and the public inputs $x_i$.

*   **What the Adversary CANNOT Do:**
    *   They have **no $\mathbb{G}_1$ handle** for $Q_{const}(x,\tau)$: the quotient correction bases are missing from the $\mathbb{G}_1$ span (Lean CRS explicitly excludes them).
    *   They have **no way to apply $\rho$ inside $\mathbb{G}_T$**: the only source of $\rho$ is in the armed $\mathbb{G}_2$ handles, and pairing is $\mathbb{G}_1 \times \mathbb{G}_2 \to \mathbb{G}_T$. There is no operation that takes a $\mathbb{G}_T$ element and multiplies it by $\rho$.

*   **Conclusion:** The adversary cannot synthesize $[Q_{const}(x,\tau)]_1$ in $\mathbb{G}_1$, nor can they compute $T_{const}(x)^\rho$ from their handle set. The armed target remains unreachable.

## 3. Completeness for Honest Prover

The "Honest Prover Dilemma" (Prover needs handles that Adversary abuses) is resolved by the **Linearity Assumption**.

*   Since no constraint places public inputs in A or B, the quotient separates: $H(x,w) = Q_{const}(x) + H_{wit}(w)$.
*   We **bake** $Q_{const}$ into the target as $T_{const}(x) = e(Q_{const}(x,\tau), \delta)$.
*   We **publish** handles only for $H_{wit}(w)$ (the $(const, wit)$ and $(wit, wit)$ pairs).
*   The adversary gets no handles involving public inputs (since $u_{pub} = v_{pub} = 0$).
*   The Honest Prover builds $H_{wit}(w)$ using the safe witness-only handles.

## 4. Reduction to Computational Assumptions

The security of the Lean CRS / Baked Quotient construction reduces to standard assumptions in the bilinear setting. We consider multiple related problems.

### 4.1 The Core Assumption: GT-XPDH

**GT-XPDH (Target Group Extended Power Diffie-Hellman):**
Given statement-only bases $\{Y_j\}, \Delta \in \mathbb{G}_2$, their $\rho$-powers $\{Y_j^\rho\}, \Delta^\rho$, and independent target $R \in \mathbb{G}_T$, compute $R^\rho$.

**Theorem (Tight Reduction):** GT-XPDH reduces tightly to DDH in $\mathbb{G}_2$:
- If adversary breaks GT-XPDH with advantage $\epsilon$, there exists solver for DDH in $\mathbb{G}_2$ with advantage $\geq \epsilon - 1/r$
- **SXDH implies GT-XPDH** (only the $\mathbb{G}_2$-half of SXDH is needed)

See `gt-xpdh-reduction.md` for the complete proof.

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

1. **Missing $\mathbb{G}_1$ Bases**: The Lean CRS excludes $Q_{const}$ bases $\{[Q_i(\tau)]_1\}$ for public-input-dependent quotient correction
2. **GT-Baked Projections Only**: The adversary receives only $\mathbb{G}_T$ projections $T_i = e(Q_i(\tau), \delta)$, not the underlying $\mathbb{G}_1$ elements
3. **Algebraic Consistency**: All queries return answers consistent with the algebraic structure
4. **No $\rho$-Scaling in $\mathbb{G}_T$**: There is no operation to multiply a $\mathbb{G}_T$ element by the arming secret $\rho$

**Adversary's View:**
- Lean CRS in $\mathbb{G}_1$: witness-only bases (no $Q_{const}$ bases)
- $\mathbb{G}_2$ VK: includes $[\delta]_2$
- $\mathbb{G}_T$ handles: $T_i = e(Q_i(\tau), \delta)$ for $0 \le i \le \ell$

**Key Insight**: The adversary's reachable span is:
$$\text{Span}_{adv} = \text{LinComb}(\text{Lean CRS}) + \text{Pairings}(\text{Lean CRS})$$

The *polynomial* $f(\tau) = Q_{const}(x,\tau)$ underlying $T_{const} = e(f(\tau), \delta)$ is still outside the $\mathbb{G}_1$ span. Even though $T_{const}$ itself is computable in $\mathbb{G}_T$, the adversary cannot compute $T_{const}^\rho$ because $\rho$ only appears in armed $\mathbb{G}_2$ handles.

### 4.4 The GT-XPDH / TEP Reduction

Our setting maps directly to **GT-XPDH**:

**The Challenge:**
- Adversary has Lean CRS: $\{[\tau^i]_1\}_{i \in \text{Lean}}$ (no $Q_{const}$ bases), $[\delta]_2$
- Adversary has GT-baked handles: $T_i = e(Q_i(\tau), \delta)$ for $0 \le i \le \ell$
- Target: $T_{const}^\rho$ where $T_{const} = e([Q_{const}(x,\tau)]_1, [\delta]_2)$
- $Q_{const}(x,\tau)$ is **outside** the $\mathbb{G}_1$ span of Lean CRS elements

**Why GT-XPDH Applies:**
The polynomial $f(\tau) = Q_{const}(x,\tau)$ represents the public-input-dependent quotient correction. The Lean CRS deliberately excludes the $\mathbb{G}_1$ bases needed to compute $[f(\tau)]_1$. The adversary can compute $T_{const} = e(f(\tau), \delta)$ from the GT-baked handles, but cannot:
1. Extract $[f(\tau)]_1$ from $T_{const}$ (discrete log in $\mathbb{G}_T$)
2. Compute $T_{const}^\rho$ without a $\mathbb{G}_T$-exponentiation oracle for $\rho$

To forge a proof, the adversary must produce $C \in \mathbb{G}_1$ such that:
$$e(A, B) = T_{const}^\rho \cdot e(C, \delta)$$

This requires computing $T_{const}^\rho$ or an equivalent, which is exactly the GT-XPDH problem: given $\mathbb{G}_T$ projections of polynomials outside the $\mathbb{G}_1$ span, compute their $\rho$-exponent.

**Connection to TEP:**
The Target Exponent Problem is the "search" version: given the target $T_{const}$, find exponents $(a, b)$ such that $e([a]_1, [b]_2) = T_{const}$. Our construction ensures:
- The adversary cannot find such $(a, b)$ without knowing $Q_{const}(\tau)$
- $Q_{const}(\tau)$ is not computable from the Lean CRS

**Theorem**: If $\mathcal{A}$ can forge a Lean proof with advantage $\epsilon$, we can solve GT-XPDH with advantage $\epsilon / \text{poly}(\lambda)$.

### 4.5 Why Affine Quotient Correction is Critical

The affine structure $Q_{const}(x) = q_0 + q_1 \cdot x$ is essential:

| Property | Security Implication |
|----------|---------------------|
| 2-dimensional secret space | Minimal polynomial to hide outside CRS span |
| Linear in $x$ | Statement-dependent, witness-independent |
| Determined by 2 samples | Setup computes $q_0, q_1$ from probes at $x=0, x=1$ |
| Outside adversary span | GT-XPDH-hard to compute target without bases |

If the quotient correction were **non-affine** (e.g., $q_0 + q_1 x + q_2 x^2$):
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
"Compute Q_const(τ)"      →   IMPOSSIBLE (no basis)
```

The adversary never queries the "missing" $Q_{const}$ bases because they're not in the Lean CRS. The simulation is **perfect** for all polynomial-time adversaries.

## 5. Outer Circuit Linearity Requirement

For the DDH reduction to hold, the outer circuit must satisfy:

### 5.1 Constraint Structure

| Constraint Type | A-column | B-column | Captured By |
|-----------------|----------|----------|-------------|
| **Public binding** | $1$ | reconstructed (witness LC) | $x_{pub}$ |
| Witness × Witness | $w_i$ | $w_j$ | $h_{query\_wit}$ |
| Constant × Witness | $1$ | $w_j$ | $h_{query\_wit}$ |

**Critical Invariant**: No constraint places a public input in A or B. Public inputs appear **only** in C.

### 5.2 Statement Dependency Requirement

For the derived key $K = R^\rho$ to be **statement-dependent** (binding the arming randomness $\rho$ to the specific public input $x$), statement binding is through the **Groth16 target** $R(vk, x)$.

*   **Constraint**: `1 * reconstructed = x_pub` places $x$ in the **C-matrix** only.
*   **Effect**: $v_{pub} = 0$, $u_{pub} = 0$, $w_{pub} \neq 0$.
*   **Statement Binding**: Via $IC_i = w_i/\gamma$ in the Groth16 target:
    $$R(vk, x) = e([\alpha]_1, [\beta]_2) \cdot e(L(x), [\gamma]_2) \cdot T_{const}(x)$$
    where $L(x) = \sum x_i \cdot IC_i$ and $IC_i = (\beta u_i + \alpha v_i + w_i)/\gamma = w_i/\gamma$ (since $u_i = v_i = 0$).
*   **Key**: $K(x) = R(vk, x)^\rho$. Different statements yield different $L(x)$, hence different $R$, hence different $K$.
*   **Security Benefit**: Eliminates the $\alpha \cdot V_{pub}$ pollution term; V-span becomes trivially satisfied.

## 6. Conclusion

The algebraic framework confirms that PVUGC is secure in the AGBGM when the following minimum defenses are in place:

### 6.1 Minimum Required Defenses

| Defense | Purpose | Blocks |
|---------|---------|--------|
| **W-Span Separation** | $W_{pub} \perp W_{wit}$ | Residue synthesis attack |
| **Lean CRS (Baked Quotient)** | Quotient in $\mathbb{G}_T$ only; no PoT | Quotient forgery in $\mathbb{G}_1$ |
| **Linear Circuit Design** | Public inputs appear linearly | Non-linear quotient terms |
| **Span Membership** | $Q_{const} \notin \text{span}(H_{ij})$ | Baked quotient synthesis |

**Note:** U-span and V-span separation are trivially satisfied ($u_{pub} = v_{pub} = 0$) and need not be explicitly verified.

**Span Membership Sufficient Condition:** The audit check "$u_{pub}=0$, $v_{pub}=0$, and $\text{rows}(C_{pub}) \cap \text{rows}(C_{wit}) = \emptyset$" is a **sufficient condition** implying $Q_{const} \notin \text{span}(H_{ij})$. This becomes if-and-only-if under the assumption that $H_{ij}$ bases are constructed solely from $(const, wit)$ and $(wit, wit)$ pairs with no shared Lagrange indices.

### 6.2 Security Properties Achieved

1. **Standard Groth16 Algebra** — No complex modifications needed; $[\alpha]_1$ can remain public
2. **Proof-Agnostic Decapsulation** — Any valid proof yields the same $K = R^\rho$
3. **Statement-Dependent Keys** — Different $(vk, x)$ pairs yield different keys via $IC_i = w_i/\gamma$
4. **GT-XPDH Hardness** — Reduces to DDH in $\mathbb{G}_2$ (standard assumption)
5. **Simplified Attack Surface** — No $\alpha \cdot V_{pub}$ pollution term (V-span trivial)

The combination of these defenses eliminates all known algebraic attack vectors and reduces security to the hardness of **GT-XPDH** in the Generic Bilinear Group Model.

### 6.3 Assumption Hierarchy

```
                    GBGM (Generic Bilinear Group Model)
                              ↓ implies
                    GT-XPDH (Target Group XPDH)
                              ↓ tight reduction to
                    DDH in G₂ (SXDH suffices)
```

In the **standard model** (non-generic), security relies on:
- **SXDH**: DDH hardness in both $\mathbb{G}_1$ and $\mathbb{G}_2$ (only $\mathbb{G}_2$-half needed)
- **Groth16 Knowledge Soundness**: Valid proofs only from witness knowledge
- **Collision Resistance**: SHA-256 for Fiat-Shamir

The GBGM provides the cleanest reduction with bound $\tilde{O}(q^2/r)$ for $q$ oracle queries. See `gt-xpdh-reduction.md` for the full proof.
