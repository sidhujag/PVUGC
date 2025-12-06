# PVUGC Security Analysis: Algebraic Framework & GBGM Model

This document defines the algebraic framework used to prove the security of PVUGC's One-Sided Decapsulation logic. Security rests on four pillars:

1. **Full Span Separation** — $U_{pub} \perp U_{wit}$, $V_{pub} \perp V_{wit}$, $W_{pub} \perp W_{wit}$ (verified by circuit audit)
2. **Lean CRS** — No Powers of Tau; public quotient baked into $\mathbb{G}_T$
3. **Linear Circuit Design** — Public inputs appear only linearly (no pub×pub or pub×wit constraints)
4. **Aggregated Armed Handle** — Public B-columns aggregated into single armed handle $D_{pub} = \rho(\beta + \sum x_i v_i(\tau))$

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
    *   $\mathbb{G}_T$ — GT-baked public quotient evaluations
        *   $T_i = e(H_i(\tau), \delta)$ for $0 \le i \le \ell$, where $H_{pub}(x,\tau) = \sum_{i=0}^{\ell} x_i H_i(\tau)$
        *   $T_{const}(x) = e(H_{pub}(x,\tau), \delta) = \prod_{i=0}^{\ell} T_i^{x_i}$ is publicly computable in $\mathbb{G}_T$
*   **Explicit Exclusions (Lean CRS):**
    *   No clean polynomial bases for public columns (only witness-column $A_k/B_k$ are published); no stand-alone Powers-of-$\tau$ ladder
    *   No public-only $H$ bases in $\mathbb{G}_1$ (the constant quotient polynomials $H_i(\tau)$ never appear as $\mathbb{G}_1$ handles)
    *   No armed $[\gamma]_2^\rho$, $[1]_2^\rho$, or $[H(\tau)]_2^\rho$
*   **Arming Instance (masked by $\rho$):**
    *   $D_{pub} = \rho \cdot (\beta + \sum_{i=0}^\ell x_i v_i(\tau))$
    *   $D_\delta = \rho \cdot \delta$
    *   $D_j = \rho \cdot v_j(\tau)$ for all witness columns $j > \ell$

Even though the Lean CRS exposes clean witness-column bases ($A_k$, $B_k$), they span only the witness subspace. Because public-only $H$ bases and Powers-of-$\tau$ elements are withheld, and because the circuit is audited to keep public columns linear, those witness handles remain orthogonal to the baked public quotient. This is the core "span separation" analyzed in §2.1 and §2.3.

### 1.2 Adversary Capabilities
The adversary can construct new handles via:
1.  **Linear Combination:** Given handles $h_1, h_2$, compute $c_1 h_1 + c_2 h_2$. Label: $c_1 L(h_1) + c_2 L(h_2)$.
2.  **Pairing:** Given $h_1 \in \mathbb{G}_1, h_2 \in \mathbb{G}_2$, compute $e(h_1, h_2)$. Label: $L(h_1) \cdot L(h_2)$.

**Goal:** Construct a handle with label equal to the Target Label. In standard Groth16 R1CS notation:
$$ L(K_{core}) = \rho\alpha\beta + \rho(\beta U_{pub} + \alpha V_{pub} + W_{pub}) $$

where $U_{pub}, V_{pub}, W_{pub}$ are the public-input contributions to the A, B, C polynomials respectively. The Lean CRS bakes the public quotient into $\mathbb{G}_T$, so the effective target becomes:
$$ L_{Target} = \rho \cdot \left(\alpha\beta + \beta U_{pub} + \alpha V_{pub} + W_{pub} + H_{pub}\delta\right) $$

**Why [α]₁ can be public:** Even though the adversary has $[\alpha]_1$, they cannot extract $K_{core}$ because:
- Pairing $[\alpha]_1$ with armed bases yields terms like $\rho\alpha V_{wit}$
- V-span separation ($V_{pub} \perp V_{wit}$) prevents canceling the $\rho\alpha V_{pub}$ pollution
- Similarly, U/W-span separation blocks residue synthesis attacks

## 2. Security Invariants (The "Impossibility" Proofs)

We argue security entirely inside the Algebraic Generic Bilinear Group Model. A WE adversary may issue arbitrary linear-combination and pairing queries—it is not constrained to produce Groth16-style $(A,B,C)$ tuples. Security holds because the Target Label lies outside the algebraic span reachable from the Lean CRS handles.

### 2.1 Attack Vector Analysis

There are two primary algebraic attack strategies:

**Attack A: Pollution Cancellation (V-Span Attack)**
- The adversary uses public $[\alpha]_1$ to compute $H_\alpha = e([\alpha]_1, D_{pub})$ (where $D_{pub}$ is already $\rho$-masked)
- This yields $L(H_\alpha) = \rho\alpha\beta + \rho\alpha V_{pub}$
- To isolate $\rho\alpha\beta$, adversary must cancel the "pollution" term $\rho\alpha V_{pub}$
- Available witness handles can only generate $\rho\alpha V_{wit}$
- **Defense:** V-span separation ($V_{pub} \perp V_{wit}$) blocks this attack

**Attack B: Residue Synthesis (U/W-Span Attack)**
- The adversary tries to synthesize the remaining components: $Residue = \rho(\beta U_{pub} + W_{pub})$
- Available witness handles generate only $\rho\beta U_{wit}$ and $\rho W_{wit}$
- **Defense:** U-span separation ($U_{pub} \perp U_{wit}$) and W-span separation ($W_{pub} \perp W_{wit}$) block this attack

### 2.2 The Gamma Invariant (Supplementary Barrier)
**Claim:** (Supplementary) The adversary cannot construct the term $\rho \cdot \gamma \cdot IC(x)$ without satisfying the R1CS. This barrier is not relied upon for the main span-separation argument but provides additional algebraic separation.

**Proof (degree argument):**

We track the degrees of the independent indeterminates $\rho$ (arming secret) and $\gamma$ (Groth16 trapdoor) inside every handle. Although the baked target used in PVUGC involves only $\rho$ (the $\gamma$ factors cancel for honest users), it is useful to note that any adversarial attempt to recreate a $\rho \cdot \gamma$ term—by arming the IC bases themselves—fails for algebraic reasons.

| Handle Type | Group | $Deg_\rho$ | $Deg_\gamma$ | Notes |
|-------------|:-----:|:----------:|:------------:|-------|
| $A_k$, $L_k$, $H_{wit}$ | $\mathbb{G}_1$ | 0 | 0 | witness-column bases (no $\gamma$ factor) |
| $IC_i$ | $\mathbb{G}_1$ | 0 | -1 | only source with $\gamma^{-1}$ |
| VK constants $[\beta]_2, [\gamma]_2, [\delta]_2$ | $\mathbb{G}_2$ | 0 | $\le 1$ | unarmed |
| Armed handles $D_{pub}, D_\delta, D_j$ | $\mathbb{G}_2$ | 1 | 0 | carry $\rho$, never $\gamma$ |

When the adversary forms a pairing $E = e(H_1, H_2)$, the degrees add:

1. If $H_2$ is armed ($Deg_\rho = 1$), then $Deg_\gamma(E) = Deg_\gamma(H_1) \le 0$ because no $\mathbb{G}_1$ handle has positive $\gamma$ degree.
2. If $H_2$ is unarmed ($Deg_\rho = 0$), then $Deg_\rho(E) = Deg_\rho(H_1) = 0$.

Thus no pairing (nor any linear combination thereof) can yield a handle with $Deg_\rho = 1$ **and** $Deg_\gamma = 1$. Even if an adversary tried to arm the IC bases directly, the $\rho \cdot \gamma$ monomial would remain algebraically unreachable.

### 2.3 Full Span Separation (Primary Defense)
**Claim:** The adversary cannot forge the public residual using witness handles because the public and witness subspaces are orthogonal.

**The Three Span Separations:**

| Matrix | Separation | Blocks |
|--------|------------|--------|
| U (A-matrix) | $U_{pub} \perp U_{wit}$ | Residue synthesis via A-queries |
| V (B-matrix) | $V_{pub} \perp V_{wit}$ | Pollution cancellation via B-columns |
| W (C-matrix) | $W_{pub} \perp W_{wit}$ | Residue synthesis via C-queries |

**Proof:**
- The adversary has witness handles $A_k$, $B_k$, $L_k$, $H_{wit}$, and armed $D_j$—all tied solely to witness columns
- The **Circuit Audit** verifies that no pub×pub or pub×wit constraints exist
- Therefore, no linear combination of witness handles can produce public-input-dependent terms
- Result: Both Pollution Cancellation and Residue Synthesis attacks are blocked

### 2.4 The Baked Quotient Invariant (Blocks Quotient Forging)
**Claim:** The adversary cannot use the CRS to forge the quotient polynomial $H_{pub}(x)$ or its armed equivalent.

*   **What the Adversary CAN Do:**
    *   The adversary **can** compute $T_{const}(x) = \prod_{i=0}^{\ell} T_i^{x_i}$ in $\mathbb{G}_T$ from the public GT-baked handles $T_i$ and the public inputs $x_i$.

*   **What the Adversary CANNOT Do:**
    *   They have **no $\mathbb{G}_1$ handle** for $H_{pub}(x,\tau)$: the public $H$-bases are missing from the $\mathbb{G}_1$ span (Lean CRS explicitly excludes them).
    *   They have **no way to apply $\rho$ inside $\mathbb{G}_T$**: the only source of $\rho$ is in the armed $\mathbb{G}_2$ handles, and pairing is $\mathbb{G}_1 \times \mathbb{G}_2 \to \mathbb{G}_T$. There is no operation that takes a $\mathbb{G}_T$ element and multiplies it by $\rho$.

*   **Conclusion:** The adversary cannot synthesize $[H_{pub}(x,\tau)]_1$ in $\mathbb{G}_1$, nor can they compute $T_{const}(x)^\rho$ from their handle set. The armed target remains unreachable.

## 3. Completeness for Honest Prover

The "Honest Prover Dilemma" (Prover needs handles that Adversary abuses) is resolved by the **Linearity Assumption**.

*   Since the Public Inputs interact only linearly in the circuit, the quotient polynomial separates: $H(x) = H_{const} + H_{wit}(w)$.
*   We **bake** $H_{const}$ into the target (removing the need to construct it).
*   We **publish** handles only for $H_{wit}(w)$.
*   The adversary gets no "Dangerous" handles (handles that depend on public inputs).
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

1. **Missing $\mathbb{G}_1$ Bases**: The Lean CRS excludes $H_{pub}$ bases $\{[H_i(\tau)]_1\}$ for public-input-dependent quotient terms
2. **GT-Baked Projections Only**: The adversary receives only $\mathbb{G}_T$ projections $T_i = e(H_i(\tau), \delta)$, not the underlying $\mathbb{G}_1$ elements
3. **Algebraic Consistency**: All queries return answers consistent with the algebraic structure
4. **No $\rho$-Scaling in $\mathbb{G}_T$**: There is no operation to multiply a $\mathbb{G}_T$ element by the arming secret $\rho$

**Adversary's View:**
- Lean CRS in $\mathbb{G}_1$: witness-only bases (no $H_{pub}$ bases)
- $\mathbb{G}_2$ VK: includes $[\delta]_2$
- $\mathbb{G}_T$ handles: $T_i = e(H_i(\tau), \delta)$ for $0 \le i \le \ell$

**Key Insight**: The adversary's reachable span is:
$$\text{Span}_{adv} = \text{LinComb}(\text{Lean CRS}) + \text{Pairings}(\text{Lean CRS})$$

The *polynomial* $f(\tau) = H_{pub}(x,\tau)$ underlying $T_{baked} = e(f(\tau), \delta)$ is still outside the $\mathbb{G}_1$ span. Even though $T_{baked}$ itself is computable in $\mathbb{G}_T$, the adversary cannot compute $T_{baked}^\rho$ because $\rho$ only appears in armed $\mathbb{G}_2$ handles.

### 4.4 The GT-XPDH / TEP Reduction

Our setting maps directly to **GT-XPDH**:

**The Challenge:**
- Adversary has Lean CRS: $\{[\tau^i]_1\}_{i \in \text{Lean}}$ (no $H_{pub}$ bases), $[\delta]_2$
- Adversary has GT-baked handles: $T_i = e(H_i(\tau), \delta)$ for $0 \le i \le \ell$
- Target: $T_{baked}^\rho$ where $T_{baked} = e([H_{pub}(x,\tau)]_1, [\delta]_2)$
- $H_{pub}(x,\tau)$ is **outside** the $\mathbb{G}_1$ span of Lean CRS elements

**Why GT-XPDH Applies:**
The polynomial $f(\tau) = H_{pub}(x,\tau)$ represents the public-input-dependent quotient. The Lean CRS deliberately excludes the $\mathbb{G}_1$ bases needed to compute $[f(\tau)]_1$. The adversary can compute $T_{baked} = e(f(\tau), \delta)$ from the GT-baked handles, but cannot:
1. Extract $[f(\tau)]_1$ from $T_{baked}$ (discrete log in $\mathbb{G}_T$)
2. Compute $T_{baked}^\rho$ without a $\mathbb{G}_T$-exponentiation oracle for $\rho$

To forge a proof, the adversary must produce $C \in \mathbb{G}_1$ such that:
$$e(A, B) = T_{baked}^\rho + e(C, \delta)$$

This requires computing $T_{baked}^\rho$ or an equivalent, which is exactly the GT-XPDH problem: given $\mathbb{G}_T$ projections of polynomials outside the $\mathbb{G}_1$ span, compute their $\rho$-exponent.

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
| Linear packing | $x - \Sigma 2^i b_i$ | $1$ | $q_{const}$ (baked) |
| Witness × Witness | $w_i$ | $w_j$ | $h_{query\_wit}$ |
| VK × Proof | constant | witness | $h_{query\_wit}$ |

**Critical Invariant**: No constraint has public input $x$ in **both** A and B columns.

### 5.2 Statement Dependency Requirement

For the derived key $K = R^\rho$ to be **statement-dependent** (binding the arming randomness $\rho$ to the specific public input $x$), the public input MUST appear in the B-matrix of the constraint system.

*   **Requirement**: The constraint $1 \cdot x = x$ (or equivalent) must place $x$ in the B-matrix column.
*   **Effect**: The B-polynomial becomes $B(x) = \beta + x \cdot v_{pub}(\tau)$. The armed handle becomes $D_{pub} = \rho \cdot B(x)$.
*   **Security**: The key becomes $K(x) = e(A, D_{pub}) = e(A, \beta)^\rho \cdot e(A, v_{pub})^{\rho \cdot x}$. This binds $\rho$ to $x$ multiplicatively in the exponent.
*   **Vulnerability (Avoided)**: If $x$ appears *only* in C (e.g., via $1 \cdot 0 = x$), then $B(x) = \beta$ (constant). The armed handle $D_{pub} = \rho \beta$ yields a constant key $K = e(A, \beta)^\rho$ valid for *any* statement, breaking the KEM property.
*   **Exclusion**: Public inputs MUST NOT appear in the A-matrix to prevent adversary manipulation of the A-side pairing input. The outer circuit enforces this (see `bin/audit_circuit.rs`).

## 6. Conclusion

The algebraic framework confirms that PVUGC is secure in the AGBGM when the following minimum defenses are in place:

### 6.1 Minimum Required Defenses

| Defense | Purpose | Blocks |
|---------|---------|--------|
| **Full Span Separation** | $U/V/W_{pub} \perp U/V/W_{wit}$ | Pollution cancellation, residue synthesis |
| **Lean CRS (Baked Quotient)** | No PoT; public quotient in $\mathbb{G}_T$ only | Quotient forgery |
| **Linear Circuit Design** | Public inputs appear linearly | Quotient non-separation |
| **Aggregated Armed Handle** | $D_{pub} = \rho(\beta + \sum x_i v_i)$ | GT-slicing attacks |

### 6.2 Security Properties Achieved

1. **Standard Groth16 Algebra** — No complex modifications needed; $[\alpha]_1$ can remain public
2. **Proof-Agnostic Decapsulation** — Any valid proof yields the same $K = R^\rho$
3. **Statement-Dependent Keys** — Different $(vk, x)$ pairs yield different keys
4. **GT-XPDH Hardness** — Reduces to DDH in $\mathbb{G}_2$ (standard assumption)

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
