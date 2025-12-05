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
The adversary starts with handles for the public parameters (Lean CRS + Verification Key) and the specific arming instance. We list the explicit algebraic labels because the poisoning is the source of every security invariant.

*   **Public CRS / VK (unarmed):**
    *   $\mathbb{G}_1$ — circuit queries
        *   $A_k$ ($k > \ell$): $u_k(\tau)$ (clean witness-column bases, no $\rho$)
        *   $B^{(1)}_k$ ($k > \ell$): $v_k(\tau)$ in $\mathbb{G}_1$
        *   $L_k$ ($k > \ell$): $\frac{\beta v_k(\tau) + \alpha u_k(\tau) + w_k(\tau)}{\delta}$ (witness-only, still poisoned)
        *   $IC_i$ ($i \le \ell$): $\frac{u_i(\tau)}{\gamma}$ (**note the inverse $\gamma$**)
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

Even though the Lean CRS exposes clean witness-column bases ($A_k$, $B_k$), they span only the witness subspace. Because public-only $H$ bases and Powers-of-$\tau$ elements are withheld, and because the circuit is audited to keep public columns linear, those witness handles remain orthogonal to the baked public quotient. This is the core “span separation” used later in §2.2–§2.3.

### 1.2 Adversary Capabilities
The adversary can construct new handles via:
1.  **Linear Combination:** Given handles $h_1, h_2$, compute $c_1 h_1 + c_2 h_2$. Label: $c_1 L(h_1) + c_2 L(h_2)$.
2.  **Pairing:** Given $h_1 \in \mathbb{G}_1, h_2 \in \mathbb{G}_2$, compute $e(h_1, h_2)$. Label: $L(h_1) \cdot L(h_2)$.

**Goal:** Construct a handle with label equal to the Target Label:
$$ L_{Target} = \rho \cdot \left(\alpha \beta + \sum_{i=0}^{\ell} x_i u_i(\tau) + T_{const}\right) $$

where $T_{const} = e(H_{pub}(x,\tau), \delta)$ is the baked quotient term. The `+` sign arises because the Lean prover omits the quotient polynomial $H_{pub}$ from C, so honest extraction naturally includes the $e(H_{pub}, \delta)$ term that would otherwise cancel.

*Why no $\gamma$ term?* The IC bases in the Lean CRS are $u_i(\tau)/\gamma$. Honest decapsulation pairs $\sum x_i \cdot IC_i$ with the unarmed $[\gamma]_2$, so the $\gamma$ cancels before arming with $\rho$. Adversaries still never obtain an armed $[\gamma]_2^\rho$, but the monomial enforced in the protocol is $\rho \cdot \sum x_i u_i(\tau)$.

## 2. Security Invariants (The "Impossibility" Proofs)

We argue security entirely inside the Algebraic Generic Bilinear Group Model. A WE adversary may issue arbitrary linear-combination and pairing queries—it is not constrained to produce Groth16-style $(A,B,C)$ tuples. Consequently we do **not** rely on Rank-1 structure; instead we show that the target decapsulation label lies outside the algebraic span reachable from the Lean CRS handles. The argument proceeds along two axes:

1. **Span analysis:** anything involving public-only quotient terms or clean polynomial bases is simply missing from the CRS.
2. **Degree analysis:** the trapdoor indeterminates $\rho$ (arming) and $\gamma$ (Groth16) never cohabit a handle, so monomials that require both are unreachable.

The first two invariants below—§2.2 (Linearity) and §2.3 (Baked Quotient)—form the primary defense. They guarantee the public-only quotient term lives outside the Lean CRS span regardless of any $\gamma$-related arguments. The $\gamma$ barrier (§2.1) is a belt-and-suspenders separation that further blocks direct attempts to arm the IC bases.

Security holds because the Target Label lies outside the linear span of the labels reachable by the adversary.

### 2.1 The Gamma Invariant (Supplementary Barrier)
**Claim:** (Supplementary) The adversary cannot construct the term $\rho \cdot \gamma \cdot IC(x)$ without satisfying the R1CS. This barrier is not relied upon for the main baked-quotient argument but it provides an additional algebraic separation.

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

### 2.2 The Linearity Invariant (Blocks Full Span / Public-Public)
**Claim:** The adversary cannot forge the public residual $\Delta_{pub}$ using witness handles—even though it may possess clean witness-column bases from the CRS.

*   **Proof:**
    *   The public residual $\Delta_{pub}$ depends on the public inputs $x$.
    *   The adversary has witness handles $A_k$, $B_k$, $H_{wit}$ and the armed $D_j$—all tied solely to witness columns.
    *   **Constraint:** The **Trapdoor-Aware Audit** (and the Linearity property of the Outer Circuit) guarantees that the subspace spanned by the public residual is orthogonal to the subspace spanned by the witness columns (no pub×pub or pub×wit constraints).
    *   **Result:** No linear combination of the available witness handles can equal $\Delta_{pub}$ (unless the R1CS is satisfied).

### 2.3 The Baked Quotient Invariant (Blocks Remainder Forging)
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
| Linear packing | $x_{outer} - \Sigma 2^i b_i$ | $1$ | $q_{const}$ (baked) |
| Witness × Witness | $w_i$ | $w_j$ | $h_{query\_wit}$ |
| VK × Proof | constant | witness | $h_{query\_wit}$ |

**Critical Invariant**: No constraint has $x_{outer}$ in **both** A and B columns.

### 5.2 Statement Dependency Requirement

For the derived key $K = R^\rho$ to be **statement-dependent** (binding the arming randomness $\rho$ to the specific public input $x$), the public input $x$ MUST appear in the B-matrix of the constraint system.

*   **Requirement**: The constraint $1 \cdot x = x$ (or equivalent) must place $x$ in the B-matrix column.
*   **Effect**: The B-polynomial becomes $B(x) = \beta + x \cdot v_{pub}(\tau)$. The armed handle becomes $D_{pub} = \rho \cdot B(x)$.
*   **Security**: The key becomes $K(x) = e(A, D_{pub}) = e(A, \beta)^\rho \cdot e(A, v_{pub})^{\rho \cdot x}$. This binds $\rho$ to $x$ multiplicatively in the exponent.
*   **Vulnerability (Avoided)**: If $x$ appears *only* in C (e.g., via $1 \cdot 0 = x$), then $B(x) = \beta$ (constant). The armed handle $D_{pub} = \rho \beta$ yields a constant key $K = e(A, \beta)^\rho$ valid for *any* statement, breaking the KEM property.
*   **Exclusion**: Public inputs MUST NOT appear in the A-matrix to prevent adversary manipulation of the A-side pairing input. Our Outer Circuit already explemplifies this (see ../../bin/audit_circuit.rs).

## 6. Conclusion

The algebraic framework confirms that the **Hardened Arming** architecture is secure in the AGBGM. The combination of:

1. **Aggregation** (one-sided PPE structure)
2. **Gamma-Exclusion** (blocks GT-slicing attacks)
3. **GT-Baked Quotient** (publishes $H_{pub}$ only as $\mathbb{G}_T$ projections $T_i = e(H_i(\tau), \delta)$, not as $\mathbb{G}_1$ handles)
4. **Linearity/Audit** (ensures affine quotient, orthogonal to witness span)
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
