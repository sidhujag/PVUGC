# PVUGC Security Analysis: Algebraic Framework & GBGM Model

This document defines the algebraic framework used to prove the security of PVUGC's One-Sided Decapsulation logic. Security rests on four pillars:

1. **W-Span Separation** — $W_{pub} \perp W_{wit}$ (verified by circuit audit; U/V-span trivially satisfied)
2. **Lean CRS** — No Powers of Tau; baked quotient $Q_{const}$ in $G_T$ only
3. **Linear Circuit Design** — No constraint places a public input in A or B
4. **Public Inputs in C-Matrix** — Statement binding via W-polynomial ($IC_i = w_i/\gamma$)

**Notation:** We write the group law in $G_T$ multiplicatively. The target is:

$$R_{baked}(vk, x) = e(\alpha_1, \beta_2) \cdot e(IC(x), \gamma_2) \cdot T_{const}(x)$$

where $T_{const}(x) = \prod_i T_i^{x_i} = e(Q_{const}(x), \delta_2)$ is the baked quotient correction.

**Architecture:** Public inputs are bound in the C-matrix only ($v_{pub} = 0$, $u_{pub} = 0$). This:
- Eliminates $(wit,pub)$ cross-terms in the quotient
- Makes U-span and V-span separation trivially satisfied
- Shifts statement binding to the W-polynomial via $IC_i = w_i/\gamma$

## 1. The Algebraic Model (AGBGM)

We work in the Algebraic Generic Bilinear Group Model (AGBGM). The adversary interacts with a system of oracles representing the group operations in $G_1, G_2, G_T$ and the bilinear pairing $e: G_1 \times G_2 \to G_T$.

### 1.1 Handles and Labels
Every group element $g$ held by the adversary is represented by a handle. Internally, the oracle maintains a mapping from handles to **Algebraic Labels**, which are multivariate polynomials over the finite field $F_r$ in the formal indeterminates representing the secret trapdoors.

**Trapdoor Indeterminates:**
*   $\alpha$, $\beta$, $\gamma$, $\delta$: The Groth16 secrets.
*   $\tau$: The structured reference string (SRS) parameter.
*   $\rho$: The fresh arming randomness (per instance).

<a id="basis-handles"></a>
**Available Handles (The Basis):**
The adversary starts with handles for the public parameters (Lean CRS + Verification Key) and the specific arming instance. We list the explicit algebraic labels because the poisoning is the source of every security invariant.

<a id="g1-bases"></a>
*   **Public CRS / VK (unarmed):**
    *   $G_1$ — circuit queries
        *   $A_k$ ($k > \ell$): $u_k(\tau)$ (clean witness-column bases, no $\rho$)
        *   $B_k^{(1)}$ ($k > \ell$): $v_k(\tau)$ in $G_1$
        *   $L_k$ ($k > \ell$): $\frac{\beta u_k(\tau) + \alpha v_k(\tau) + w_k(\tau)}{\delta}$ (witness-only, poisoned by $\alpha$, $\beta$, $\delta^{-1}$)
        *   $IC_i$ ($i \le \ell$): $\frac{\beta u_i(\tau) + \alpha v_i(\tau) + w_i(\tau)}{\gamma}$ (public-input coefficients, poisoned by $\gamma^{-1}$)
        *   $H_{wit}$: $H_{i,j}(\tau)$ where at least one of $i,j$ indexes a witness column
        *   $\alpha_1$: $\alpha$ (Groth16 trapdoor; public VK element)
    *   $G_2$ — verification key elements
        *   $\beta_2$, $\gamma_2$, $\delta_2$
        *   $B_k^{(2)} = v_k(\tau)$ in $G_2$ (clean, unmasked)
<a id="gt-bases"></a>
    *   $G_T$ — GT-baked public quotient correction
        *   $T_i = e(Q_i(\tau), \delta)$ for $0 \le i \le \ell$, where $Q_{const}(x,\tau) = \sum_{i=0}^{\ell} x_i Q_i(\tau)$
        *   $T_{const}(x) = e(Q_{const}(x,\tau), \delta) = \prod_{i=0}^{\ell} T_i^{x_i}$ is publicly computable in $G_T$
        *   Note: $Q_{const}$ is the gap between standard and lean proofs, not the full quotient polynomial
<a id="explicit-exclusions"></a>
*   **Explicit Exclusions (Lean CRS):**
    *   No clean polynomial bases for public columns (only witness-column $A_k/B_k$ are published); no stand-alone Powers of Tau ladder
    *   No public-only $H$ bases in $G_1$ (the constant quotient polynomials $H_i(\tau)$ never appear as $G_1$ handles)
    *   No armed $\gamma_2^\rho$, $1_2^\rho$, or $H(\tau)_2^\rho$
<a id="arming-instance"></a>
*   **Arming Instance (masked by $\rho$):**
    *   $\beta_2^\rho = \rho \cdot \beta$ (constant; $v_{pub} = 0$ means no public B-columns to aggregate)
    *   $\delta_2^\rho = \rho \cdot \delta$
    *   $v_j(\tau)_2^\rho = \rho \cdot v_j(\tau)$ for all witness columns $j > \ell$

Even though the Lean CRS exposes clean witness-column bases ($A_k$, $B_k$), they span only the witness subspace. Because public-only $H$ bases and Powers of Tau elements are withheld, and because the circuit is audited to keep public columns linear, those witness handles remain orthogonal to the baked public quotient. This is the core "span separation" analyzed in [§2.1](#21-attack-vector-analysis) and [§2.3](#23-full-span-separation-primary-defense).

### 1.2 Adversary Capabilities
The adversary can construct new handles via:
1.  **Linear Combination:** Given handles $h_1, h_2$, compute $c_1 h_1 + c_2 h_2$. Label: $c_1 L(h_1) + c_2 L(h_2)$.
2.  **Pairing:** Given $h_1 \in G_1, h_2 \in G_2$, compute $e(h_1, h_2)$. Label: $L(h_1) \cdot L(h_2)$.

<a id="target-label"></a>
**Goal:** Construct a handle with label equal to the Target Label. With $u_{pub} = v_{pub} = 0$:

$$L(K_{core}) = \rho \cdot (\alpha\beta + W_{pub})$$

where $W_{pub}$ is the public-input contribution to the C-polynomial (since $U_{pub} = V_{pub} = 0$). The Lean CRS bakes the public quotient correction into $G_T$, so the effective baked target becomes:

$$L_{Target} = \rho \cdot (\alpha\beta + W_{pub} + Q_{const}\delta)$$

<a id="groth16-equation"></a>
where $Q_{const}(x)$ is the affine correction computed from the gap between standard and lean proofs. Concretely, under the Groth16 equation

$$e(A, B) = e(\alpha_1, \beta_2) \cdot e(IC(x), \gamma_2) \cdot e(H(x,w), \delta_2)$$

<a id="quotient-decomposition"></a>
and the decomposition $H(x,w) = Q_{const}(x) + H_{wit}(w)$, arming the $B$- and $\delta_2$-handles multiplies this target by $\rho$, so the algebraic label of the armed target is exactly $L_{Target}$ as written above.

**Why $\alpha_1$ can be public:** Even though the adversary has $\alpha_1$, they cannot extract $K_{core}$ because:
- With $v_{pub} = 0$, pairing $\alpha_1$ with armed B-handles yields no statement-dependent pollution
- The adversary cannot synthesize $\rho W_{pub}$ from witness handles (blocked by W-span separation)
- Statement binding is through $R(vk, x)$ via $IC_i = w_i/\gamma$, not through armed B-handles

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
- The baked quotient $T_{const}$ encodes $W_{pub}/Z$ in $G_T$
- Since $u_{pub} = v_{pub} = 0$, $H_{ij}$ only encodes $(U_{wit} \cdot V_{wit})/Z$
- **Blocked by:** Span membership check ($Q_{const}$ not in span($H_{ij}$), verified by audit)

**Note:** With $v_{pub} = 0$, pairing $\alpha_1$ with any armed B-handle yields no statement-dependent "pollution" term. This eliminates the classic V-span attack vector entirely by architectural design.

### 2.2 The Gamma Invariant (Supplementary Barrier)
**Claim:** (Supplementary) The adversary cannot construct the term $\rho \cdot \gamma \cdot IC(x)$ without satisfying the R1CS. This barrier is not relied upon for the main span-separation argument but provides additional algebraic separation.

**Proof (degree argument):**

We track the degrees of the independent indeterminates $\rho$ (arming secret) and $\gamma$ (Groth16 trapdoor) inside every handle. Although the baked target used in PVUGC involves only $\rho$ (the $\gamma$ factors cancel for honest users), it is useful to note that any adversarial attempt to recreate a $\rho \cdot \gamma$ term—by arming the IC bases themselves—fails for algebraic reasons.

| Handle Type | Group | $Deg_\rho$ | $Deg_\gamma$ | Notes |
|-------------|:-----:|:----------:|:------------:|-------|
| $A_k$, $L_k$, $H_{wit}$ | $G_1$ | 0 | 0 | witness-column bases (no $\gamma$ factor) |
| $IC_i$ | $G_1$ | 0 | -1 | only source with $\gamma^{-1}$ |
| VK constants $\beta_2$, $\gamma_2$, $\delta_2$ | $G_2$ | 0 | ≤ 1 | unarmed |
| Armed handles $\beta_2^\rho$, $\delta_2^\rho$, $v_{j,2}^\rho$ | $G_2$ | 1 | 0 | carry $\rho$, never $\gamma$ |

Recall from the **[Explicit Exclusions (Lean CRS)](#explicit-exclusions)** above that there are no armed $G_2$ handles involving $\gamma$ (no $\gamma_2^\rho$); the only source of non-zero $\gamma$-degree is the unarmed $IC_i$ with $Deg_\gamma = -1$.

When the adversary forms a pairing $E = e(H_1, H_2)$, the degrees add:

1. If $H_2$ is armed ($Deg_\rho = 1$), then $Deg_\gamma(E) = Deg_\gamma(H_1) \le 0$ because no $G_1$ handle has positive $\gamma$ degree.
2. If $H_2$ is unarmed ($Deg_\rho = 0$), then $Deg_\rho(E) = Deg_\rho(H_1) = 0$.

Thus no pairing (nor any linear combination thereof) can yield a handle with $Deg_\rho = 1$ **and** $Deg_\gamma = 1$. Even if an adversary tried to arm the IC bases directly, the $\rho \cdot \gamma$ monomial would remain algebraically unreachable.

### 2.3 Full Span Separation (Primary Defense)
**Claim:** The adversary cannot forge the public residual using witness handles because the public and witness subspaces are orthogonal.

<a id="span-table"></a>
**The Three Span Separations:**

| Matrix | Separation | Status | Notes |
|--------|------------|--------|-------|
| U (A-matrix) | $U_{pub} \perp U_{wit}$ | **TRIVIAL** | $u_{pub} = 0$ (public not in A) |
| V (B-matrix) | $V_{pub} \perp V_{wit}$ | **TRIVIAL** | $v_{pub} = 0$ (public not in B) |
| W (C-matrix) | $W_{pub} \perp W_{wit}$ | **VERIFIED** | Primary defense; $w_{pub} \neq 0$ for statement binding |

<a id="span-proof"></a>
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

<a id="baked-quotient"></a>
### 2.4 The Baked Quotient Invariant (Blocks Quotient Forging)
**Claim:** Under the audit-enforced span-membership condition ($Q_{const}$ not in span($H_{ij}$)), the adversary cannot use the CRS to forge the quotient correction $Q_{const}(x)$ or its armed equivalent.

<a id="adv-can-do"></a>
*   **What the Adversary CAN Do:**
    *   The adversary **can** compute $T_{const}(x) = \prod_{i=0}^{\ell} T_i^{x_i}$ in $G_T$ from the public GT-baked handles $T_i$ and the public inputs $x_i$.

<a id="adv-cannot-do"></a>
*   **What the Adversary CANNOT Do:**
    *   They have **no $G_1$ handle** for $Q_{const}(x,\tau)$: the quotient correction bases are missing from the $G_1$ span (Lean CRS explicitly excludes them).
    *   They have **no way to apply $\rho$ inside $G_T$**: the only source of $\rho$ is in the armed $G_2$ handles, and pairing is $G_1 \times G_2 \to G_T$. There is no operation that takes a $G_T$ element and multiplies it by $\rho$.

*   **Conclusion:** Given the missing $G_1$ bases for $Q_{const}$ and the fact that $Q_{const}$ is not in span($H_{ij}$) (enforced by audit), the adversary cannot synthesize $Q_{const}(x,\tau)$ in $G_1$, nor can they compute $T_{const}(x)^\rho$ from their handle set. The armed target remains unreachable.

### 2.5 WE Decryptor Model and RHS Identity Coverage

We now make explicit how our algebraic model captures a *general* decryptor with full pairing access, and how this covers all ways of realizing the QAP identity

$$\left(\sum_i a_i u_i(x)\right)\left(\sum_i a_i v_i(x)\right) = \sum_i a_i w_i(x) \pmod{t(x)}$$

**General decryptor model.**  
A WE decryptor is modeled as an arbitrary algebraic adversary in the AGBGM with oracles for:
- linear combinations in each of $G_1, G_2, G_T$, and
- the bilinear pairing $e: G_1 \times G_2 \to G_T$.

We impose **no restriction** that the decryptor must ever construct Groth16-style $(A,B,C)$ tuples. Any decryptor is just a polynomial-time pairing circuit over the published handles listed in [§1.1](#11-handles-and-labels) (Lean CRS, VK, arming instance), plus the ciphertext components (e.g. $R(vk,x)^\rho$).

**Algebraic labels in $G_T$.**  
Every handle $H_T \in G_T$ that the decryptor can ever obtain has an internal algebraic label of the form

$$L(H_T) \in F_r[\alpha,\beta,\gamma,\delta,\tau,\rho]$$

obtained by starting from the basis labels in [§1.1](#11-handles-and-labels) and closing under:
- linearity (addition and scalar multiplication of labels), and
- bilinearity: for $E = e(H_1,H_2)$, we have $L(E) = L(H_1) · L(H_2)$.

<a id="crucially"></a>
Crucially:
- **$\rho$ appears only in $G_2$ input labels**, linearly, via the armed handles $\beta_2^\rho$, $\delta_2^\rho$, $v_j(\tau)_2^\rho$ (see [Arming Instance](#arming-instance)).
- **No $G_1$ handle carries $\rho$**, and there is **no primitive that multiplies a $G_T$ handle by $\rho$** (see [What Adversary CANNOT Do](#adv-cannot-do)). Pairing two armed $G_2$ handles is impossible (domain mismatch), so every $G_T$ handle has degree $\le 1$ in $\rho$.

Thus the *coefficient* of $\rho$ in any $G_T$ label lies in the linear span generated from:
- the unarmed $G_1$ bases $A_k$, $B_k^{(1)}$, $L_k$, $IC_i$, $H_{wit}$, and
- the unarmed $G_2$ base $\beta_2$, $\gamma_2$, $\delta_2$.
Any $\rho$-bearing $G_T$ handle must arise from a single pairing that uses exactly one armed $G_2$ input, so its $\rho$-coefficient is confined to that unarmed $G_1$ span.

**Target label and the QAP RHS.**  
In our setting with $u_{pub}=v_{pub}=0$, the honest target label for the armed GT value is (see [Target Label](#target-label)):

$$L_{Target} = \rho \cdot (\alpha\beta + W_{pub} + Q_{const}(x)\delta)$$

where:
- $W_{pub}$ is the public-input contribution to the $C$-polynomial,
- $Q_{const}(x)$ is the affine quotient correction that accounts for the gap between the standard and Lean presentations,
- $T_{const}(x) = e(Q_{const}(x,\tau),\delta)$ is baked into $G_T$ (see [Gᴛ Bases](#gt-bases)),
- and the quotient decomposition is $H(x,w)=Q_{const}(x)+H_{wit}(w)$ (see [Quotient Decomposition](#quotient-decomposition)).

Any **GT element equal to the QAP RHS "honest value"** necessarily has label $L_{Target}$ up to public, $\rho$–independent multiplicative factors, because the only way to introduce $\rho$ into $G_T$ is through pairings with the armed $G_2$ handles, and the only public-input dependence available in the Lean CRS is via $W_{pub}$ and $Q_{const}(x)$.

**Indices $i > \ell$ (witness-only terms).**  
For all $i>\ell$ we explicitly provide individual witness-column elements:
- $A_k = u_k(\tau)$, $B_k^{(1)} = v_k(\tau)$, $L_k = (\beta u_k(\tau)+\alpha v_k(\tau)+w_k(\tau))/\delta$ for $k>\ell$ (see [G₁ Bases](#g1-bases)),
- $H_{wit}$ bases that involve at least one witness column (see [G₁ Bases](#g1-bases)),
- and their armed $G_2$ companions $v_j(\tau)_2^\rho$ for $j>\ell$ (see [Arming Instance](#arming-instance)).

These suffice for an honest prover to realize the witness-dependent part of the QAP identity

$$\left(\sum_i a_i u_i(x)\right)\left(\sum_i a_i v_i(x)\right) = W_{pub}(x) + W_{wit}(x) \pmod{t(x)}$$

in Groth16 form: the public part $W_{pub}$ is encoded solely via the $IC_i$ (see [G₁ Bases](#g1-bases), [Span Proof](#span-proof)), while the witness part $W_{wit}$ is encoded in $L_k$ and $H_{wit}$ (see [G₁ Bases](#g1-bases)). By W-span separation ($W_{pub} \perp W_{wit}$, see [Span Table](#span-table)), any GT element obtained by pairing witness-only handles with armed $G_2$ handles always has $\rho$–coefficient lying in the **witness span**, and can never pick up the $W_{pub}$ contribution.

**All alternative RHS syntheses are covered.**  

$$\sum_i a_i w_i(x) \pmod{t(x)}$$

might be realized in many different ways, not just via the canonical Groth16 $(A,B,C)$ construction. In our AGBGM formulation:
- Every $G_T$ handle the decryptor can compute has a label in the linear span generated by the basis labels in [§1.1](#11-handles-and-labels) under linearity and bilinearity.
- The **coefficient of $\rho$ in that label** must lie in the span of the witness-only $w$-contributions (via $L_k$, $H_{wit}$) plus any *unarmed* public terms (via $IC_i$, $T_i$).
- Because:
  - $W_{pub}$ lives in a subspace orthogonal to the witness span (W-span separation, see [Span Table](#span-table)), and
  - $Q_{const}(x)$ is **by audit** outside the span of the published $H_{ij}$ bases (see [Baked Quotient Invariant](#baked-quotient)),
  the label $\alpha\beta + W_{pub} + Q_{const}(x)\delta$ is algebraically unreachable as a $\rho$–coefficient within the adversary's span.

Equivalently, the only paths to $W_{pub}$ or $Q_{const}(x)$ inside $G_T$ would require either a missing $Q_{const}$ basis in $G_1$ or an oracle that multiplies $G_T$ by $\rho$; neither exists in the Lean CRS model.

Formally, if a decryptor produced some handle $K \in G_T$ with $L(K) = L_{Target}$, then we could use that to solve GT-XPDH (as detailed in [§4.4](#44-the-gt-xpdh--tep-reduction)) by extracting a $\rho$–multiple of $T_{const}(x)$, contradicting SXDH/GT-XPDH. Therefore:
- **No pairing circuit over the published handles can synthesize the QAP RHS label with the correct $\rho$–dependence**, unless the QAP identity holds with the actual witness and the honest construction is followed.
- This holds regardless of *how* the decryptor arranges its pairings (Groth16-style, or any algebraic re-encoding of the RHS), because we argue at the level of labels and spans, not at the level of a particular syntactic expression.

**WE game interpretation.**  
In the WE IND game, the adversary/decryptor receives:
1. all published Lean CRS and VK handles ([§1.1](#11-handles-and-labels)),
2. full access to linear-combination and pairing oracles ([§1.2](#12-adversary-capabilities)),
3. challenge ciphertext components, in particular $K^\star = R(vk,x_b)^\rho$ for a hidden bit $b$.

The simulator answers all linear-combination and pairing queries consistently while keeping $\rho$ confined to $G_2$ labels. Our span-separation plus GT-XPDH argument then shows:
- For any PPT decryptor, the view when $b=0$ vs. $b=1$ differs only in a handle whose label is outside the adversary's algebraic span, and
- Under GT-XPDH (see [Crucially](#crucially), [§4.1](#41-the-core-assumption-gt-xpdh)), such a handle is indistinguishable from a random $G_T$ element.

Hence the WE construction remains secure even against a **general pairing-aware decryptor**, not just against adversaries that try to manufacture Groth16-style proofs.

### 2.6 Defense in Depth: The Double Algebraic Lock

While the formal reduction relies on the AGBGM to characterize the system's security, the protocol implements two distinct, orthogonal algebraic barriers. An adversary must effectively break both to forge a key.

1. **The γ-Barrier (Scalar Independence):**
   The statement binding relies on terms of the form $w_i \cdot \gamma^{-1}$. The arming mechanism relies on $\rho$. In the AGBGM, no combination of pairing operations can map $\rho$ to $\gamma^{-1}$. This prevents the adversary from synthesizing the IC component of the target.

2. **The τ-Barrier (Polynomial Independence):**
   The baked quotient $T_{const}$ corresponds to a polynomial $Q_{const}(x, \tau)$ that lies outside the linear span of the Lean CRS (specifically, it requires powers of $\tau$ that are withheld).
   - Even if an adversary could bypass the γ-barrier (e.g., via an oracle for $\gamma$), they would still face the $T_{const}$ barrier.
   - Forging the term $e(Q_{const}, \delta)^\rho$ without the underlying $G_1$ bases is equivalent to solving a **q-type Knowledge-of-Exponent** problem. While strictly proven in the AGBGM (via span separation), this provides a second layer of heuristic security comparable to Strong Diffie-Hellman assumptions.

## 3. Completeness for Honest Prover

The "Honest Prover Dilemma" (Prover needs handles that Adversary abuses) is resolved by the **Linearity Assumption**.

*   Since no constraint places public inputs in A or B, the quotient separates: $H(x,w) = Q_{const}(x) + H_{wit}(w)$.
*   We **bake** $Q_{const}$ into the target as $T_{const}(x) = e(Q_{const}(x,\tau), \delta)$.
*   We **publish** handles only for $H_{wit}(w)$: $(wit, wit)$ pairs and $(const, wit)$ pairs excluding those where wit participates in a public-input binding row.
*   The adversary gets no handles involving public inputs (since $u_{pub} = v_{pub} = 0$).
*   The Honest Prover builds $H_{wit}(w)$ using the safe witness-only handles.

## 4. Reduction to Computational Assumptions

The security of the Lean CRS / Baked Quotient construction reduces to standard assumptions in the bilinear setting. We consider multiple related problems.

### 4.1 The Core Assumption: GT-XPDH

**GT-XPDH (Target Group Extended Power Diffie-Hellman):**
Given statement-only bases $(Y_j)$, $\Delta$ in $G_2$, their $\rho$-powers $(Y_j^\rho)$, $\Delta^\rho$, and independent target $R$ in $G_T$, compute $R^\rho$.

**Theorem (Tight Reduction):** Random GT-XPDH (with independent $R$) reduces tightly to DDH in $G_2$:
- If adversary breaks GT-XPDH with advantage $\epsilon$, there exists solver for DDH in $G_2$ with advantage $\geq \epsilon - 1/r$
- **SXDH implies GT-XPDH** (only the $G_2$-half of SXDH is needed)

See [gt-xpdh-reduction.md](gt-xpdh-reduction.md) for this Standard Model reduction. Note: PVUGC uses the *Correlated* GT-XPDH game (statement-derived $R$), which requires the AGBGM bridging argument to connect to Random GT-XPDH (see [§2.6](#26-defense-in-depth-the-double-algebraic-lock)).

### 4.2 The GBGM Simulation

In the GBGM, the adversary interacts with group elements through an **oracle** that:
- Returns random "handles" for group elements
- Only allows linear combinations and pairings
- The adversary cannot "look inside" the handles to extract discrete logs

**Simulation Setup:**

| World | τ (toxic waste) | CRS Elements | Target |
|-------|-----------------|--------------|--------|
| Real | Concrete field element | $\tau^i$ in $G_1$, $G_2$ at real τ | $e(Q_{const}(x,\tau), \delta)$ in $G_T$ |
| Simulated | Symbolic (never revealed) | Random handles with algebraic relations | Consistent random handle |

The simulator tracks all algebraic relations between handles. For any adversary query:
1. **Linear combination**: Returns handle consistent with tracked relations
2. **Pairing**: Returns handle consistent with the bilinear structure

### 4.3 Indistinguishability Argument

The adversary **cannot distinguish** real from simulated worlds because:

1. **Missing $G_1$ Bases**: The Lean CRS excludes $Q_{const}$ bases (the $Q_i(\tau)$ in $G_1$) for public-input-dependent quotient correction
2. **GT-Baked Projections Only**: The adversary receives only $G_T$ projections $T_i = e(Q_i(\tau), \delta)$, not the underlying $G_1$ elements
3. **Algebraic Consistency**: All queries return answers consistent with the algebraic structure
4. **No $\rho$-Scaling in $G_T$**: There is no operation to multiply a $G_T$ element by the arming secret $\rho$

**Adversary's View:**
- Lean CRS in $G_1$: witness-only bases (no $Q_{const}$ bases)
- $G_2$ VK: includes $\delta_2$
- $G_T$ handles: $T_i = e(Q_i(\tau), \delta)$ for $0 \le i \le \ell$

**Key Insight**: The adversary's reachable span is:

$$Span_{adv} = LinComb(Lean CRS) + Pairings(Lean CRS)$$

The *polynomial* $f(\tau) = Q_{const}(x,\tau)$ underlying $T_{const} = e(f(\tau), \delta)$ is still outside the $G_1$ span. Even though $T_{const}$ itself is computable in $G_T$, the adversary cannot compute $T_{const}^\rho$ because $\rho$ only appears in armed $G_2$ handles.

### 4.4 The GT-XPDH / TEP Reduction

Our setting maps directly to **GT-XPDH**:

**The Challenge:**
- Adversary has Lean CRS: $\tau^i$ in $G_1$ for $i$ in Lean (no $Q_{const}$ bases), $\delta_2$
- Adversary has GT-baked handles: $T_i = e(Q_i(\tau), \delta)$ for $0 \le i \le \ell$
- Target: $T_{const}^\rho$ where $T_{const} = e(Q_{const}(x,\tau), \delta_2)$ in $G_T$
- $Q_{const}(x,\tau)$ is **outside** the $G_1$ span of Lean CRS elements

**Why GT-XPDH Applies:**
The polynomial $f(\tau) = Q_{const}(x,\tau)$ represents the public-input-dependent quotient correction. The Lean CRS deliberately excludes the $G_1$ bases needed to compute $f(\tau)$ in $G_1$. The adversary can compute $T_{const} = e(f(\tau), \delta)$ from the GT-baked handles, but cannot:
1. Extract $f(\tau)$ from $T_{const}$ (discrete log in $G_T$)
2. Compute $T_{const}^\rho$ without a $G_T$-exponentiation oracle for $\rho$

To forge a proof, the adversary must produce $C \in G_1$ such that:

$$e(A, B) = T_{const}^\rho \cdot e(C, \delta)$$

This requires computing $T_{const}^\rho$ or an equivalent, which is exactly the GT-XPDH problem: given $G_T$ projections of polynomials outside the $G_1$ span, compute their $\rho$-exponent.

**Connection to TEP:**
The Target Exponent Problem is the "search" version: given the target $T_{const}$, find exponents $a$, $b$ such that $e(a \cdot G_1, b \cdot G_2) = T_{const}$. Our construction ensures:
- The adversary cannot find such $(a, b)$ without knowing $Q_{const}(\tau)$
- $Q_{const}(\tau)$ is not computable from the Lean CRS

**Theorem**: **In the AGBGM**, if $A$ can forge a Lean proof with advantage $\epsilon$, we can solve GT-XPDH with advantage $\epsilon / poly(\lambda)$.

### 4.5 Why Affine Quotient Correction is Critical

The affine structure $Q_{const}(x) = \sum_{i=0}^{\ell} x_i \cdot Q_i(\tau)$ (where $x_0 = 1$) is essential:

| Property | Security Implication |
|----------|---------------------|
| $(\ell+1)$-dimensional secret space | One coefficient per public input + constant |
| Linear in $x$ | Statement-dependent, witness-independent |
| Determined by $\ell+1$ samples | Setup computes $Q_0, \ldots, Q_\ell$ via probing |
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

| Constraint Type | A-column | B-column | C-column | Captured By |
|-----------------|----------|----------|----------|-------------|
| Bit reconstruction | $1$ | LC(bits) | $x_{wit}$ | $h_{query\_wit}$ |
| **Public binding** | $1$ | $x_{wit}$ | $x_{pub}$ | $t_{const}$ |
| Constant × Constant | $1$ | $1$ | — | $t_{const}$ |
| Constant × Witness | $1$ | $w_j$ | — | $h_{query\_wit}$ |
| Witness × Witness | $w_i$ | $w_j$ | — | $h_{query\_wit}$ |

**Standard→Lean Gap**: Rows captured by $t_{const}$ have **no G₁ handle** in the Lean CRS — the prover cannot compute their quotient contribution in G₁. This gap is a design choice that enables the security invariant (no handle abuse). GT-baking compensates so verification still succeeds:
- *Constant × Constant*: Circuit-determined, no witness/statement dependency
- *Public binding*: Statement-dependent ($x_{wit} = x_{pub}$), computable from public inputs

**Critical Invariant**: No constraint places a public input in A or B. Public inputs appear **only** in C.

### 5.2 Statement Dependency Requirement

For the derived key $K = R^\rho$ to be **statement-dependent** (binding the arming randomness $\rho$ to the specific public input $x$), statement binding is through the **Groth16 target** $R(vk, x)$.

*   **Constraint**: `1 * x_wit = x_pub` places $x$ in the **C-matrix** only (with single witness $x_{wit}$ in B).
*   **Effect**: $v_{pub} = 0$, $u_{pub} = 0$, $w_{pub} \neq 0$.
*   **Statement Binding**: Via $IC_i = w_i/\gamma$ in the Groth16 target:

$$R(vk, x) = e(\alpha_1, \beta_2) \cdot e(L(x), \gamma_2) \cdot T_{const}(x)$$

where $L(x) = \sum x_i \cdot IC_i$ and $IC_i = (\beta u_i + \alpha v_i + w_i)/\gamma = w_i/\gamma$ (since $u_i = v_i = 0$).

*   **Key**: $K(x) = R(vk, x)^\rho$. Different statements yield different $L(x)$, hence different $R$, hence different $K$.
*   **Security Benefit**: Eliminates the $\alpha \cdot V_{pub}$ pollution term; V-span becomes trivially satisfied.

## 6. Conclusion

The algebraic framework confirms that PVUGC is secure in the AGBGM when the following minimum defenses are in place:

### 6.1 Minimum Required Defenses

| Defense | Purpose | Blocks |
|---------|---------|--------|
| **W-Span Separation** | $W_{pub} \perp W_{wit}$ | Residue synthesis attack |
| **Lean CRS (Baked Quotient)** | Quotient in $G_T$ only; no Powers of Tau | Quotient forgery in $G_1$ |
| **Linear Circuit Design** | Public inputs appear linearly | Non-linear quotient terms |
| **Span Membership** | Audit-enforced condition: $Q_{const}$ not in span($H_{ij}$) | Baked quotient synthesis |

**Note:** U-span and V-span separation are trivially satisfied ($u_{pub} = v_{pub} = 0$) and need not be explicitly verified.

**Span Membership Sufficient Condition:** The audit check — $u_{pub}=0$, $v_{pub}=0$, and $rows(C_{pub}) \cap rows(C_{wit}) = \emptyset$ — is a **sufficient condition** implying $Q_{const}$ is not in span($H_{ij}$), and is exactly what PVUGC's circuit audit enforces in practice. This becomes if-and-only-if under the assumption that $H_{ij}$ bases are constructed solely from $(const, wit)$ and $(wit, wit)$ pairs with no shared Lagrange indices.

### 6.2 Security Properties Achieved

1. **Standard Groth16 Algebra** — No complex modifications needed; $\alpha_1$ can remain public
2. **Proof-Agnostic Decapsulation** — Any valid proof yields the same $K = R^\rho$
3. **Statement-Dependent Keys** — Different $(vk, x)$ pairs yield different keys via $IC_i = w_i/\gamma$
4. **GT-XPDH Hardness** — Reduces to DDH in $G_2$ (standard assumption)
5. **Simplified Attack Surface** — No $\alpha \cdot V_{pub}$ pollution term (V-span trivial)

The combination of these defenses eliminates all known algebraic attack vectors and reduces security to the hardness of **GT-XPDH** in the Generic Bilinear Group Model.

### 6.3 Assumption Hierarchy

```
   PVUGC Protocol (Correlated Game)
         ↓ (Structural Security via AGBGM)
   Generic GT-XPDH Problem
         ↓ (Computational Hardness via Standard Model)
   DDH in G₂
```

In the **standard model** (non-generic), security relies on:
- **SXDH**: DDH hardness in both $G_1$ and $G_2$ (only $G_2$-half needed)
- **Groth16 Knowledge Soundness**: Valid proofs only from witness knowledge
- **Collision Resistance**: SHA-256 for Fiat-Shamir

The GBGM provides the cleanest reduction with bound $O(q^2/r)$ for $q$ oracle queries.

**Two complementary proofs:**
1. **This document**: AGBGM span-separation analysis (PVUGC → GT-XPDH)
2. **[gt-xpdh-reduction.md](gt-xpdh-reduction.md)**: Standard Model reduction (Random GT-XPDH → DDH)
