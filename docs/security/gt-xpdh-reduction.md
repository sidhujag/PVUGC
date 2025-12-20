# GT-XPDH Reduction to DDH in $\mathbb{G}_2$ (and Generic-Model Bound)

This note formalizes the GT-XPDH ("external power in $\mathbb{G}_T$") assumption and records:

- a tight black-box reduction from GT-XPDH to DDH in $\mathbb{G}_2$, hence that SXDH implies GT-XPDH, and
- the algebraic generic bilinear group (GBGM) bound of $\sim O(q^2 / r)$ (polylog factors in $q$ suppressed) for any adversary making $q$ oracle calls.

We conclude with the PVUGC "No-Proof-Spend" corollary. All probabilities below are taken over the randomness of both the challenger and the adversary.

---

## Setting

Let $(\mathbb{G}_1, \mathbb{G}_2, \mathbb{G}_T, e)$ be asymmetric prime-order, non-degenerate bilinear groups of order $r$. Let $g_1 \in \mathbb{G}_1$ and $g_2 \in \mathbb{G}_2$ be generators, and write $g_T := e(g_1, g_2)$ for the induced generator of $\mathbb{G}_T$. We assume canonical encodings with efficient equality testing in every group.

SXDH asserts that DDH is hard in both $\mathbb{G}_1$ and $\mathbb{G}_2$; throughout this document we only rely on the $\mathbb{G}_2$-half (DDH in $\mathbb{G}_2$).

---

## GT-XPDH (external power in $\mathbb{G}_T$)

Fix $m \geq 0$. Sample independently (statement-only) bases $Y_0, \ldots, Y_m, \Delta \leftarrow_R \mathbb{G}_2$, a non-zero exponent $\rho \leftarrow_R \mathbb{Z}_r^*$, and $R \leftarrow_R \mathbb{G}_T$. Give the adversary the tuple

$$\left( \{Y_j\}_{j=0}^m, \Delta, \{Y_j^\rho\}_{j=0}^m, \Delta^\rho, R \right)$$

The adversary succeeds in the computational GT-XPDH game if it outputs $R^\rho \in \mathbb{G}_T$. In the decisional GT-XPDH-DEC variant the challenger additionally samples $b \leftarrow_R \{0,1\}$ and sets

$$W := \begin{cases} R^\rho & \text{if } b = 1 \\ U & \text{for } U \leftarrow_R \mathbb{G}_T \text{ if } b = 0 \end{cases}$$

giving $W$ to the adversary, whose goal is to recover $b$. The advantages are defined in the usual way: for a computational adversary

$$\mathsf{Adv}_{GT\text{-}XPDH}(\mathcal{A}) := \Pr[\mathcal{A} \text{ outputs } R^\rho]$$

and for a decisional adversary

$$\mathsf{Adv}_{GT\text{-}XPDH\text{-}DEC}(\mathcal{A}) := |\Pr[\mathcal{A} \text{ outputs } 1 \mid b = 1] - \Pr[\mathcal{A} \text{ outputs } 1 \mid b = 0]|$$

---

## Lemma 1 (Uniform "pairing form" of $R$)

For $u \leftarrow_R \mathbb{Z}_r^*$ and $v \leftarrow_R \mathbb{Z}_r$, the element

$$R_0 := e(g_1^u, g_2^v) = g_T^{uv}$$

is uniform in $\mathbb{G}_T$ and independent of all other sampled values. Indeed, for any $t \in \mathbb{Z}_r$,

$$\Pr[uv = t] = \sum_{u \in \mathbb{Z}_r^*} \Pr[u] \cdot \Pr[v = t \cdot u^{-1}] = \frac{r-1}{(r-1) \cdot r} = \frac{1}{r}$$

so $uv$ is uniform in $\mathbb{Z}_r$, implying that $R_0$ is uniform in $\mathbb{G}_T$. Because the samplings of $u$ and $v$ are independent of $\rho$ and of $\{Y_j, \Delta\}$, the value $R_0$ is jointly independent of those elements as required.

Consequently, the GT-XPDH game is equivalent to the variant in which the challenger sets $R = e(g_1^u, g_2^v)$ for fresh uniformly random $u \in \mathbb{Z}_r^*$, $v \in \mathbb{Z}_r$. Moreover, $R_0$ is independent not only of $\rho$ and $\{Y_j, \Delta\}$, but also of their powered forms $\{Y_j^\rho\}$ and $\Delta^\rho$, which are functions of $X = g_2^\rho$ and the independently sampled $\{Y_j, \Delta\}$.

### Lemma 2 (Independence of PVUGC anchor from armed bases)

Let $(\mathsf{vk}, x)$ be any fixed Groth16 statement. The Groth16 verification target is:

$$R(\mathsf{vk}, x) = e([\alpha]_1, [\beta]_2) \cdot e(L(x), [\gamma]_2)$$

where $L(x) = \sum_i x_i \cdot IC_i$ is the public-input linear combination.

**Key observation:** The armed bases $\{[\beta]_2^\rho, [v_j]_2^\rho, [\delta]_2^\rho\}$ are derived from $\{[\beta]_2, b_{g2\_query} \text{ (witness columns)}, [\delta]_2\}$. Critically, **$[\gamma]_2$ is never armed**.

**Independence claim:** Since $[\gamma]_2 \notin \text{span}\{\text{armed bases}\}$, the **$\rho$-armed** component $e(L(x), [\gamma]_2)^\rho$ (and hence $R(\mathsf{vk},x)^\rho$) cannot be computed from the armed transcript alone. The adversary can pair $[\alpha]_1$ with armed bases, but these never produce terms involving $[\gamma]_2^\rho$.

**For the reduction:** We treat $R(\mathsf{vk}, x)$ as a fixed statement-derived $\mathbb{G}_T$ element. The reduction embeds the DDH challenge element $Y = g_2^v$ into $[\gamma]_2$, allowing the simulator to detect whether the adversary computed $R(\mathsf{vk}, x)^\rho$. This works because $R(\mathsf{vk}, x)$ contains a factor $e(L(x), [\gamma]_2)$ that depends on $[\gamma]_2$, which the adversary cannot access in armed form.

---

## Theorem 1 (Tight reduction to DDH in $\mathbb{G}_2$)

Let $\mathcal{A}$ be any PPT adversary for GT-XPDH with success probability $\varepsilon$. There exists a PPT algorithm $\mathcal{B}$ that solves DDH in $\mathbb{G}_2$ with advantage at least $\varepsilon - 1/r$. The reduction is tight: $\mathcal{B}$ makes a single black-box call to $\mathcal{A}$ and performs only a constant number of pairings.

### DDH$_{\mathbb{G}_2}$ game

The DDH challenger samples $\rho, v \leftarrow_R \mathbb{Z}_r$, sets $X := g_2^\rho$ and $Y := g_2^v$, and returns

$$(g_2, X, Y, T)$$

where either $T = g_2^{\rho v}$ (the Diffie–Hellman case) or $T \leftarrow_R \mathbb{G}_2$ (the random case). The adversary must decide which distribution it received.

### Construction of $\mathcal{B}$

Given $(g_2, X, Y, T)$ from the DDH challenger:

1. **Embed the exponent.** Sample independent coefficients $\alpha_0, \ldots, \alpha_m, \alpha_\Delta \leftarrow_R \mathbb{Z}_r$ and set
   $$Y_j := g_2^{\alpha_j}, \quad Y_j^\rho := X^{\alpha_j}, \quad \Delta := g_2^{\alpha_\Delta}, \quad \Delta^\rho := X^{\alpha_\Delta}$$
   This matches the distribution in the GT-XPDH game because $X = g_2^\rho$.

2. **Program $R$.** Using the lemma, sample $u \leftarrow_R \mathbb{Z}_r^*$ and set
   $$R := e(g_1^u, Y) = e(g_1^u, g_2^v)$$

3. **Run $\mathcal{A}$.** Provide $(\{Y_j\}, \Delta, \{Y_j^\rho\}, \Delta^\rho, R)$ to $\mathcal{A}$ and record its output $S$.

4. **Decide.** Compute
   $$T' := e(g_1^u, T) \in \mathbb{G}_T$$
   and output "DH" if and only if $S = T'$.

### Correctness analysis

- If $T = g_2^{\rho v}$, then
  $$T' = e(g_1^u, g_2^{\rho v}) = e(g_1^u, g_2^v)^\rho = R^\rho$$
  Hence $S = T'$ exactly when $\mathcal{A}$ solves the GT-XPDH instance, which occurs with probability $\varepsilon$.

- If $T \leftarrow_R \mathbb{G}_2$, then by bilinearity $T' = e(g_1^u, T)$ is uniform in $\mathbb{G}_T$ and independent of $S$ (since $S = R^\rho$). Therefore $\Pr[S = T'] = 1/r$.

The distinguishing advantage of $\mathcal{B}$ is thus at least $\varepsilon - 1/r$. Consequently DDH hardness in $\mathbb{G}_2$ implies both the computational and decisional variants of GT-XPDH.

### Correlated GT-XPDH (PVUGC form)

PVUGC never samples an independent random $R$; instead it derives

$$R(\mathsf{vk}, x) = e([\alpha]_1, [\beta]_2) \cdot e(IC(x), [\gamma]_2)$$

from the verifying key and public input. The protocol enforces five guardrails:

1. $[\gamma]_2$ never appears among the armed bases (only the aggregated public B-column, witness-only B columns, and $[\delta]_2$ are armed).
2. Every public input wire participates in a non-zero C-column so that $IC(x) \neq 0$.
3. CRS hygiene holds: $[\gamma]_2 \notin \text{span}\{[\beta]_2, b_{g2\_query}, [\delta]_2\}$.
4. Each arming uses a fresh exponent $\rho$.
5. Never arm any $\mathbb{G}_1$ element (arming $U^\rho$ would reveal $e(U, [\gamma]_2)^\rho$ via public pairings).

These guardrails are the reduction-level restatement of the Lean-CRS / baked-quotient architecture in [algebraic_framework.md](algebraic_framework.md): public inputs bound in the C-matrix only ($u_{pub} = v_{pub} = 0$, $w_{pub} \neq 0$), W-span separation between public and witness C-rows, and the explicit exclusion of any armed $[\gamma]_2$ handle.

Under these conditions, **$R(\mathsf{vk}, x)$ contains a factor $e(L(x), [\gamma]_2)$ that cannot be computed from the armed transcript** since $[\gamma]_2^\rho$ is never published (Lemma 2). We define the **correlated GT-XPDH game** as: armed bases $\{[\beta]_2^\rho, [v_j]_2^\rho, [\delta]_2^\rho\}$ are derived from $(\mathsf{vk}, x)$ under the guardrails, the challenger samples $\rho$, and sets $R = R(\mathsf{vk}, x)$. An adversary wins if it outputs $R^\rho$.

### Theorem 1′ (Tight DDH reduction for the correlated game)

Let $\mathcal{A}$ break the correlated GT-XPDH game with advantage $\varepsilon$. Construct $\mathcal{B}$ against DDH in $\mathbb{G}_2$ just as before, except that:

1. Embed the DDH challenge element $Y = g_2^v$ as $[\gamma]_2$ inside the CRS (this is consistent with the hygiene rule).
2. Program $[\alpha]_1 = g_1^u$ with $u \leftarrow_R \mathbb{Z}_r^*$ and keep the public input $x$ fixed so $IC(x)$ is known.
3. Publish the armed transcript derived from $\mathsf{vk}$ along with $R(\mathsf{vk}, x) = e(g_1^u, [\beta]_2) \cdot e(IC(x), Y)$. (The simulator can compute $[\beta]_2^\rho$ as $X^b$ because it chose $[\beta]_2 = g_2^b$ and the DDH challenger supplies $X = g_2^\rho$.)

If the DDH challenge is real ($T = g_2^{\rho v}$), then

$$R(\mathsf{vk}, x)^\rho = e(g_1^u, [\beta]_2)^\rho \cdot e(IC(x), Y)^\rho = e(g_1^u, [\beta]_2^\rho) \cdot e(IC(x), T)$$

and $\mathcal{A}$'s output lets $\mathcal{B}$ compare against $e(IC(x), T)$ exactly as in Theorem 1 after cancelling the known $[\beta]_2^\rho$ term. If the challenge is random, the comparison succeeds only with probability $1/r$. Thus $\mathcal{B}$ decides DDH with advantage at least $\varepsilon - 1/r$, showing that SXDH implies security for PVUGC even in the correlated setting.

---

## Theorem 2 (Algebraic GBGM bound)

In the algebraic generic bilinear group model, let $\mathcal{A}$ issue at most $q$ oracle queries (group operations in $\mathbb{G}_1$, $\mathbb{G}_2$, $\mathbb{G}_T$, and pairings). Then

$$\mathsf{Adv}_{GT\text{-}XPDH}(\mathcal{A}) \leq \sim O(q^2 / r)$$

**Sketch.** Assign formal indeterminates $a$, $i_x$ to the $\mathbb{G}_1$ sources and $y_\beta$, $y_\gamma$, $y_\delta$, $\{y_j\}$ to the $\mathbb{G}_2$ sources. Every $\mathbb{G}_T$ handle maintained by $\mathcal{A}$ is labeled with an explicit polynomial $E_H$ in these variables. Pairing with a masked right leg $Y^\rho \in \{[\beta]_2^\rho, [v_j]_2^\rho, [\delta]_2^\rho\}$ contributes a monomial of the form $\rho \cdot L(U) \cdot y_*$ (degree $\leq 3$), where $L(U)$ is the linear form describing the left leg $U \in \mathbb{G}_1$ and $y_* \in \{y_\beta, y_j \,(j > \ell), y_\delta\}$. Operations inside $\mathbb{G}_T$ add such polynomials and scale them by known integers, so the $\rho$-bearing part of any reachable $E_H$ lies in

$$\rho \cdot \text{span}\{ y_\beta, y_j \,(j > \ell), y_\delta \}$$

and never includes a $\rho \cdot y_\gamma$ term. The target exponent is $E_* = \rho \cdot r_* = \rho \cdot (a \cdot y_\beta + i_x \cdot y_\gamma)$, whose $\rho \cdot y_\gamma$ coefficient equals $i_x \neq 0$ for valid statements. Therefore $E_H = E_*$ can hold only via an accidental algebraic equality among the $\leq q$ produced handles. The standard algebraic/generic-group collision analysis (Schwartz–Zippel style) bounds this probability by $\sim O(q^2 / r)$. $\square$

---

## Corollary (PVUGC No-Proof-Spend)

Fix a statement $(\mathsf{vk}, x)$. Let the statement-only bases $\{Y_j\}$, $\Delta$ be derived from $\mathsf{vk}$ (excluding $\gamma_2$), and require an accepting GS attestation before any $\mathbb{G}_1$ witnesses may appear inside pairings. For a fresh exponent $\rho_i$ sampled per armer, and given only the public data $(\{Y_j^{\rho_i}\}, \Delta^{\rho_i}, R(\mathsf{vk}, x))$, computing

$$M_i := R(\mathsf{vk}, x)^{\rho_i}$$

without an accepting attestation is infeasible:

- **GBGM:** the success probability is at most $\sim O(q^2 / r)$.
- **SXDH / DDH in $\mathbb{G}_2$:** any PPT adversary for the computation gives a PPT DDH$_{\mathbb{G}_2}$ solver with essentially the same advantage (Theorem 1).

Consequently the PVUGC key $K_i = \text{Hash}(\text{ser}_{\mathbb{G}_T}(M_i) \| \ldots)$ remains hidden and the adaptor cannot be finalized without producing a valid attestation.

---

## Self-decapper resistance

**Security dependency.** With public inputs in C-matrix only ($v_{pub} = 0$), $[\gamma]_2$ is excluded from armed bases. The PPE constraint ensures that honest proofs satisfy the verification equation.

**Key observation:** Statement binding is through $R(\mathsf{vk}, x)$ which includes $e(L(x), [\gamma]_2)$ where $L(x) = \sum x_i \cdot IC_i$ and $IC_i = w_i/\gamma$. Since $[\gamma]_2$ is never armed, the adversary cannot compute $R^\rho$ without producing a valid Groth16 proof.

This reduces to **DDH in $\mathbb{G}_2$**: the reduction embeds the DDH challenge element into $[\gamma]_2$, allowing detection of whether the adversary computed $R(\mathsf{vk}, x)^\rho$.

---

## Note on "DLIP" (target-group assumptions)

The above results do not rely on any additional $\mathbb{G}_T$-side assumptions. One may still cite target-group assumptions such as GT-DLIN/DLIP when considering alternate formulations in which $R$ is algebraically derived from public $\mathbb{G}_T$ combinations, but they are unnecessary for the GT-XPDH formulation used here (in which $R$ is uniform and independent).

---

## Summary

- GT-XPDH tightly reduces to DDH in $\mathbb{G}_2$; thus SXDH (using only the $\mathbb{G}_2$ half) suffices.
- In the algebraic GBGM the success probability is bounded by $\sim O(q^2 / r)$.
- PVUGC's No-Proof-Spend property follows directly under these standard assumptions.
