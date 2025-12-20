# GT-XPDH Reduction to DDH in G₂ (and Generic-Model Bound)

This note formalizes the GT-XPDH ("external power in $G_T$") assumption and records:

- a tight black-box reduction from GT-XPDH to DDH in G₂, hence that SXDH implies GT-XPDH, and
- the algebraic generic bilinear group (GBGM) bound of $O(q^2 / r)$ (polylog factors in $q$ suppressed) for any adversary making $q$ oracle calls.

We conclude with the PVUGC "No-Proof-Spend" corollary. All probabilities below are taken over the randomness of both the challenger and the adversary.

---

## Setting

Let $(G_1, G_2, G_T, e)$ be asymmetric prime-order, non-degenerate bilinear groups of order $r$. Let $g_1 \in G_1$ and $g_2 \in G_2$ be generators, and write $g_T := e(g_1, g_2)$ for the induced generator of $G_T$. We assume canonical encodings with efficient equality testing in every group.

SXDH asserts that DDH is hard in both $G_1$ and $G_2$; throughout this document we only rely on the G₂-half (DDH in G₂).

---

<a id="gt-xpdh-definition"></a>
## GT-XPDH (external power in $G_T$)

Fix $m \geq 0$. Sample independently (statement-only) bases $Y_0, \ldots, Y_m, \Delta \leftarrow G_2$, a non-zero exponent $\rho \leftarrow Z_r^*$, and $R \leftarrow G_T$. Give the adversary the tuple

$$(Y_0, \ldots, Y_m, \Delta, Y_0^\rho, \ldots, Y_m^\rho, \Delta^\rho, R)$$

The adversary succeeds in the computational GT-XPDH game if it outputs $R^\rho \in G_T$. In the decisional GT-XPDH-DEC variant the challenger additionally samples $b \leftarrow (0,1)$ and sets:

- $W := R^\rho$ if $b = 1$
- $W := U$ for $U \leftarrow G_T$ if $b = 0$

giving $W$ to the adversary, whose goal is to recover $b$. The advantages are defined in the usual way: for a computational adversary

$$Adv_{GT-XPDH}(A) := Pr[A \to R^\rho]$$

and for a decisional adversary

$$Adv_{GT-XPDH-DEC}(A) := |Pr[A \to 1 \mid b=1] - Pr[A \to 1 \mid b=0]|$$

---

<a id="lemma-1"></a>
## Lemma 1 (Uniform "pairing form" of R)

For $u \leftarrow Z_r^*$ and $v \leftarrow Z_r$, the element

$$R_0 := e(g_1^u, g_2^v) = g_T^{uv}$$

is uniform in $G_T$ and independent of all other sampled values. Indeed, for any $t \in Z_r$,

$$Pr[uv = t] = \sum_u Pr[u] \cdot Pr[v = t \cdot u^{-1}] = \frac{r-1}{(r-1) \cdot r} = \frac{1}{r}$$

so $uv$ is uniform in $Z_r$, implying that $R_0$ is uniform in $G_T$. Because the samplings of $u$ and $v$ are independent of $\rho$ and of $(Y_j, \Delta)$, the value $R_0$ is jointly independent of those elements as required.

Consequently, the GT-XPDH game is equivalent to the variant in which the challenger sets $R = e(g_1^u, g_2^v)$ for fresh uniformly random $u \in Z_r^*$, $v \in Z_r$. Moreover, $R_0$ is independent not only of $\rho$ and $(Y_j, \Delta)$, but also of their powered forms $(Y_j^\rho)$ and $\Delta^\rho$, which are functions of $X = g_2^\rho$ and the independently sampled $(Y_j, \Delta)$.

<a id="lemma-2"></a>
### Lemma 2 (Independence of PVUGC anchor from armed bases)

Let $(vk, x)$ be any fixed Groth16 statement. The Groth16 verification target is:

$$R(vk, x) = e(\alpha_1, \beta_2) \cdot e(L(x), \gamma_2)$$

where $L(x) = \sum_i x_i \cdot IC_i$ is the public-input linear combination.

<a id="key-observation"></a>
**Key observation:** The armed bases $\beta_2^\rho$, $v_{j,2}^\rho$, $\delta_2^\rho$ are derived from $\beta_2$, witness columns, and $\delta_2$. Critically, **$\gamma_2$ is never armed**.

**Independence claim:** Since $\gamma_2$ is not in span(armed bases), the **ρ-armed** component $e(L(x), \gamma_2)^\rho$ (and hence $R(vk,x)^\rho$) cannot be computed from the armed transcript alone. The adversary can pair $\alpha_1$ with armed bases, but these never produce terms involving $\gamma_2^\rho$.

**For the reduction:** We treat $R(vk, x)$ as a fixed statement-derived $G_T$ element. The reduction embeds the DDH challenge element $Y = g_2^v$ into $\gamma_2$, allowing the simulator to detect whether the adversary computed $R(vk, x)^\rho$. This works because $R(vk, x)$ contains a factor $e(L(x), \gamma_2)$ that depends on $\gamma_2$, which the adversary cannot access in armed form.

---

<a id="theorem-1"></a>
## Theorem 1 (Tight reduction to DDH in G₂)

Let $A$ be any PPT adversary for GT-XPDH with success probability $\epsilon$. There exists a PPT algorithm $B$ that solves DDH in $G_2$ with advantage at least $\epsilon - 1/r$. The reduction is tight: $B$ makes a single black-box call to $A$ and performs only a constant number of pairings.

<a id="ddh-game"></a>
### DDH in G₂ game

The DDH challenger samples $\rho, v \leftarrow Z_r$, sets $X := g_2^\rho$ and $Y := g_2^v$, and returns

$$(g_2, X, Y, T)$$

where either $T = g_2^{\rho v}$ (the Diffie–Hellman case) or $T \leftarrow G_2$ (the random case). The adversary must decide which distribution it received.

<a id="construction-b"></a>
### Construction of B

Given $(g_2, X, Y, T)$ from the DDH challenger:

1. **Embed the exponent.** Sample independent coefficients $\alpha_0, \ldots, \alpha_m, \alpha_\Delta \leftarrow Z_r$ and set

$$Y_j := g_2^{\alpha_j}, \quad Y_j^\rho := X^{\alpha_j}, \quad \Delta := g_2^{\alpha_\Delta}, \quad \Delta^\rho := X^{\alpha_\Delta}$$

This matches the distribution in the GT-XPDH game because $X = g_2^\rho$.

2. **Program R.** Using [Lemma 1](#lemma-1), sample $u \leftarrow Z_r^*$ and set

$$R := e(g_1^u, Y) = e(g_1^u, g_2^v)$$

3. **Run A.** Provide $((Y_j), \Delta, (Y_j^\rho), \Delta^\rho, R)$ to $A$ and record its output $S$.

4. **Decide.** Compute

$$T' := e(g_1^u, T) \in G_T$$

and output "DH" if and only if $S = T'$.

<a id="correctness"></a>
### Correctness analysis

- If $T = g_2^{\rho v}$, then $T' = e(g_1^u, g_2^{\rho v}) = e(g_1^u, g_2^v)^\rho = R^\rho$. Hence $S = T'$ exactly when $A$ solves the GT-XPDH instance, which occurs with probability $\epsilon$.

- If $T \leftarrow G_2$, then by bilinearity $T' = e(g_1^u, T)$ is uniform in $G_T$ and independent of $S$ (since $S = R^\rho$). Therefore $Pr[S = T'] = 1/r$.

The distinguishing advantage of $B$ is thus at least $\epsilon - 1/r$. Consequently DDH hardness in $G_2$ implies both the computational and decisional variants of GT-XPDH.

<a id="correlated-gt-xpdh"></a>
### Correlated GT-XPDH (PVUGC form)

PVUGC never samples an independent random $R$; instead it derives

$$R(vk, x) = e(\alpha_1, \beta_2) \cdot e(IC(x), \gamma_2)$$

from the verifying key and public input. The protocol enforces five guardrails:

<a id="guardrails"></a>
1. $\gamma_2$ never appears among the armed bases (only the aggregated public B-column, witness-only B columns, and $\delta_2$ are armed).
2. Every public input wire participates in a non-zero C-column so that $IC(x) \neq 0$.
3. CRS hygiene holds: $\gamma_2$ is not in span($\beta_2$, $b_{g2query}$, $\delta_2$).
4. Each arming uses a fresh exponent $\rho$.
5. Never arm any $G_1$ element (arming $U^\rho$ would reveal $e(U, \gamma_2)^\rho$ via public pairings).

These guardrails are the reduction-level restatement of the Lean-CRS / baked-quotient architecture in [algebraic_framework.md](algebraic_framework.md): public inputs bound in the C-matrix only ($u_{pub} = v_{pub} = 0$, $w_{pub} \neq 0$), W-span separation between public and witness C-rows, and the explicit exclusion of any armed $\gamma_2$ handle.

Under these conditions, **$R(vk, x)$ contains a factor $e(L(x), \gamma_2)$ that cannot be computed from the armed transcript** since $\gamma_2^\rho$ is never published ([Lemma 2](#lemma-2)). We define the **correlated GT-XPDH game** as: armed bases $\beta_2^\rho$, $v_{j,2}^\rho$, $\delta_2^\rho$ are derived from $(vk, x)$ under the guardrails, the challenger samples $\rho$, and sets $R = R(vk, x)$. An adversary wins if it outputs $R^\rho$.

<a id="theorem-1-prime"></a>
### Theorem 1′ (Tight DDH reduction for the correlated game)

Let $A$ break the correlated GT-XPDH game with advantage $\epsilon$. Construct $B$ against DDH in $G_2$ just as before, except that:

1. Embed the DDH challenge element $Y = g_2^v$ as $\gamma_2$ inside the CRS (this is consistent with the hygiene rule).
2. Program $\alpha_1 = g_1^u$ with $u \leftarrow Z_r^*$ and keep the public input $x$ fixed so $IC(x)$ is known.
3. Publish the armed transcript derived from $vk$ along with $R(vk, x) = e(g_1^u, \beta_2) \cdot e(IC(x), Y)$. (The simulator can compute $\beta_2^\rho$ as $X^b$ because it chose $\beta_2 = g_2^b$ and the DDH challenger supplies $X = g_2^\rho$.)

If the DDH challenge is real ($T = g_2^{\rho v}$), then

$$R(vk, x)^\rho = e(g_1^u, \beta_2)^\rho \cdot e(IC(x), Y)^\rho = e(g_1^u, \beta_2^\rho) \cdot e(IC(x), T)$$

and $A$'s output lets $B$ compare against $e(IC(x), T)$ exactly as in [Theorem 1](#theorem-1) after cancelling the known $\beta_2^\rho$ term. If the challenge is random, the comparison succeeds only with probability $1/r$. Thus $B$ decides DDH with advantage at least $\epsilon - 1/r$, showing that SXDH implies security for PVUGC even in the correlated setting.

---

<a id="theorem-2"></a>
## Theorem 2 (Algebraic GBGM bound)

In the algebraic generic bilinear group model, let $A$ issue at most $q$ oracle queries (group operations in $G_1$, $G_2$, $G_T$, and pairings). Then

$$Adv_{GT-XPDH}(A) \leq O(q^2 / r)$$

**Sketch.** Assign formal indeterminates $a$, $i_x$ to the $G_1$ sources and $y_\beta$, $y_\gamma$, $y_\delta$, $y_j$ to the $G_2$ sources. Every $G_T$ handle maintained by $A$ is labeled with an explicit polynomial $E_H$ in these variables. Pairing with a masked right leg $Y^\rho$ (one of $\beta_2^\rho$, $v_{j,2}^\rho$, $\delta_2^\rho$) contributes a monomial of the form $\rho \cdot L(U) \cdot y$ (degree ≤ 3), where $L(U)$ is the linear form describing the left leg $U$ in $G_1$ and $y$ is one of $y_\beta$, $y_j$ (for $j > \ell$), or $y_\delta$. Operations inside $G_T$ add such polynomials and scale them by known integers, so the $\rho$-bearing part of any reachable $E_H$ lies in

$$\rho \cdot span(y_\beta, y_j, y_\delta)$$

where $j > \ell$, and never includes a $\rho \cdot y_\gamma$ term. The target exponent is $E = \rho \cdot r = \rho \cdot (a \cdot y_\beta + i_x \cdot y_\gamma)$, whose $\rho \cdot y_\gamma$ coefficient equals $i_x \neq 0$ for valid statements. Therefore $E_H = E$ can hold only via an accidental algebraic equality among the ≤ $q$ produced handles. The standard algebraic/generic-group collision analysis (Schwartz–Zippel style) bounds this probability by $O(q^2 / r)$. ∎

---

<a id="corollary"></a>
## Corollary (PVUGC No-Proof-Spend)

Fix a statement $(vk, x)$. Let the statement-only bases $(Y_j)$, $\Delta$ be derived from $vk$ (excluding $\gamma_2$), and require an accepting GS attestation before any $G_1$ witnesses may appear inside pairings. For a fresh exponent $\rho_i$ sampled per armer, and given only the public data $((Y_j^{\rho_i}), \Delta^{\rho_i}, R(vk, x))$, computing

$$M_i := R(vk, x)^{\rho_i}$$

without an accepting attestation is infeasible:

- **GBGM:** the success probability is at most $O(q^2 / r)$ (see [Theorem 2](#theorem-2)).
- **SXDH / DDH in G₂:** any PPT adversary for the computation gives a PPT DDH solver in G₂ with essentially the same advantage (see [Theorem 1](#theorem-1)).

Consequently the PVUGC key $K_i = Hash(ser_{G_T}(M_i) \| \ldots)$ remains hidden and the adaptor cannot be finalized without producing a valid attestation.

---

<a id="self-decapper"></a>
## Self-decapper resistance

**Security dependency.** With public inputs in C-matrix only ($v_{pub} = 0$), $\gamma_2$ is excluded from armed bases. The PPE constraint ensures that honest proofs satisfy the verification equation.

**Key observation:** Statement binding is through $R(vk, x)$ which includes $e(L(x), \gamma_2)$ where $L(x) = \sum x_i \cdot IC_i$ and $IC_i = w_i/\gamma$. Since $\gamma_2$ is never armed, the adversary cannot compute $R^\rho$ without producing a valid Groth16 proof.

This reduces to **DDH in G₂**: the reduction embeds the DDH challenge element into $\gamma_2$, allowing detection of whether the adversary computed $R(vk, x)^\rho$ (see [Theorem 1′](#theorem-1-prime)).

---

## Note on "DLIP" (target-group assumptions)

The above results do not rely on any additional $G_T$-side assumptions. One may still cite target-group assumptions such as GT-DLIN/DLIP when considering alternate formulations in which $R$ is algebraically derived from public $G_T$ combinations, but they are unnecessary for the GT-XPDH formulation used here (in which $R$ is uniform and independent).

---

## Summary

- GT-XPDH tightly reduces to DDH in G₂ (see [Theorem 1](#theorem-1)); thus SXDH (using only the G₂ half) suffices.
- In the algebraic GBGM the success probability is bounded by $O(q^2 / r)$ (see [Theorem 2](#theorem-2)).
- PVUGC's No-Proof-Spend property follows directly under these standard assumptions (see [Corollary](#corollary)).
