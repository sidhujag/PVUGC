# GT-XPDH Reduction to DDH in G2 (and Generic-Model Bound)

This note formalizes the GT-XPDH ("external power in GT") assumption and records:

- a tight black-box reduction from GT-XPDH to DDH in G2, hence that SXDH implies GT-XPDH, and
- the algebraic generic bilinear group (GBGM) bound of ~O(q^2 / r) (polylog factors in q suppressed) for any adversary making q oracle calls.

We conclude with the PVUGC "No-Proof-Spend" corollary. All probabilities below are taken over the randomness of both the challenger and the adversary.

---

## Setting

Let (G1, G2, GT, e) be asymmetric prime-order, non-degenerate bilinear groups of order r. Let g1 ∈ G1 and g2 ∈ G2 be generators, and write gT := e(g1, g2) for the induced generator of GT. We assume canonical encodings with efficient equality testing in every group.

SXDH asserts that DDH is hard in both G1 and G2; throughout this document we only rely on the G2-half (DDH in G2).

---

## GT-XPDH (external power in GT)

Fix m ≥ 0. Sample independently (statement-only) bases Y0, …, Ym, Δ ←R G2, a non-zero exponent ρ ←R Zr*, and R ←R GT. Give the adversary the tuple

( {Yj}j=0..m, Δ, {Yj^ρ}j=0..m, Δ^ρ, R ).

The adversary succeeds in the computational GT-XPDH game if it outputs R^ρ ∈ GT. In the decisional GT-XPDH-DEC variant the challenger additionally samples b ←R {0,1} and sets

W := R^ρ if b = 1, and
W := U for U ←R GT if b = 0,

giving W to the adversary, whose goal is to recover b. The advantages are defined in the usual way: for a computational adversary

Adv_GT-XPDH(A) := Pr[A outputs R^ρ],

and for a decisional adversary

Adv_GT-XPDH-DEC(A) := |Pr[A outputs 1 | b = 1] − Pr[A outputs 1 | b = 0]|.

---

## Lemma 1 (Uniform "pairing form" of R)

For u ←R Zr* and v ←R Zr, the element

R0 := e(g1^u, g2^v) = gT^{uv}

is uniform in GT and independent of all other sampled values. Indeed, for any t ∈ Zr,

Pr[uv = t] = ∑_{u∈Zr*} Pr[u] · Pr[v = t·u^{-1}] = (r−1)/((r−1)·r) = 1/r,

so uv is uniform in Zr, implying that R0 is uniform in GT. Because the samplings of u and v are independent of ρ and of {Yj, Δ}, the value R0 is jointly independent of those elements as required.

Consequently, the GT-XPDH game is equivalent to the variant in which the challenger sets R = e(g1^u, g2^v) for fresh uniformly random u ∈ Zr*, v ∈ Zr. Moreover, R0 is independent not only of ρ and {Yj, Δ}, but also of their powered forms {Yj^ρ} and Δ^ρ, which are functions of X = g2^ρ and the independently sampled {Yj, Δ}.

### Lemma 2 (Independence of PVUGC anchor from armed bases)

Let (vk, x) be any fixed Groth16 statement. The Groth16 verification target is:
```
R(vk, x) = e([α]_1, [β]_2) · e(L(x), [γ]_2)
```
where L(x) = Σᵢ xᵢ·ICᵢ is the public-input linear combination.

**Key observation:** The armed bases {D_pub, D_j, D_δ} are derived from {[β]_2, b_g2_query (witness columns), [δ]_2}. Critically, **[γ]_2 is never armed**.

**Independence claim:** Since [γ]_2 ∉ span{armed bases}, the component e(L(x), [γ]_2) in R(vk,x) cannot be computed from the armed transcript alone. The adversary can compute e([α]_1, D_pub) and other pairings with armed bases, but these never produce terms involving [γ]_2^ρ.

**For the reduction:** We treat R(vk, x) as a fixed statement-derived GT element. The reduction embeds the DDH challenge element Y = g2^v into [γ]_2, allowing the simulator to detect whether the adversary computed R(vk, x)^ρ. This works because R(vk, x) contains a factor e(L(x), [γ]_2) that depends on [γ]_2, which the adversary cannot access in armed form.

---

## Theorem 1 (Tight reduction to DDH in G2)

Let A be any PPT adversary for GT-XPDH with success probability ε. There exists a PPT algorithm B that solves DDH in G2 with advantage at least ε − 1/r. The reduction is tight: B makes a single black-box call to A and performs only a constant number of pairings.

### DDH_G2 game

The DDH challenger samples ρ, v ←R Zr, sets X := g2^ρ and Y := g2^v, and returns

(g2, X, Y, T)

where either T = g2^{ρv} (the Diffie–Hellman case) or T ←R G2 (the random case). The adversary must decide which distribution it received.

### Construction of B

Given (g2, X, Y, T) from the DDH challenger:

1. Embed the exponent. Sample independent coefficients α0, …, αm, αΔ ←R Zr and set
   Yj := g2^{αj},   Yj^ρ := X^{αj},   Δ := g2^{αΔ},   Δ^ρ := X^{αΔ}.
   This matches the distribution in the GT-XPDH game because X = g2^ρ.
2. Program R. Using the lemma, sample u ←R Zr* and set
   R := e(g1^u, Y) = e(g1^u, g2^v).
3. Run A. Provide ({Yj}, Δ, {Yj^ρ}, Δ^ρ, R) to A and record its output S.
4. Decide. Compute
   T' := e(g1^u, T) ∈ GT
   and output “DH” if and only if S = T'.

### Correctness analysis

- If T = g2^{ρv}, then
  T' = e(g1^u, g2^{ρv}) = e(g1^u, g2^{v})^ρ = R^ρ.
  Hence S = T' exactly when A solves the GT-XPDH instance, which occurs with probability ε.
- If T ←R G2, then by bilinearity T' = e(g1^u, T) is uniform in GT and independent of S (since S = R^ρ). Therefore Pr[S = T'] = 1/r.

The distinguishing advantage of B is thus at least ε − 1/r. Consequently DDH hardness in G2 implies both the computational and decisional variants of GT-XPDH.

### Correlated GT-XPDH (PVUGC form)

PVUGC never samples an independent random R; instead it derives
```
R(vk, x) = e([α]_1, [β]_2) · e(IC(x), [γ]_2)
```
from the verifying key and public input. The protocol enforces five guardrails:

1. `[γ]_2` never appears among the armed bases (only the aggregated public B-column, witness-only B columns, and `[δ]_2` are armed).
2. Every public input wire participates in a non-zero C-column so that IC(x) ≠ 0.
3. CRS hygiene holds: `[γ]_2 ∉ span{[β]_2, b_g2_query, [δ]_2}`.
4. Each arming uses a fresh exponent ρ.
5. Never arm any G₁ element (arming U^ρ would reveal e(U, [γ]_2)^ρ via public pairings).

Under these conditions, **R(vk, x) contains a factor e(L(x), [γ]_2) that cannot be computed from the armed transcript** since [γ]_2^ρ is never published (Lemma 2). We define the **correlated GT-XPDH game** as: armed bases {D_pub, D_j, D_δ} are derived from (vk, x) under the guardrails, the challenger samples ρ, and sets R = R(vk, x). An adversary wins if it outputs R^ρ.

### Theorem 1′ (Tight DDH reduction for the correlated game)

Let A break the correlated GT-XPDH game with advantage ε. Construct B against DDH in G2 just as before, except that:

1. Embed the DDH challenge element Y = g2^v as `[γ]_2` inside the CRS (this is consistent with the hygiene rule).
2. Program `[α]_1 = g1^u` with u ←R Z_r^* and keep the public input x fixed so IC(x) is known.
3. Publish the armed transcript derived from vk along with R(vk, x) = e(g1^u, [β]_2) · e(IC(x), Y). (The simulator can compute `[β]_2^{ρ}` as X^{b} because it chose `[β]_2 = g_2^{b}` and the DDH challenger supplies X = g_2^{ρ}`.)

If the DDH challenge is real (T = g2^{ρv}), then
```
R(vk, x)^ρ = e(g1^u, [β]_2)^ρ · e(IC(x), Y)^ρ = e(g1^u, [β]_2^ρ) · e(IC(x), T),
```
and A’s output lets B compare against e(IC(x), T) exactly as in Theorem 1 after cancelling the known `[β]_2^ρ` term. If the challenge is random, the comparison succeeds only with probability 1/r. Thus B decides DDH with advantage at least ε − 1/r, showing that SXDH implies security for PVUGC even in the correlated setting.

---

## Theorem 2 (Algebraic GBGM bound)

In the algebraic generic bilinear group model, let A issue at most q oracle queries (group operations in G1, G2, GT, and pairings). Then

Adv_GT-XPDH(A) ≤ ~O(q^2 / r).

Sketch. Assign formal indeterminates a, i_x to the G₁ sources and y_β, y_γ, y_δ, {y_j} to the G₂ sources. Every GT handle maintained by A is labeled with an explicit polynomial E_H in these variables. Pairing with a masked right leg Y^ρ ∈ {D_pub, D_j (j>ℓ), D_δ} contributes a monomial of the form ρ·L(U)·y_* (degree ≤ 3), where L(U) is the linear form describing the left leg U ∈ G₁ and y_* ∈ {y_pub, y_j (j>ℓ), y_δ}. Operations inside G_T add such polynomials and scale them by known integers, so the ρ-bearing part of any reachable E_H lies in

    ρ · span{ y_pub, y_j (j>ℓ), y_δ }

and never includes a ρ·y_γ term. The target exponent is E_* = ρ·r_* = ρ·(a·y_β + i_x·y_γ), whose ρ·y_γ coefficient equals i_x ≠ 0 for valid statements. Therefore E_H = E_* can hold only via an accidental algebraic equality among the ≤ q produced handles. The standard algebraic/generic-group collision analysis (Schwartz–Zippel style) bounds this probability by ~O(q^2 / r). ∎

---

## Corollary (PVUGC No-Proof-Spend)

Fix a statement (vk, x). Let the statement-only bases {Yj}, Δ be derived from vk (excluding γ2), and require an accepting GS attestation before any G1 witnesses may appear inside pairings. For a fresh exponent ρi sampled per armer, and given only the public data ({Yj^{ρi}}, Δ^{ρi}, R(vk, x)), computing

Mi := R(vk, x)^{ρi}

without an accepting attestation is infeasible:

- GBGM: the success probability is at most ~O(q^2 / r).
- SXDH / DDH in G2: any PPT adversary for the computation gives a PPT DDH_G2 solver with essentially the same advantage (Theorem 1).

Consequently the PVUGC key Ki = Hash(ser_GT(Mi) ∥ …) remains hidden and the adaptor cannot be finalized without producing a valid attestation.

---

## Self-decapper resistance

**Security dependency.** Under public-(B) aggregation, $[\gamma]_2$ exclusion, and public-output coverage, let
$$
T := \left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j, Y_j)\right) \cdot e(X^{(B)}_\delta, [\delta]_2)
$$
be the publicly evaluable B-leg aggregation. Any tuple that makes GS-PPE hold without a valid Groth16 proof must solve
$$
e(C, [\delta]_2) = R(\mathsf{vk}, x) \cdot T^{-1},
$$
i.e., discrete logarithm in $\mathbb{G}_T$. Therefore a "self-decapper" would have to solve discrete logarithms across the pairing (e.g., recover $z = \log_{g_T}(R \cdot T^{-1})$ and either $\log_{g_2}([\delta]_2)$ or $\log_{g_1}(C)$). The PPE constraint ensures that honest proofs satisfy the verification equation.

---

## Note on “DLIP” (target-group assumptions)

The above results do not rely on any additional GT-side assumptions. One may still cite target-group assumptions such as GT-DLIN/DLIP when considering alternate formulations in which R is algebraically derived from public GT combinations, but they are unnecessary for the GT-XPDH formulation used here (in which R is uniform and independent).

---

## Summary

- GT-XPDH tightly reduces to DDH in G2; thus SXDH (using only the G2 half) suffices.
- In the algebraic GBGM the success probability is bounded by ~O(q^2 / r).
- PVUGC’s No-Proof-Spend property follows directly under these standard assumptions.

