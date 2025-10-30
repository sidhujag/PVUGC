GT-XPDH Reduction to DDH in G2 (and Generic-Model Bound)

This note formalizes the GT-XPDH ("external power in GT") assumption and records:

- a tight black-box reduction from GT-XPDH to DDH in G2, hence that SXDH implies GT-XPDH, and
- the algebraic generic bilinear group (GBGM) bound of Õ(q² / r) for any adversary making q oracle calls.

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

is uniform in GT and independent of all other sampled values. Indeed, since u is invertible modulo r, the product uv is uniform in Zr, implying that R0 is uniform in GT. Because the samplings of u and v are independent of ρ and of {Yj, Δ}, the value R0 is jointly independent of those elements as required.

Consequently, the GT-XPDH game is equivalent to the variant in which the challenger sets R = e(g1^u, g2^v) for fresh uniformly random u ∈ Zr*, v ∈ Zr. Moreover, R0 is independent not only of ρ and {Yj, Δ}, but also of their powered forms {Yj^ρ} and Δ^ρ, which are functions of X = g2^ρ and the independently sampled {Yj, Δ}.

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

---

## Theorem 2 (Algebraic GBGM bound)

In the algebraic generic bilinear group model, let A issue at most q oracle queries (group operations in G1, G2, GT, and pairings). Then

Adv_GT-XPDH(A) ≤ Õ(q² / r).

Sketch. In the GBGM, each handle in GT corresponds to an explicitly known polynomial over indeterminates representing the underlying exponents. The challenger’s inputs give rise to at most affine dependence on the unknown ρ through symbols e(X, Yj^ρ) and e(X, Δ^ρ). Because R is sampled independently of those symbols, the algebraic span of all handles obtained by the adversary contains no term in which R is multiplied by ρ. Producing R^ρ therefore requires the adversary to guess a new root of a non-zero degree-≤ q polynomial over Zr. The standard Schwartz–Zippel argument for algebraic adversaries bounds the success probability by Õ(q² / r).

---

## Corollary (PVUGC No-Proof-Spend)

Fix a statement (vk, x). Let the statement-only bases {Yj}, Δ be derived from vk (excluding γ2), and require an accepting DLREP+GS attestation before any G1 witnesses may appear inside pairings. For a fresh exponent ρi sampled per armer, and given only the public data ({Yj^{ρi}}, Δ^{ρi}, R(vk, x)), computing

Mi := R(vk, x)^{ρi}

without an accepting attestation is infeasible:

- GBGM: the success probability is at most Õ(q² / r).
- SXDH / DDH in G2: any PPT adversary for the computation gives a PPT DDH_G2 solver with essentially the same advantage (Theorem 1).

Consequently the PVUGC key Ki = Hash(ser_GT(Mi) ∥ …) remains hidden and the adaptor cannot be finalized without producing a valid attestation.

---

## Note on “DLIP” (target-group assumptions)

The above results do not rely on any additional GT-side assumptions. One may still cite target-group assumptions such as GT-DLIN/DLIP when considering alternate formulations in which R is algebraically derived from public GT combinations, but they are unnecessary for the GT-XPDH formulation used here (in which R is uniform and independent).

---

## Summary

- GT-XPDH tightly reduces to DDH in G2; thus SXDH (using only the G2 half) suffices.
- In the algebraic GBGM the success probability is bounded by Õ(q² / r).
- PVUGC’s No-Proof-Spend property follows directly under these standard assumptions.

