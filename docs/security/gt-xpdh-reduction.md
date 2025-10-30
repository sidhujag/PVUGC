GT-XPDH Reduction to DDH in G2 (and Generic-Model Bound)

This doc formalizes GT-XPDH (“external power in GT”) and proves:
- A tight black-box reduction to DDH in G2 (hence implied by SXDH), and
- A standard algebraic generic bilinear group bound (~O(q^2/r)).

It also states the PVUGC corollary for No-Proof-Spend. (All probabilities are over the challenger’s and adversary’s randomness.)

---

Setting
Let (G1, G2, GT, e) be asymmetric prime-order bilinear groups of order r. Let g1 ∈ G1, g2 ∈ G2 be generators and gT := e(g1, g2) generate GT. Encodings are canonical and efficiently testable (so equality tests in GT are exact).

SXDH means DDH is hard in both G1 and G2; below we only need the G2 half (DDH in G2).

---

Problem (GT-XPDH: external power in GT)
Let m ≥ 0. Sample independent statement-only bases Y0,…,Ym, Δ ←$ G2, sample ρ ←$ Zr*, and sample R ←$ GT uniformly and independently.
Give the adversary ( {Yj}j=0..m, Δ, {Yj^ρ}j=0..m, Δ^ρ, R ). Goal: output R^ρ ∈ GT.

We also consider the decisional variant GT-XPDH-DEC: given the same tuple and an extra W ∈ GT, decide whether W = R^ρ.

---

Lemma (Uniform “pairing form” of R)
For u ←$ Zr^*, v ←$ Zr, the element R0 := e(g1^u, g2^v) is uniform in GT and independent of ρ and {Yj, Δ}.

Thus, in GT-XPDH we may set R = e(g1^u, g2^v) without changing the distribution.

---

Theorem 1 (Tight reduction to DDH in G2)
If a PPT adversary A solves GT-XPDH with advantage ε, there is a PPT adversary B that solves DDH in G2 with advantage at least ε − 1/r. The reduction is tight (one call to A) and uses O(1) pairings.

DDH_G2 game: Challenger samples g2^ρ, g2^v and gives (g2, g2^ρ, g2^v, T), where T = g2^{ρv} (DH) or T ←$ G2 (random). Goal: decide which.

Reduction B:
1) Embed exponent: For random α0,…,αm, αΔ ←$ Zr, set Yj := g2^{αj}, Yj^ρ := (g2^ρ)^{αj}, Δ := g2^{αΔ}, Δ^ρ := (g2^ρ)^{αΔ}.
2) Program R: Pick u ←$ Zr^*. Set R := e(g1^u, g2^v). (Uniform by lemma.)
3) Run A on ({Yj}, Δ, {Yj^ρ}, Δ^ρ, R) to get S.
4) Decide: Compute T' := e(g1^u, T) ∈ GT and output “DH” iff S = T'.

Correctness: If T = g2^{ρv}, then T' = e(g1^u, g2^{ρv}) = (e(g1^u, g2^v))^ρ = R^ρ, so S = T' with prob. ε. If T ←$ G2, then T' is uniform in GT and independent of S = R^ρ, so Pr[S = T'] = 1/r. Hence Adv_DDH_G2(B) ≥ ε − 1/r.

Consequence: Under SXDH (indeed, under DDH in G2), GT‑XPDH is hard. No target‑group assumption is required for the computational or decisional variants.

---

Theorem 2 (Algebraic Generic Bilinear Group Bound)
In the algebraic generic bilinear group model (GBGM), any adversary A making at most q oracle queries (group ops in G1, G2, GT, pairings) satisfies Adv_GT‑XPDH(A) ≤ ~O(q^2/r) (i.e., O(q^2/r) up to polylog factors in q).

Sketch: Handles in GT span Zr-linear combinations of bilinear images e(X, ·) where “·” ∈ {Yj, Δ, Yj^ρ, Δ^ρ}; these carry at most affine dependence on ρ. In the algebraic model, all GT handles the adversary forms lie in the Zr-span of e(X, Yj), e(X, Δ), e(X, Yj^ρ), e(X, Δ^ρ); the fresh symbol R never appears with a ρ‑bearing operand, so creating R^ρ forces a new monomial R·ρ that cannot be generated from the span. By Schwartz–Zippel counting in the algebraic model, success ≤ ~O(q^2/r).

---

Corollary (PVUGC No‑Proof‑Spend)
Fix (vk, x). Let statement‑only bases {Yj}, Δ be derived from vk (excluding γ2), and require an accepting DLREP+GS attestation to introduce the G1 witnesses into pairings. For any ρ_i sampled per armer, given only ({Yj^{ρ_i}}, Δ^{ρ_i}, R(vk, x)), computing M_i := R(vk, x)^{ρ_i} without an accepting attestation is infeasible:
- Under GBGM: success ≤ Õ(q^2/r).
- Under SXDH (DDH in G2): any PPT algorithm for M_i yields a PPT DDH_G2 solver with essentially the same advantage (Theorem 1).

Hence the PVUGC key K_i = Hash(ser_GT(M_i) || …) remains hidden and the adaptor cannot be finalized without a valid attestation.

---

Note on “DLIP” (target‑group assumptions)
The results above do not require any GT‑side assumption. We may still cite GT‑DLIN/DLIP if formulating alternates where R is synthetically built from GT combinations, but it is not needed for GT‑XPDH as we have defined (R uniform and independent).

---

Summary
- GT‑XPDH ≤ DDH in G2 (tight). Therefore GT‑XPDH is implied by SXDH (using only the G2 half).
- GBGM bound: ~O(q^2/r) (polylog factors in q suppressed).
- PVUGC No‑Proof‑Spend follows under standard assumptions.

