# Generic Bilinear Proof for PVUGC Decapsulation (Hardened Scheme)

We analyze decapsulation in the algebraic generic bilinear group model (GBGM). The adversary receives the entire public transcript for a fixed statement (vk, x) and may fabricate arbitrary G₁ points, evaluate any pairings, and combine the results in G_T. We show that with the hardened arming policy—aggregate the public B-column and never arm γ₂—no such adversary can recover the KEM key M = R(vk, x)^ρ except with negligible probability. We also show the original per-public arming is generically breakable, matching the intuition that a decryptor could "separate" (a+b)(x+y) into ax+by inside G_T.

## Setup (algebraic GBGM)

- Prime-order (G₁,G₂,G_T) with a non-degenerate bilinear pairing e. In the algebraic GBGM every group handle carries its (hidden) linear form in a set of formal indeterminates; the adversary is restricted to algebraic manipulations (additions, known-integer scalings, pairings).

- **CRS / vk:**
  - G₂: independently sampled β₂, γ₂, δ₂ and query points Q_1,…,Q_m, with γ₂ ∉ span{β₂, Q_j, δ₂}.
  - G₁: α₁ and the instance commitment IC(x) (assumed non-zero; we salt deterministically if needed).
  - Exponent indeterminates: a, i_x for α₁, IC(x), y_β, y_γ, y_δ, y_j for the G₂ bases, and u_1, u_2, … for adversary-chosen G₁ seeds.

The only programmed relation is

    y_pub = y_β + Σ_{i=1}^{ℓ} x_i y_i,

corresponding to the aggregated public column B_pub(vk,x).

- **Arming (hardened):** sample fresh ρ ← 𝔽_r^* and publish only

    { B_pub^ρ, Q_j^ρ (j>ℓ), δ₂^ρ }.

We never publish γ₂^ρ nor individual public masks β₂^ρ or Q_i^ρ for i≤ℓ.

- **KEM anchor:** R = e(α₁,β₂)·e(IC(x),γ₂). The decapper's target is M = R^ρ.

## Reachable subgroup in G_T

Define the armed right-legs

    ArmedRight^ρ := { B_pub^ρ, Q_j^ρ (j>ℓ), δ₂^ρ }

and the subgroup they generate in G_T

    𝓗 := ⟨ e(U, Y^ρ) : U ∈ G₁, Y^ρ ∈ ArmedRight^ρ ⟩ ⊆ G_T.

**Lemma 1 (Reachability).** In the algebraic GBGM, the ρ-dependent part of the exponent of any reachable G_T handle lies in

    ρ · span{ y_pub, y_j (j>ℓ), y_δ }.

In particular, no sequence of oracle queries can produce any handle whose exponent contains a non-zero ρ·y_γ term (equivalently, no e(·,γ₂^ρ) contribution can appear).

**Proof sketch.** Pairing with a masked right leg produces monomials of the form ρ·L(U)·y_* (degree ≤3 in the indeterminates); pairing with unmasked CRS elements produces terms with no ρ; operations in G_T add exponents and scale by known integers. Thus every reachable exponent polynomial has degree ≤3 and its ρ-portion is confined to the span above. ∎

## Decapsulation hardness in GBGM

Let r_* = a·y_β + i_x·y_γ so that R = g_T^{r_*}. The decapper must output R^ρ = g_T^{ρ·r_*}.

**Lemma 2.** Any algebraic generic adversary making at most q oracle queries satisfies

    Pr[outputs R^ρ] ≤ c · q²/r

for an absolute constant c.

**Proof idea.** Every reachable exponent has the form

    E_H(𝓥) = ρ·F_H(y_pub,{y_j}_{j>ℓ},y_δ;u) + G_H(y_β,y_γ;u) + c_H·r_*,

with c_H ∈ ℤ. By Lemma 1, the coefficient of ρ·y_γ in E_H is always zero, while in the target E_* = ρ·r_* = ρ·(a·y_β + i_x·y_γ) it equals i_x. In the algebraic GBGM, the only way those polynomials can coincide is via a spurious algebraic equality among the ≤q produced handles—an event bounded by O(q²/r); see the standard generic-group collision analysis. ∎

**Interpretation.** The adversary may "mix" pairings arbitrarily in G_T, but all ρ-bearing terms remain trapped in 𝓗. Because R^ρ carries an unarmed γ₂^ρ leg, it lies outside 𝓗 (unless IC(x)=0, which we exclude/salt). Hence mixing cannot reach M.

**Corollary (GT-XPDH/SXDH view).** Equivalently, computing R^ρ from {Y, Y^ρ} breaks the masked-basis external Diffie–Hellman problem (GT-XPDH). In a selectively programmed instance one can cancel the armed β-part to recover e(IC(x),γ₂^ρ), directly solving XPDH—again yielding an O(q²/r)-type bound under SXDH.

## Unhardened scheme ⇒ generic break

If the arming phase also publishes per-public masks (β₂^ρ, Q_i^ρ for i ≤ ℓ), the adversary gains masked handles for every B-column. In GBGM it can then lift the identities

    e(γ_{abc}[i],γ₂) = e(A_i(τ),β₂)·e(α₁,B_i(τ))

under ρ and sum over i to obtain e(IC(x),γ₂^ρ); multiplying by e(α₁,β₂^ρ) recovers R^ρ without a witness. This is exactly the "(a+b)(x+y) ⇒ ax+by" phenomenon and motivates the hardened rule (aggregate the public column; never arm γ₂).

## Hygiene (required)

1. Never publish γ₂^ρ (nor any right-hand element with a γ₂ component).
2. Ensure IC(x) ≠ 0 (salt deterministically if needed).
3. Sample CRS elements independently, with γ₂ ∉ span{β₂,Q_j,δ₂}.
4. Use a fresh ρ for every instance.

## Instantiation note

In PVUGC, Y_0 = B_pub(vk,x) aggregates the constant and all public B-columns; Y_j for j>0 enumerate witness-only entries of b_g2_query. The arming phase publishes only Y_0^ρ, Y_j^ρ for j>ℓ, and δ₂^ρ; DLREP/GS artifacts never add new ρ-bearing bases, and γ₂ is excluded by construction. Thus the concrete system matches the abstract interface used above.