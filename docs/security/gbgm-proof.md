# PVUGC Security Analysis: GBGM and Computational Reduction

This document provides both a generic bilinear group model (GBGM) analysis and a computational reduction to DDH/SXDH for PVUGC decapsulation security with hardened arming. The Groth16 variant described here is **gated**: normal Groth16 callers stay on the standard CRS, while the PVUGC outer prover explicitly opts into the modified setup.

## Executive Summary

We prove PVUGC decapsulation security via two complementary approaches:
1. **Generic Model**: In GBGM, adversaries cannot produce R^ρ except with negligible probability.
2. **Computational Reduction**: Any adversary that outputs R^ρ under the hardened arming policy can be turned into a DDH breaker in G₂.

The computational reduction is pairing-aware and black-box, but it still relies on the SXDH/DDH assumption for the concrete CRS.

## System Overview

### Modified Groth16 Structure
Standard Groth16 uses the verification equation:
```
e(A,B) = e(α₁,β₂) · e(IC(x)/γ,γ₂) · e(C,δ₂)
```
where the instance commitment IC is scaled by 1/γ.

For PVUGC, we modify this to:
```
e(A,B) = e(α₁,β₂) · e(IC(x),γ₂) · e(C,δ₂)
```
where IC(x) is unscaled. We re-parameterize the proving key and verifier so that honest proofs satisfy this equation. One way to achieve this is to precompute queries `[(1-γ)/δ · f_i(τ)]₁` in the proving key and have the prover add their x-linear combination to C. Only the PVUGC outer circuit calls this generator/prover path; all other Groth16 users keep the original parameters.

#### Why This Convention Is Safe

**Soundness/Zero-knowledge/Extraction**: The adjustment is a CRS re-parameterization; it preserves the standard Groth16 arguments because the simulator/extractor receive the same linear combinations of trapdoor scalars. The benefit is purely notational: IC(x) remains unscaled, which lets us embed the DDH challenge by setting γ₂ directly to the challenge handle without ever needing its discrete log.

### PVUGC Anchor
```
R(vk,x) := e(α₁,β₂) · e(IC(x),γ₂)
```

### Hardened Arming Policy
Given ρ ← 𝔽ᵣ*, publish:
- D_pub = (β₂ + Σᵢ≤ℓ xᵢQᵢ)^ρ (aggregated public column)
- Dⱼ = Qⱼ^ρ for j > ℓ (individual witness columns)
- D_δ = δ₂^ρ (delta column)

Never publish γ₂^ρ or individual public column masks.

---

## Self-Contained Witness Encryption Scheme

### Instance
R1CS with polynomials uᵢ, vᵢ, wᵢ ∈ 𝔽ᵣ[X] of degree ≤ n-1, t(X) = Xⁿ - 1, and assignment a = (a₀,...,aₘ) such that:
```
(Σᵢ₌₀ᵐ aᵢuᵢ(τ)) · (Σᵢ₌₀ᵐ aᵢvᵢ(τ)) ≡ Σᵢ₌₀ᵐ aᵢwᵢ(τ) mod t(τ)
```
with a₀ = 1, (a₁,...,aₗ) public, (aₗ₊₁,...,aₘ) witness.

### CRS (Outer Groth16)
Generators g₁ ∈ G₁, g₂ ∈ G₂. Trapdoors τ, α, β, γ, δ ← 𝔽ᵣ. Publish:
- α₁ = g₁^α, β₂ = g₂^β, γ₂ = g₂^γ, δ₂ = g₂^δ
- Qᵢ = [vᵢ(τ)]₂ for all i (true Groth16 queries)
- ICᵢ = [fᵢ(τ)]₁ where fᵢ are Groth16 IC polynomials WITHOUT 1/γ

**Public pk/vk elements.** Besides α₁, β₂, γ₂, δ₂, {Qᵢ}, and {ICᵢ}, the proving key exposes the usual Groth16 G₁ queries ([A_i(τ)]₁, [C_i(τ)]₁, and monomials [τ^k]₁ up to degree n), plus any compiler-fixed linear combinations. The verifying key contains α₁, β₂, γ₂, δ₂, and the ICᵢ. None of these G₁ elements are ever masked by ρ.

The pk/vk are parameterized so honest proofs satisfy:
```
e(A,B) = e(α₁,β₂) · e(IC(x),γ₂) · e(C,δ₂)
```

### WE.Encrypt(vk, x)
Sample fresh ρ ← 𝔽ᵣ*. Publish ciphertext CT = (R, D_pub, {Dⱼ}ⱼ>ℓ, D_δ) where:
```
R := e(α₁,β₂) · e(IC(x),γ₂)
D_pub := (β₂ + Σᵢ≤ℓ xᵢQᵢ)^ρ
Dⱼ := Qⱼ^ρ for j > ℓ
D_δ := δ₂^ρ
```
**Hygiene**: Never publish any right-leg with a γ₂ component.

### WE.Decrypt(CT, w)
Given witness w (values aₗ₊₁,...,aₘ), construct Groth16 proof (A,B,C) for (vk,x) and compute:
```
M := e(A, D_pub) · ∏ⱼ>ℓ e(bⱼA, Dⱼ) · e(sA, D_δ) · e(C, D_δ)^(-1)
```
Output K := H(ser_GT(M)). **Correctness**: As shown below, M = R^ρ.

---

## Part I: Generic Bilinear Group Model Analysis

### Algebraic GBGM with Pairing

Each handle carries an explicit label polynomial over formal indeterminates; in the GBGM these symbols (ρ, y_γ, y_β, {yⱼ}, y_δ) together with any adversary-chosen G₁ seeds are assumed to be algebraically independent. The adversary may form and pair any public G₁ handle available in the pk/vk (e.g., [A_i(τ)]₁, [C_i(τ)]₁, [τ^k]₁) or any linear combination thereof.

- **G₂ basis symbols**: y_β, y_γ, y_δ, {yⱼ}; **G₁ basis**: a (for α₁) and prover-chosen symbols; **mask symbol**: ρ
- A G₁ handle U has label L_U linear in G₁ symbols; a G₂ handle Y has label R_Y linear in {y_β, y_γ, y_δ, yⱼ}
- Pairing returns G_T handle with label: E = ρ·(L_U·R_Y) if Y is masked, or E = L_U·R_Y if Y is unmasked; consequently every G_T label is a polynomial of total degree at most 3 in the independent symbols (degree‑1 G₁ term × degree‑1 G₂ term × optional ρ mask).
- G_T multiplication/division add/subtract labels; raising to known integer scales the label

Only right-leg (G₂) elements are ever published with a ρ mask, so every ρ-dependent term in G_T must originate from pairing against a masked right leg.

### Armed Set

Masked right-legs:
- B_pub^ρ with label ρ·(y_β + Σᵢ≤ℓ xᵢyᵢ)
- Qⱼ^ρ with label ρ·yⱼ for j > ℓ
- δ₂^ρ with label ρ·y_δ

By hygiene, **no** masked right-leg has any y_γ component.

### Invariant (No ρ·y_γ)

By induction on adversary operations:

**Base**: Pairings with masked right-legs yield labels ρ·L_U·r(Y) where r(Y) ∈ span{y_β, yⱼ(j>ℓ), y_δ}; hence the ρ-part has no y_γ. Pairings with unmasked γ₂ produce L_U·y_γ with no ρ.

**Closure**: G_T multiplication/division add/subtract labels; scaling by known integer multiplies the whole label. None introduce ρ·y_γ if not present.

Let q denote the total number of oracle calls that can create new labels (pairing evaluations plus G_T operations that output fresh handles).

### Lemma (Reachable ρ-span)

Every G_T handle the adversary can produce has label:
```
E_H = ρ·F_H(y_β, yⱼ(j>ℓ), y_δ) + G_H(y_β, yⱼ, y_δ, y_γ)
```
with coefficient of ρ·y_γ equal to **0**.

### Target Label and GBGM Bound

Assuming IC(x) ≠ 0 (so i_x ≠ 0), R = e(α₁,β₂) · e(IC(x),γ₂) has label E_R = a·y_β + i_x·y_γ, so:
```
R^ρ: ρ·(a·y_β + i_x·y_γ)
```
whose ρ-part contains i_x·y_γ with i_x ≠ 0.

**GBGM Bound**: Equality H = R^ρ forces a non-trivial polynomial identity (the ρ·y_γ coefficient must vanish). For degree-3 polynomials over 𝔽_r obtained from at most q oracle queries, the algebraic-generic collision bound gives Pr[H = R^ρ] ≤ c·q²/r for a fixed constant c.

**Comment**: This is pairing-aware and doesn't assume (Σ aᵢuᵢ)(Σ aᵢvᵢ) is the only path; it permits any mixing in the τ-subspace and still concludes "no ρ·y_γ".

### Generic Attack on Unhardened Scheme

With individual public masks (β₂^ρ, Qᵢ^ρ for i≤ℓ), adversary can:
1. Lift identity e(γ_abc[i],γ₂) = e(Aᵢ(τ),β₂)·e(α₁,Bᵢ(τ))
2. Sum to get e(IC(x),γ₂^ρ)
3. Multiply by e(α₁,β₂^ρ) to recover R^ρ

This is the "(a+b)(x+y) → ax+by" attack that hardened arming prevents.

GBGM deliberately ignores any extra algebraic relations among CRS elements beyond these labels; the next section handles the concrete CRS under DDH/SXDH.

---

## Part II: Computational Reduction to DDH (pairing-aware, no uniqueness)

**Setting.** The outer SNARK is Groth16 with verifier equation
```
e(A,B) = e(α₁,β₂) · e(IC(x),γ₂) · e(C,δ₂).
```
**Notation.** G₁ and G₂ use additive group law internally (we still write Y^ρ for scalar multiplication); G_T is multiplicative.
PVUGC publishes only
```
D_pub = (β₂ + Σᵢ≤ℓ xᵢ Qᵢ)^ρ,   Dⱼ = Qⱼ^ρ (j>ℓ),   D_δ = δ₂^ρ,
```
and never any right-leg with a γ₂ component. Define R(vk,x)=e(α₁,β₂)·e(IC(x),γ₂).

### Theorem (PVUGC decap ⇒ DDH in G₂)

Let a PPT adversary 𝒜, with full pairing access and arbitrary G_T mixing, output M = R^ρ with probability ε. Then there exists a PPT distinguisher ℬ for DDH in G₂ with advantage at least ε - 1/r.

**Proof (explicit, pairing-aware).** Given a DDH challenge (g₂, X=g₂^ρ, Y=g₂^v, T), construct a real-looking PVUGC instance as follows.

1. **Program the structured CRS.** Sample τ, α, β, δ ∈ 𝔽_r. Set Qᵢ := [vᵢ(τ)]₂, β₂ := g₂^β, δ₂ := g₂^δ, γ₂ := Y, α₁ := g₁^α, and publish ICᵢ := [fᵢ(τ)]₁ with IC(x)=∑_{i=1}^ℓ x_i·ICᵢ ≠ 0. Using τ (which we chose) also compute the public G₁ pk queries ([A_i(τ)]₁, [C_i(τ)]₁, [τ^k]₁), matching the honest CRS.

2. **Publish armed right-legs** using scalar linearity (X = g₂^ρ):
```
D_pub = X^{β + ∑_{i≤ℓ} x_i v_i(τ)},   Dⱼ = X^{v_j(τ)} (j>ℓ),   D_δ = X^{δ}.
```

3. **Publish the anchor.** R := e(α₁,β₂)·e(IC(x),γ₂) = e(g₁^{α}, g₂^{β})·e(IC(x), Y).

4. **Run 𝒜** on the simulated instance; obtain M★ ∈ G_T.

5. **Decide DDH.** Compute
```
M' := M★ · e(α₁,β₂^ρ)^{-1}
     = M★ · e(g₁^{α}, X^{β})^{-1},
T' := e(IC(x), T).
```
Output “DH” iff M' = T'.

- If T = Y^ρ (DH): T' = e(IC(x),Y)^ρ = e(IC(x),γ₂)^ρ. When 𝒜 succeeds, M★ = R^ρ = e(α₁,β₂)^ρ · e(IC(x),γ₂)^ρ, hence M' = T'. Success probability ε.

- If T is uniform in G₂: T' is uniform in G_T and independent of M'. Thus Pr[M'=T']=1/r.

Therefore Adv^DDH_G₂(ℬ) ≥ ε - 1/r. ∎

**Remarks.** The simulation is exact for (β₂,Qᵢ,δ₂) and their masks (published as known scalar multiples of X), and γ₂ is independent as in the honest CRS. The reduction treats 𝒜 as a black box and requires no uniqueness assumptions in G_T.

### Why Any Valid Proof Gives R^ρ

For any valid (A,B,C) satisfying the verifier equation and any decomposition B = B_pub + Σ_{j>ℓ} bⱼ Qⱼ + s·δ₂,
```
M = e(A,B_pub^ρ) · ∏_{j>ℓ} e(bⱼ A, Qⱼ^ρ) · e(sA, δ₂^ρ) · e(C, δ₂^ρ)^{-1}
  = (e(A,B) · e(C,δ₂)^{-1})^ρ
  = (e(α₁,β₂) · e(IC(x),γ₂))^ρ
  = R^ρ.
```
All group laws are multiplicative in G_T; the sum that defines B is in G₂. The identity holds for every valid proof, independent of how the witness was obtained.

---

## Security Requirements

1. **Never publish γ₂^ρ** or any element with γ₂ component
2. **Ensure IC(x) ≠ 0** (salt if needed)
3. **Sample CRS independently** with γ₂ ∉ span{β₂,Qⱼ,δ₂}
4. **Use fresh ρ per instance**

---


## Implications

### What This Proves
- PVUGC decapsulation is as hard as DDH in G₂ (SXDH)
- Security holds even with individual witness columns exposed
- GT-level "mix and match" attacks would break DDH
- The reduction works black-box without any uniqueness assumptions

### What This Addresses
Under DDH/SXDH, any GT-level mix-and-match strategy that succeeds with non-negligible probability would immediately give a DDH break. Relative to these assumptions, this addresses concerns about GT-level adversaries who can:
- Mix witness columns arbitrarily
- Exploit pairing structures beyond R1CS constraints
- Use any algebraic identity in GT
- Find alternative polynomial relations that bypass rank-1 structure

Any such attack succeeding with non-negligible probability breaks DDH/SXDH.

### Why the Groth16 Modification Matters
The removal of the 1/γ scaling factor from IC(x) is essential for the security reduction and is only enabled for the PVUGC outer prover:
- **Standard Groth16**: IC scaled by 1/γ would require knowing γ to embed the DDH challenge
- **Modified version (PVUGC-only path)**: Unscaled IC allows programming γ₂ = Y without knowing its discrete log, while the rest of the ecosystem continues to use the default CRS
- **Security preserved**: The re-parameterization maintains all Groth16 security properties


---

## Conclusion

PVUGC decapsulation security rests on two standard assumptions:
1. **Groth16 soundness** (for proof verification)
2. **DDH in G₂/SXDH** (for decapsulation hardness via the reduction)