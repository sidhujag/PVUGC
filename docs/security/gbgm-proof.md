# PVUGC Security Analysis: GBGM and Computational Reduction

This document provides both a generic bilinear group model (GBGM) analysis and a computational reduction to DDH/SXDH for PVUGC decapsulation security with hardened arming.

## Executive Summary

We prove PVUGC decapsulation security via two complementary approaches:
1. **Generic Model**: In GBGM, adversaries cannot produce R^ρ except with negligible probability
2. **Computational Reduction**: Any adversary producing R^ρ (by ANY method) breaks DDH in G₂

The computational reduction is the stronger result, providing standard-model security without generic assumptions.

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
where IC(x) is unscaled. We re-parameterize the proving key and verifier so that honest proofs satisfy this equation. One way to achieve this is to precompute queries `[(1-γ)/δ · f_i(τ)]₁` in the proving key and have the prover add their x-linear combination to C.

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

## Part I: Generic Bilinear Group Model Analysis

### Setup (Algebraic GBGM)

- Prime-order groups (G₁,G₂,G_T) with pairing e
- Adversary restricted to algebraic operations
- CRS elements: α₁, β₂, γ₂, δ₂, {Qⱼ}
- Formal indeterminates: a, i_x, y_β, y_γ, y_δ, {yⱼ}

### Reachable Subgroup in G_T

**Definition**: Armed right-legs
```
ArmedRight^ρ := {B_pub^ρ, Qⱼ^ρ (j>ℓ), δ₂^ρ}
```

**Lemma 1 (Reachability)**: In algebraic GBGM, any reachable G_T element has ρ-dependent exponent in:
```
ρ · span{y_pub, yⱼ (j>ℓ), y_δ}
```
Crucially, no ρ·y_γ terms can appear.

### Decapsulation Hardness in GBGM

**Lemma 2**: Any algebraic generic adversary making q queries satisfies:
```
Pr[outputs R^ρ] ≤ c·q²/r
```

**Proof sketch**: The target R^ρ contains ρ·i_x·y_γ, but reachable elements have coefficient 0 for ρ·y_γ. Equality requires spurious collision (probability ≤ q²/r).

### Generic Attack on Unhardened Scheme

With individual public masks (β₂^ρ, Qᵢ^ρ for i≤ℓ), adversary can:
1. Lift identity e(γ_abc[i],γ₂) = e(Aᵢ(τ),β₂)·e(α₁,Bᵢ(τ))
2. Sum to get e(IC(x),γ₂^ρ)
3. Multiply by e(α₁,β₂^ρ) to recover R^ρ

This is the "(a+b)(x+y) → ax+by" attack that hardened arming prevents.

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

1. **Program the structured CRS.** Sample α₀,{αᵢ},α_δ ∈ 𝔽_r. Set β₂:=g₂^{α₀}, Qᵢ:=g₂^{αᵢ}, δ₂:=g₂^{α_δ}, γ₂:=Y. Sample u←𝔽_r^* and set α₁:=g₁^u. Publish IC(x) for a fixed x with IC(x)≠0.

2. **Publish armed right-legs** using scalar linearity in G₂ (additive in G₂, multiplicative in G_T):
```
D_pub = α₀·X + Σᵢ≤ℓ xᵢ (αᵢ·X),   Dⱼ = αⱼ·X (j>ℓ),   D_δ = α_δ·X.
```

3. **Publish the anchor** R:=e(α₁,β₂)·e(IC(x),γ₂)=e(g₁^u,g₂^{α₀})·e(IC(x),Y).

4. **Run 𝒜** on the simulated instance; obtain M★ ∈ G_T.

5. **Decide DDH (corrected rule).** Compute
```
M' := M★ · e(α₁,β₂^ρ)^{-1}
     = M★ · e(g₁^u, α₀·X)^{-1},
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
Under DDH/SXDH, any GT-level mix-and-match strategy that succeeds with noticeable probability would immediately give a DDH break, so relative to those assumptions this addresses concerns about GT-level adversaries who can:
- Mix witness columns arbitrarily
- Exploit pairing structures beyond R1CS constraints
- Use any algebraic identity in GT
- Find alternative polynomial relations that bypass rank-1 structure

Any such attack succeeding with non-negligible probability breaks DDH/SXDH.

### Why the Groth16 Modification Matters
The removal of the 1/γ scaling factor from IC(x) is essential for the security reduction:
- **Standard Groth16**: IC scaled by 1/γ would require knowing γ to embed the DDH challenge
- **Modified version**: Unscaled IC allows programming γ₂ = Y without knowing its discrete log
- **Security preserved**: The re-parameterization maintains all Groth16 security properties


---

## Conclusion

PVUGC decapsulation security rests on two standard assumptions:
1. **Groth16 soundness** (for proof verification)
2. **DDH in G₂/SXDH** (for decapsulation hardness via the reduction)