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

### IC-Correction Terms and the ρ·y_γ Invariant

We now make explicit how IC-correction interacts with the GBGM labels and show that it preserves the key invariant that no adversarial GT handle ever contains a ρ·y_γ monomial.

#### GBGM setup and hygiene axioms

We work in the algebraic GBGM with pairing and the following formal symbols:

- **Mask symbol**: ρ
- **G₂ basis symbols**:
  - y_β for β₂
  - y_γ for γ₂
  - y_δ for δ₂
  - yⱼ for Qⱼ := [vⱼ(τ)]₂
- **G₁ basis symbols**: a (for α₁) plus any prover‑chosen seeds.

Every G₂ handle has a label linear in {y_β, y_γ, y_δ, yⱼ}. Every G₁ handle has a label linear in the G₁ basis symbols. Pairing and G_T operations act on labels as:

- If Y is unmasked (no ρ), then e(U,Y) has label L_U · R_Y.
- If Y is masked (Y^ρ), then e(U,Y^ρ) has label ρ · L_U · R_Y.
- G_T multiplication/division add/subtract labels, and exponentiation by known integers scales the label.

We formalize the implementation hygiene as GBGM axioms:

1. **Axiom H1 (no masked γ‑basis).**  
   The only G₂ elements that are ever masked and published are β₂, δ₂, and the Qⱼ. Equivalently, every masked right‑leg Y^ρ has label
   R_Y ∈ span{y_β, y_δ, yⱼ},
   and **no masked right‑leg has any y_γ component**.

2. **Axiom H2 (no γ‑bearing G₁ paired with γ₂ in public equations).**  
   Some G₁ queries (the IC‑correction terms) contain γ in their scalar, but the only public pairing equation that involves γ₂ is
   e(IC(x), γ_2),
   where IC(x) is built from γ‑free bases [fᵢ(τ)]₁. G₁ elements that involve γ in their scalar (such as IC‑correction) are only ever paired with δ₂ or δ₂^ρ, **never with γ₂**, in any published relation.

These two axioms are exactly what this convention and the PVUGC plumbing enforce in code.

#### IC and IC-correction labels

For each public index i we have:

- ICᵢ = [f_i(τ)]₁ from `gamma_abc_g1_raw[i]`, with no γ in its label; γ may appear only inside the scalar polynomial f_i(τ).
- IC_corrᵢ = [((1-γ)/δ) · f_i(τ)]₁ from `ic_correction_g1[i]`.

In the GBGM, γ, δ, and f_i(τ) are **field scalars**, not new basis symbols. Thus:

- The G₁ label of ICᵢ is some linear form L_i in the G₁ bases.
- The G₁ label of IC_corrᵢ is just a scalar multiple of the same form:
  L_i^{corr} = ((1-γ)/δ) · L_i,
  i.e., still linear in the same G₁ basis symbols. γ appears only as a scalar coefficient in front of L_i; it does **not** create a new G₂ basis symbol.

#### Pairings involving IC-correction

Now consider all pairings an adversary can form that involve IC_corr and public G₂ elements.

1. **With masked δ₂^ρ** (right‑leg label y_δ):
   e(IC_corrᵢ, δ_2^ρ) ⇒ label = ρ · L_i^{corr} · y_δ.  
   The ρ‑part is some scalar · y_δ. No y_γ appears.

2. **With masked D_pub = (β₂ + Σᵢ≤ℓ xᵢQᵢ)^ρ** (right‑leg label y_β + Σᵢ≤ℓ xᵢyᵢ):
   e(IC_corrᵢ, D_pub) ⇒ label = ρ · L_i^{corr} · (y_β + Σ_{k≤ℓ} x_k y_k).  
   The ρ‑part lies in the span of {y_β, y_k (k≤ℓ)} only.

3. **With masked witness columns Dⱼ = Qⱼ^ρ (j>ℓ)** (right‑leg label yⱼ):
   e(IC_corrᵢ, D_j) ⇒ label = ρ · L_i^{corr} · y_j.  
   Again, the ρ‑part is some scalar · yⱼ.

4. **With unmasked γ₂** (right‑leg label y_γ):
   e(IC_corrᵢ, γ_2) ⇒ label = L_i^{corr} · y_γ.  
   Here we do see y_γ, but **there is no ρ prefix**: this contributes only to the ρ‑free part of the label.

By Axiom H1, there are no other masked G₂ elements; by Axiom H2, IC_corr is never paired with γ₂^ρ (which doesn’t exist) or any γ₂‑contaminated masked base.

#### Lemma: IC-correction preserves the “no ρ·y_γ” invariant

We can now restate and prove the central invariant in the presence of IC‑correction.

**Lemma.** For every G_T handle H that the adversary can produce (using arbitrary algebraic combinations, pairings, and IC‑correction terms), its GBGM label has the form
E_H = ρ·F_H(y_β, y_j, y_δ) + G_H(y_β, y_j, y_δ, y_γ),
and the coefficient of ρ·y_γ in E_H is exactly 0.

*Proof.* We proceed by induction over the operations the adversary and oracles can perform.

- **Base cases (pairings).**

  - If the right‑leg is a masked base Y^ρ, then by Axiom H1 its label is in the span of {y_β, y_j, y_δ}. Thus
    label(e(U,Y^ρ)) = ρ · L_U · R_Y
    has ρ‑part in span{y_β, y_j, y_δ}, in particular with **no y_γ**. This covers all pairings with D_pub, Dⱼ, D_δ, including those where U = IC_corr.

  - If the right‑leg is unmasked γ₂, then
    label(e(U,γ_2)) = L_U · y_γ,
    which contains y_γ but **no ρ prefix**. So it only contributes to G_H, never to the ρ‑part.

- **Inductive step (G_T algebra).**  
  Suppose H₁, H₂ satisfy the lemma with labels
  E_{H_1} = ρ F_1 + G_1,   E_{H_2} = ρ F_2 + G_2,
  where F₁,F₂ depend only on (y_β, y_j, y_δ). Then:

  - Multiplication: H = H₁·H₂ has label
    E_H = E_{H_1} + E_{H_2} = ρ(F_1+F_2) + (G_1+G_2),
    so the ρ‑part is still free of y_γ.

  - Division: H = H₁/H₂ gives
    E_H = E_{H_1} - E_{H_2} = ρ(F_1-F_2) + (G_1-G_2),
    same property.

  - Exponentiation by a known scalar k: H = H₁^k has label
    E_H = k·E_{H_1} = ρ(kF_1) + kG_1,
    again no new basis symbols appear in the ρ‑part.

Thus no sequence of allowed operations can ever introduce a ρ·y_γ term if it was not present in the base operations. By the base case, such a term is never introduced in the first place, so the lemma holds for all H. ∎

#### Consequence for R^ρ and GBGM bound

Recall the PVUGC anchor
R(vk,x) := e(α₁,β₂)·e(IC(x),γ₂).
Assuming IC(x) ≠ 0, we have
E_R = a·y_β + i_x·y_γ, with i_x ≠ 0,
and therefore
R^ρ has label ρ·(a·y_β + i_x·y_γ),
whose ρ‑part contains a **nonzero** y_γ coefficient.

By the lemma, no adversarially generated G_T handle can have such a label unless the underlying independent formal symbols satisfy a nontrivial degree‑3 polynomial identity. By the standard algebraic generic bound, the probability of such a collision with at most q oracle calls is at most O(q²/r), negligible in the group order r. In particular, the presence of γ in the scalar factor (1−γ)/δ inside IC_corr only affects the scalar coefficients of F_H and G_H; it **never promotes y_γ into the ρ‑part**.

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