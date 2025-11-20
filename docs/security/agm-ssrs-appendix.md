# Appendix: AGM-SSRS Span-Separation Lemma and Selective-Programming Reduction

This appendix analyzes the PVUGC-specific Groth16 variant (no 1/γ scaling inside IC(x)). These tweaks are opt-in and only exercised by the PVUGC outer prover; the rest of the Groth16 codebase continues to run in the traditional mode.

**PVUGC-only CRS adjustments**
- The verifier key exposes both the classic `IC` (scaled by 1/γ) and an unscaled `IC_raw`; PVUGC only references `IC_raw` when forming the anchor.
- The proving key ships the `[(1-γ)/δ · f_i(τ)]₁` correction query so that the PVUGC prover can add the public-input linear combo to `C` and satisfy `e(A,B)=e(α₁,β₂)·e(IC_raw(x),γ₂)·e(C,δ₂)`.
- All right-leg masks are aggregated: the β/public column is armed only as `B_pub^ρ`, witness columns remain separate, and γ₂ is never armed.

## 1. The AGM-SSRS Model

### Definition (Algebraic Group Model with Structured SRS)

We work in an algebraic model where:

1. **Monomial Basis**: The G₂ elements are expressed over the basis {[τ⁰]₂, [τ¹]₂, ..., [τⁿ]₂}

2. **Explicit Structure**: Each CRS element has known polynomial representation:
   - Qⱼ = [vⱼ(τ)]₂ = Σₖ vⱼ,ₖ[τᵏ]₂
   - β₂ = [β]₂ = Σₖ βₖ[τᵏ]₂  
   - δ₂ = [δ]₂ = Σₖ δₖ[τᵏ]₂
   - γ₂ = [γ]₂ = Σₖ γₖ[τᵏ]₂

3. **Independence Hygiene**: γ₂ ∉ span{β₂, Qⱼ, δ₂} over the monomial basis

4. **Algebraic Operations**: Adversary can only perform group operations and must provide algebraic representations

## 2. Span-Separation Lemma

### Lemma (Monomial-Lift Span-Separation)

In AGM-SSRS, let the armed transcript be:
- D_pub = B_pub^ρ where B_pub = β₂ + Σᵢ≤ℓ xᵢQᵢ
- Dⱼ = Qⱼ^ρ for j > ℓ
- D_δ = δ₂^ρ

Then every GT element H that the adversary can compute satisfies:

```
log(H) = ρ·F(coeffs of B_pub, {vⱼ}_{j>ℓ}, δ) + G(unmasked) + c·r*
```

where crucially, the coefficient of ρ·γ in log(H) is always 0.

### Proof

**By induction on adversary operations:**

1. **Base case**: Initial GT elements from pairings
   - e(U, D) for armed D contributes ρ·(U's coeffs)·(D's monomial coeffs)
   - Since D ∈ {B_pub^ρ, Qⱼ^ρ, δ₂^ρ}, and none contain γ by hygiene
   - No ρ·γ term appears

2. **Inductive step**: GT operations
   - Multiplication: (ρ·F₁ + G₁) + (ρ·F₂ + G₂) preserves no-ρ·γ property
   - Division: Similar
   - Known powers: ρ·γ coefficient scales but remains 0

3. **Polynomial identities don't help**:
   - Suppose Σ cⱼvⱼ(X) ≡ aγ + bβ + ... mod t(X)
   - This would mean Σ cⱼQⱼ = a·γ₂ + b·β₂ + ... in G₂
   - Contradicts independence hygiene γ₂ ∉ span{β₂, Qⱼ, δ₂}

**Conclusion**: The ρ·γ monomial never appears, while R^ρ = e(α₁,β₂)^ρ · e(IC(x),γ₂)^ρ (with IC(x) unscaled) requires it with coefficient i_x ≠ 0. □

## 3. Selective-Programming Reduction to XPDH

### Theorem (Reduction to GT-XPDH)

If adversary A breaks PVUGC decapsulation with advantage ε, then we construct B that breaks GT-XPDH with advantage ε.

### Construction

**GT-XPDH Challenge**: Given {(Yᵢ, Yᵢ^ρ)}ᵢ and independent R ∈ GT, compute R^ρ

**Reduction B**:

1. **Setup Phase**:
   - Receive GT-XPDH challenge with Y₀ = β₂, {Yⱼ = Qⱼ}_{j>ℓ}, Y_δ = δ₂
   - Choose public inputs x* such that B_pub = β₂ (possible by setting all xᵢ = 0)
   - Set R = e(α₁,β₂) · e(IC(x*),γ₂) as the KEM anchor (the target without 1/γ)

2. **Arming Simulation**:
   - Publish D_pub = Y₀^ρ = β₂^ρ (since B_pub = β₂)
   - Publish Dⱼ = Yⱼ^ρ for j > ℓ
   - Publish D_δ = Y_δ^ρ

3. **Extraction**:
   - When A outputs M claiming M = R^ρ
   - Compute: M' = M / e(α₁,β₂^ρ)
   - Since M = e(α₁,β₂)^ρ · e(IC(x*),γ₂)^ρ
   - We get M' = e(IC(x*),γ₂)^ρ

4. **XPDH Solution**:
   - We've computed e(IC(x*),γ₂)^ρ without access to γ₂^ρ
   - This breaks XPDH for the element IC(x*) and base γ₂

### Analysis

- **Perfect simulation**: The armed transcript is distributed identically
- **Success probability**: If A succeeds with prob ε, so does B
- **Efficiency**: B runs in time comparable to A

**Conclusion**: PVUGC decapsulation reduces tightly to GT-XPDH, which is implied by SXDH. □

## Conclusion

The security of PVUGC rests on:
1. **Span-separation** that holds even with polynomial structure (AGM-SSRS)
2. **Clean reduction** to GT-XPDH under SXDH (selective programming)
3. **Simple guardrails** that are mechanically verifiable

The construction is cryptographically sound within these models, with fragility being operational (maintaining guardrails) rather than cryptanalytic.
