# PVUGC Security Analysis: Algebraic Framework & Mitigation

This document provides the algebraic generic bilinear group model (AGBGM) **security framework** for PVUGC decapsulation. It defines the attack surface, the architectural mitigations, and the formal audit required to certify security for a specific circuit.

## Executive Summary

The "Full Span" attack demonstrated that a standard Groth16 CRS provides an adversary with enough algebraic handles (Powers of Tau) to synthesize the target key without a witness. PVUGC mitigates this by restricting the algebraic structure of the system to a **single, fixed, and audited outer verifier circuit**.

**The Defense Strategy:**
1.  **Lean CRS:** We strip generic Powers of Tau and replace them with circuit-specific quotient bases, denying the adversary the "universal solvent" to forge arbitrary polynomials.
2.  **Linearity:** We ensure the Outer Circuit is linear in its public inputs, forcing the public residual $\Delta_{pub}$ to be a constant polynomial.
3.  **Baked Quotient:** We pre-compute the constant public quotient at setup time and "bake" it into the target, withholding the corresponding handles from the CRS.
4.  **Trapdoor-Aware Audit:** We formally verify that the remaining handles (witness-involved bases) are linearly independent of the target key in the trapdoor-weighted vector space.

---

## System Overview

### Architecture
PVUGC uses a **One-Sided** arming model where only the $B$-matrix (witness columns) is masked by $\rho$. The $A$-matrix is unmasked (Proving Key).

### Lean CRS Definition
The Public Parameters (PK) contain:
*   Standard Groth16 queries: $A_k, B_k, L_k$.
*   Witness-Involved Quotient Bases: $\{ H_{ij} \}$ where $i$ or $j$ is a witness index.
*   **EXCLUDED:** Powers of Tau $[\tau^k]_1$.
*   **EXCLUDED:** Purely Public Quotient Bases $\{ H_{ij} \mid i,j \le \ell \}$.

### Baked Target
The global target anchor is shifted during setup:
$$ R_{baked} = R_{orig} \cdot T_{pub}^{-1} $$
where $T_{pub}$ is the pairing of the constant public quotient with $\delta$. This allows the honest prover to skip computing the public part of the quotient (since they lack the handles), while ensuring the verification equation still holds.

---

## Security Analysis

### The Adversarial Span
The adversary aims to construct $R_{baked}^\rho$ using the available handles:
1.  **Witness Columns:** $D_j = [v_j(\tau)]_2^\rho$.
2.  **Delta Mask:** $D_\delta = [\delta]_2^\rho$.
3.  **PK Elements:** $A_k, L_k, H_{wit}$.

By pairing PK elements with ciphertext elements, the adversary generates a subspace $S_{adv}$ in $G_T$.
$$ S_{adv} = \text{Span} \{ e(A_k, D_j), e(H_{wit}, D_\delta), e(L_k, D_\delta), e(A_k, D_{pub}) \} $$

### The Trapdoor-Aware Audit
Security reduces to the claim that the target exponent $E_{target}$ lies outside $S_{adv}$ over the field of rational functions in $(\alpha, \beta, \delta, \tau)$.
*   **Polynomial Layer:** The polynomials $u, v, w$ span the relation $UV = W + Ht$.
*   **Trapdoor Layer:** The PK elements carry "poison" ($\alpha, \beta, \delta^{-1}$).
    *   $e(A, D)$ terms carry $\beta$ or $\alpha$.
    *   $e(H, D_\delta)$ terms are "clean" in polynomial structure but restricted to the Witness subspace (because $H_{pub}$ is withheld).
    *   The Target has a specific trapdoor structure ($\alpha \beta + \dots$).

The Audit verifies that no linear combination of the available (poisoned or witness-restricted) handles can sum to the specific target structure.

### Why "Full Span" Fails here
The standard Full Span attack relies on constructing the **Public Residual** $\Delta_{pub}$.
*   With **Linearity**, $\Delta_{pub}$ is constant.
*   With **Baking**, the constant target is removed (shifted to 0).
*   With **Withholding**, the handles to build the constant are gone.
*   Therefore, the attacker has nothing to build and no tools to build it.

---

## Conclusion

PVUGC decapsulation security is **Conditionally Secure**, contingent on the specific Outer Circuit passing the Trapdoor-Aware Audit. By structurally eliminating the public-side attack surface (Linearity + Baking) and hardening the witness-side surface (Lean CRS), the scheme resists algebraic attacks in the AGBGM.
