# SNARK-over-STARK Verifier Architecture (Winterfell-compatible)

## Overview

We implement a full, in-circuit verifier for Winterfell-style STARK proofs and wrap it with a Groth16 proof (SNARK-over-STARK). PVUGC then operates on the outer Groth16 proof to enable statement-dependent, proof-agnostic key extraction.

## Architecture

```
Layer 1: Inner Circuit (BLS12-377 Groth16, in-circuit STARK verifier)
├─ Verifies: Winterfell STARK proof (RPO-256 Merkle, DEEP, FRI)
├─ Public inputs: commitments (trace, comp, FRI roots) and AIR parameters
└─ Witness: batch Merkle nodes, query values, OOD frames, FRI layer data

Layer 2: Outer Circuit (BW6-761 Groth16)
├─ Verifies: inner Groth16 proof
├─ Public inputs: compressed via BooleanInputVar
└─ Witness: inner proof (A, B, C)

Layer 3: PVUGC (Groth–Sahai on BW6-761)
├─ Extracts: K = R(vk, x)^ρ (statement-dependent, proof-agnostic)
└─ Input: outer Groth16 proof and statement
```

## In-Circuit STARK Verification (Summary)

- Batch Merkle multiproof (RPO-256): mirrors Winterfell `BatchMerkleProof::get_root` across trace, composition, and each FRI layer.
- Fiat–Shamir transcript (RPO-256): derives coefficients, per-layer β, and query positions exactly as Winterfell.
- DEEP composition (linear batching): per-query shared denominators (x−z), (x−z·g) with a single batched inverse.
- Binary FRI folding: next evaluation via line-through ±xe with parameter β; consistency enforced against current layer values.
- Goldilocks ↔ bytes bridging: binds GL values to commitment bytes.

Compatibility: parsing, ordering, and pointer arithmetic match Winterfell; adversarial tests tampering with nodes, positions, OOD, or FRI data are rejected.

### Witness Linking Guarantees

- **Single allocation for OOD traces** – the circuit allocates Out-Of-Domain (OOD) trace and composition evaluations once and
  reuses the same `GlVar` handles when hashing the proof commitments and when constructing the DEEP composition. Any attempt to
  alter the values between these phases would break constraint satisfaction.
- **Shared query witnesses** – Merkle verification gadgets now pass the committed row values by reference into the DEEP
  evaluation gadgets. This guarantees that each queried row that passes the Merkle check is the same row whose numerators and
  denominators enter the DEEP combination.
- **Shape enforcement** – explicit checks ensure the prover supplies the expected number of trace columns, composition
  columns, and OOD elements before challenge derivation. Mismatched widths or missing values are caught deterministically by
  the circuit.

## Constraint Growth (empirical)

With batch verification:
- 1 FRI layer (steps=64): ~4M constraints
- 2 FRI layers (steps=128): ~5.5M constraints
- 3 FRI layers (steps=256): ~7.2M constraints

Growth is near-logarithmic in domain size for fixed query counts (batch Merkle/FRI). The outer Groth16 remains constant-size; PVUGC cost is constant (dozens of columns).

## PVUGC Integration

PVUGC operates on the outer Groth16 proof:
- Proof-agnostic extraction: different inner proofs of the same statement yield the same K.
- Statement binding: different statements yield different K with overwhelming probability.

See `specs/PVUGC.md` for the algebraic details and `DESIGN.md` for one-sided GS rationale.

## Security Notes

- Collision resistance of RPO-256 and transcript binding ensure any tampering in commitments or metadata changes challenges.
- DEEP/FRI soundness follow standard Winterfell analyses; division is enforced multiplicatively.
- Outer Groth16 provides knowledge soundness; PVUGC relies on standard pairing assumptions.


