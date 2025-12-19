# SP1 → Groth16 Wrapper → Outer Groth16 → PVUGC Architecture

## Overview

PVUGC is used as a **KEM/decapsulation layer** on top of an outer Groth16 proof. The outer proof verifies an SP1-generated Groth16 proof that wraps SP1’s STARK-based zkVM proof system. The key design goal is:

- **statement-dependent**: different SP1 statements extract different keys
- **proof-agnostic**: different outer proofs for the *same* statement extract the same key

In this repo, “the statement” that PVUGC binds to is exactly SP1’s **two public inputs**:

- `vkey_hash`: identifies the SP1 program/verifier key
- `committed_values_digest`: commits to the program’s public values (outputs)

## High-level architecture

```
Layer 0: SP1 zkVM (STARK-based)
├─ Input: (ELF program, stdin)
├─ Output: SP1 core proof + SP1 public values bytes
└─ Security: zkVM/STARK soundness

Layer 1: SP1 recursion + wrap
├─ Reduces: many STARK shard proofs → single reduced proof
├─ Wraps: reduced proof into a SNARK-friendly statement
└─ Produces: (vkey_hash, committed_values_digest) as the public statement

Layer 2: SP1 Groth16 wrapper proof (BLS12-377)
├─ Verifies: the wrapped SP1 recursion proof inside a Groth16 circuit
├─ Public inputs (Fr377):
│   - vkey_hash (field element)
│   - committed_values_digest (field element)
└─ Output: gnark Groth16 proof bytes + the 2 public inputs

Layer 3: Outer Groth16 circuit (BW6-761)
├─ Verifies: the Layer-2 (BLS12-377) Groth16 proof
├─ Public inputs: same statement (vkey_hash, committed_values_digest) mapped into outer field
└─ Output: outer Groth16 proof + witness/assignment (for PVUGC commitments)

Layer 4: PVUGC (pairing-based, on BW6-761)
├─ Input:
│   - outer Groth16 proof (A,B,C) and commitment/witness columns
│   - statement (vkey_hash, committed_values_digest)
├─ Extracts/decaps: K = R(vk_outer, statement)^ρ
└─ Property: proof-agnostic extraction for fixed statement
```

## “Statement” and why it’s enough

SP1’s wrapper statement is intentionally small:

- `vkey_hash` binds the proof to a *specific* SP1 program (i.e., program VK)
- `committed_values_digest` binds the proof to the *program’s public values* (what the program outputs / commits)

PVUGC never needs the inner STARK transcript directly; it only needs the statement that the outer circuit verifies.

## Example: proving an SP1 program end-to-end

Take an SP1 program like `TENDERMINT_ELF` (or `FIBONACCI_ELF` for a toy example).

1. **Execute** the program to get public values bytes:
   - SP1 returns `public_values` as raw bytes.
2. **Derive the statement**:
   - `vkey_hash = program_vk.hash_bn254()` (SP1 SDK naming; yields a field element-compatible integer)
   - `committed_values_digest = public_values.hash_bn254()` (hash of the public values bytes, masked per SP1 convention)
3. **Prove (Groth16)**:
   - SP1 produces a gnark Groth16 proof on **BLS12-377** whose public inputs are exactly:
     - `vkey_hash`, `committed_values_digest`
4. **Bridge + outer proof**:
   - Parse gnark proof/VK bytes into arkworks types.
   - Produce an **outer BW6-761 Groth16 proof** that verifies the inner Groth16 proof for that statement.
5. **PVUGC decapsulation**:
   - Arm the statement once (deposit-side).
   - For any number of fresh outer proofs of the same statement, PVUGC decaps the same key.

See `PVUGC/tests/test_sp1_e2e.rs` (`test_sp1_to_pvugc_real`) for the concrete flow.

## PVUGC integration notes (what must remain consistent)

- **Statement canonicalization**: the statement must be derived deterministically from non-proof data (program VK + public values).
- **Proof-agnostic extraction**: outer-proof randomness (Groth16 randomizers) must cancel in the PVUGC decap formula; only the statement survives.
- **Field-mapping consistency**: the same logical statement must be interpreted consistently across:
  - SP1’s inner wrapper field (Fr377),
  - the outer circuit field (BW6-761 scalar),
  - PVUGC’s statement encoding.

## Security notes (high level)

- SP1 soundness ensures the statement is only satisfiable for valid program executions.
- Outer Groth16 provides knowledge soundness on the wrapped statement.
- PVUGC security relies on standard pairing assumptions and the fact that the statement encoding is binding and proof randomness cancels.
