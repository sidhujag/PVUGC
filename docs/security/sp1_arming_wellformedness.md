# SP1 Arming Well-Formedness Proof (No-Bricking)

This document specifies an SP1 (zkVM) proof that an arming package is **well-formed** and therefore **cannot brick** a PVUGC deposit by encrypting under a key inconsistent with the published arms.

The proof is intended to run inside SP1 as a Rust guest program and produce an SP1 proof whose *committed public values* bind it to the exact published arming package.

## Goal

Given a statement `(vk, x)` and a PVUGC arming package containing:

- statement-only G2 base `delta`
- its ρ-armed version `D_delta = delta^ρ`
- the baked target `R_baked(vk, x)` in `G_T` (outer pairing target group)
- a DEM ciphertext `ct` and key-commitment tag `tau`
- an AD binding digest `ad_digest = SHA256("PVUGC/AD_CORE" || len(ad_core) || ad_core)`

prove in ZK that:

1. `D_delta` is consistent with a *single* scalar `ρ ≠ 0`, and
2. the ciphertext/tag are consistent with the **same** derived key:

`K = R_baked(vk, x)^ρ`,

so that a decapper using the arms cannot get stuck on a mismatched DEM key.

also prove the ciphertext decrypts to the **intended adaptor share**
by checking the decrypted 32-byte scalar corresponds to the public adaptor commitment `T_i`.

## Curves / Fields

- Outer pairing curve: **BW6-761** (for the production recursion cycle BLS12-377/BW6-761).
- DEM hash: **SHA-256**, matching `PVUGC/src/ct.rs`.

This well-formedness proof does **not** need to know anything about the *inner* SP1 proof system; it only needs the published PVUGC arming objects and the baked target `R_baked`.

## Publicly Bound Data (Committed by SP1)

The SP1 guest commits a single 32-byte digest:

`pkg_digest = SHA256( encode(pkg_public) )`

where `pkg_public` includes at minimum:

- `curve_id` (domain separation / versioning)
- `delta` bytes (BW6-761 G2 affine coords: `x_le_96 || y_le_96`)
- `D_delta` bytes (BW6-761 G2 affine coords: `x_le_96 || y_le_96`)
- `R_baked` bytes (BW6-761 GT as Fq6 tower limbs: `(c0.c0,c0.c1,c0.c2,c1.c0,c1.c1,c1.c2)` each `Fq` as 96 bytes LE)
- `ad_digest` (32 bytes)
- `ct` bytes
- `tau` (32 bytes)
- `T_i` (compressed secp256k1 point bytes, as included in AD_core)

The verifier recomputes `pkg_digest` from the published package and checks it equals the committed value from the SP1 proof.

## Verifier Requirements (Outside SP1)

The guest program is optimized and intentionally does **not** do full group hygiene (canonical parsing, on-curve checks, subgroup checks, GT r-torsion checks). Every verifier must therefore do an **outside-SP1 audit** on the exact byte-level package, and must bind those bytes to the SP1 proof via `pkg_digest`.

Minimum requirements before accepting/signing an arming package:

- **Byte-level binding:** recompute `pkg_digest = SHA256(encode(pkg_public_bytes))` and ensure it equals the digest committed by the SP1 proof.
- **BW6-761 G2 hygiene:** canonical parse + on-curve + correct-subgroup checks for `delta_base` and `delta_arm`, and reject identity points.
- **BW6-761 GT hygiene:** reject degenerate `R_baked` and enforce membership in the correct r-torsion / cyclotomic subgroup (host-side check).
- **Format/length checks:** `ct.len() == 32`, `t_i_bytes.len() == 33` with SEC1 compressed prefix `0x02/0x03`, and all BW6 encodings have the expected fixed lengths.

Semantic policy checks (must be enforced by the verifier, not just “hashed into pkg_digest”):

- **`profile` policy:** `profile` must equal the expected protocol/version identifier for PVUGC arming-wf (prevents cross-context replay across versions/semantics).
- **`ad_digest` policy:** `ad_digest` must equal `SHA256("PVUGC/AD_CORE" || len(ad_core) || ad_core)` for the statement’s actual `AD_core`.

## Witness (Private Inputs)

- `rho` (scalar field element for BW6-761), provided as canonical bytes and deserialized in-guest.

## In-Guest Checks

Let `E = BW6_761` (arkworks pairing type).

1) **Parse / validate inputs**

- Parse `delta`, `D_delta` from raw affine coordinate encodings (`x_le_96 || y_le_96`).
- Parse `R_baked` from raw Fq6 limb encoding (same layout as the guest uses for `k_bytes`).
- Deserialize `rho` as `E::ScalarField` (canonical bytes).

2) **Arming correctness**

- Check `D_delta == (delta * rho)` in `G2`.

Note: full arming correctness for all published `Y_j, D_j` must be enforced outside SP1 using
`PoCE` (same-exponent proof). This is the compression step that avoids looping over ~33k columns
in the zkVM.

3) **Key derivation consistency**

Compute:

- `K = R_baked.pow(rho)` in `G_T`.
- `k_bytes = CanonicalSerializeCompressed(K)`

4) **DEM tag check**

Recompute per `PVUGC/src/ct.rs`:

- `tau' = SHA256("PVUGC/DEM/tag" || k_bytes || ad_digest || ct)`

and assert `tau' == tau`.

5) **Plaintext / adaptor-share check**

Derive the DEM keystream per `PVUGC/src/ct.rs`:

`KS_i = SHA256("PVUGC/DEM/keystream" || k_bytes || ad_digest || counter_le)`

Decrypt:

`pt = ct XOR keystream`

Interpret `pt` as a 32-byte secp256k1 scalar (big-endian, reduced mod curve order), compute:

`T_i' = pt · G`

and assert `T_i' == T_i` where `T_i` is the compressed secp256k1 point committed in AD_core.

## Notes on “Optimal Strategy”

Expensive checks that can be done outside SP1 should be done outside, but **must be bound** to the proof via `pkg_digest`.

Recommended outside checks (non-ZK):

- Subgroup checks for all `G2` points (cheap outside, expensive inside)
- Duplicate/negated-duplicate checks for `Y_j` and the “no ±gamma2” exclusion
- Sanity constraints like `rho != 0` (still checked inside; cheap)
- Check `R_baked` matches `(vk, x)` and the baked quotient basis
- Verify `PoCE` for the armer’s full column set (`Y_j, D_j`) to ensure all arms share the same `rho`

The ZK proof is then focused on the **only non-public linkage**: `rho` consistently ties (arms) ↔ (R_baked^rho) ↔ (DEM tag).

