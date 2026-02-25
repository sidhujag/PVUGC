# SP1 Arming Well-Formedness (PVUGC)

This folder contains an SP1 (zkVM) guest program that proves an arming package is **non-bricking**:

- the published `delta_arm` binds a single secret `rho`, and
- the published `(ct, tau)` are consistent with `K = R_baked^rho`.
- the ciphertext decrypts to the intended adaptor share (by checking `T_i = pt·G` on secp256k1).

This is intended to be verified offline using SP1's native STARK proof modes (`core` or
`compressed`). No Groth16/Plonk SNARK wrapping is required unless you want on-chain verification.

## Files

- `program/`: SP1 guest (ELF) that checks arming, DEM tag, and plaintext/share consistency (`t_i_bytes`)
- `elf/`: production-distributed guest ELF location (see `elf/README.md`)
- `script/`: minimal SP1 SDK runner for local proof generation
- Spec: `../docs/security/sp1_arming_wellformedness.md`

## Build (guest)

From the program directory:

```bash
cd PVUGC/sp1-arming-wf/program
cargo build --release
```

## Run (host script)

The script expects a bincode file containing `ArmingWfInput` (same struct as in the guest).

```bash
cd PVUGC/sp1-arming-wf/script
cargo run --release -- \
  --elf ../program/target/release/pvugc-sp1-arming-wf-program \
  --input ./input.bin
```

## Required outside checks

The SP1 proof *binds to* `R_baked` (it is part of the committed package digest), but it does not
recompute `R_baked(vk,x)` from a Groth16 verifying key inside the zkVM.

For a complete arming-time validation pipeline, the verifier MUST additionally check outside SP1:

- `R_baked` matches `(vk, x)` and the published baked quotient basis (if used).
- Curve/subgroup validity for all published points (bases and arms).
- `PoCE` is valid for this armer’s full column set (compresses the ~33k per-column arm checks).

