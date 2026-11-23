# Fixed-key Groth16 frontends

The [independent compact frontend](compact/README.md) compiles a fixed SP1 v6.1.0 key and public inputs to a standalone Boolean quadratic system and lifts a real proof to a packed witness. The gnark executable below provides native validation and the earlier uniform-expansion baseline.

## Offline signature release

The `praxis-capsule` CLI encrypts a fixed 64- or 65-byte payload using the published verifier rows, fresh Praxis randomness and AES-256-GCM. The arming process takes the precomputed signature as input. Each opener supplies its own packed proof witness, the public artifacts and the arming receipt. The fixture uses the SP1 clock program and two Groth16 proofs for the same statement. The second proof is obtained by rescaling A and B in the first. Both independently pass native verification. The [three-signer adaptor experiment](../README.md) produces the fixture signature under a separate reduced policy. A setup party that obtains the completed signature in this single-capsule experiment can already spend the fixture output. Integrating the full verifier into each signer's share encryption is required to carry the one-honest-party design through to this path.

Use the [end-to-end runner](../README.md#run-the-sp1-experiment) for a fresh fixture, both proof lifts and Bitcoin signature verification. For an existing experiment, build the CLI from this directory and supply the files and independently pinned receipt directly.

```sh
go build -mod=readonly -o "$out/capsule-cli" ./cmd/praxis-capsule
receipt=$("$out/capsule-cli" arm "$manifest" "$rows" "$signature_file" "$new_capsule")
"$out/capsule-cli" open "$manifest" "$rows" "$new_capsule" "$receipt" "$packed_witness" "$new_output"
```

The sender must authenticate the verifier key, public inputs and compilation used for arming. The opener must obtain the intended receipt through an authenticated channel. Each capsule header binds the exact manifest, whose digest of the uncompressed row stream is checked on load. Output paths must be fresh.

The development profile uses BN254, six tied copies, extension degree 4, `K1=1`, `K2=2`, `g=8` and `J=J'=1`. Its key-encapsulation backend uses a 100-bit random seed. The experiment measures honest recovery and invalid-input handling. The unqualified profile supplies no security-bit or PoW estimate. The pairing-based construction is classical.

### Measured CPU run

On 2026-11-23, implementation commit `463ce76546a7a811b4225a4a05497ec475bcd9f6` processed 588,373 Boolean variables and 3,305 rows. At 255 products per row the exact QAP has 1,434,455 evaluation points. The Linux host had 16 CPUs, with Go limited to 12 workers. Each stage ran in a separate process.

| Stage | Elapsed | Peak RSS |
| --- | ---: | ---: |
| Arm one 1,051,934,251-byte capsule | 43.63 s | 358.1 MiB |
| Open with the original SP1 proof | 95.69 s | 820.6 MiB |
| Open with the rescaled SP1 proof | 95.72 s | 821.9 MiB |

Public compilation took 4.23 s. Witness lifting took 4.26 s and 4.30 s respectively, measured separately from opening. Both outputs matched the input signature byte-for-byte. A standalone BIP340 check reconstructed the synthetic transaction's BIP341 sighash from the separately pinned Bitcoin receipt and verified both outputs. Changing one witness bit or one nibble of the capsule receipt rejected the opening and left the output path empty.

| Recorded value | SHA-256 |
| --- | --- |
| Public manifest | `7bd9b3f83d9f6537dc1f17f0946337611b66a9e9b1fe0559b63d66aeae9b4b90` |
| Randomized capsule | `18ddc1a9515896c2485f6f8714dc10ec40179796728df3b09f72c652029b4c0e` |
| Input and both recovered signatures | `ee2bc3e5859001b6b719f48133ca0d312a0ac49fc56042fbfcf5a58822b607c4` |

### Size at the paper's parameters

The 1,051,934,251-byte measurement covers one full-width capsule at the six-copy development parameters. Praxis reports **7.88 GiB** compressed for its own 391,693-variable encoder and its 100-bit target. Applying Proposition 5.7 to our 588,373-variable layout with the paper's grid predicts **11.83 GiB** for the group-element arrays with standard compressed points. For this estimate the 3,305 rows are padded to 3,311 to divide evenly across 11 chunks. There are 226,731,290 G1 points at 32 bytes and 85,149,848 G2 points at 64 bytes. This is a storage estimate for a larger backend. Its runtime and security on this verifier shape require separate evaluation. [Praxis, Proposition 5.7 and Table 4](https://eprint.iacr.org/2026/2971.pdf)

## Uniform wire expansion

Run `GOMAXPROCS=2 GOMEMLIMIT=4GiB go run -mod=readonly .` from this directory with Go 1.26.8 or newer. The executable compiles gnark's BN254 Groth16 proof verifier over BN254's scalar field with subgroup checks enabled. It specializes the verification key and all five SP1 public inputs as constants. It generates no outer Groth16 setup.

The tests use Succinct's v6.0.0 Fibonacci proof and Arcora's v6.1.0 clock proof. Each test derives a second proof by replacing `(A, B)` with `(2A, B/2)`, which preserves the pairing. Both pass the native verifier and the circuit solver. The program encodes every solved field wire as 254 Boolean digits, recombines those digits in the scalar field, and checks every constraint row. Changing the expected public-values hash rejects the original proof in both verifiers. Each proof is decoded under the key matching its version selector.

| Measured quantity | v6.0.0 and v6.1.0 |
| --- | ---: |
| R1CS rows | 1,264,008 |
| Internal field wires | 2,019,937 |
| Private proof input wires | 40 |
| Public field wires, including constant one | 1 |
| Outer Groth16 commitment slots | 1 |
| Boolean variables with uniform 254-bit expansion | 513,074,158 |

For each nonconstant scalar-field wire `v`, the baseline substitutes `v = Σ 2^j b_j mod Fr` with 254 Boolean digits. Every field element has a canonical encoding of that width. Each R1CS row remains one product of substituted linear forms equated to a linear form. The 513,074,158-variable result is exact for this expansion. The check retains the linear forms in factored form. At the paper's `K1=192`, two 32-byte compressed G1 left-factor arrays per lane alone account for 6,304,655,265,792 bytes (5.73 TiB). This excludes all other factors, powers, tags, and ceremony replication. It is a size estimate for this particular substitution and group encoding. More efficient verifier encodings can use fewer variables.

The diagnostic solver supplies a transcript-derived challenge for gnark's outer commitment hint. The rows by themselves do not enforce that challenge. The ordinary gnark proving protocol binds that commitment during proving and verification. Exporting these raw rows directly into a stand-alone Praxis Boolean system would require an equivalent binding or deterministic replacement for the dependent gadgets. This executable verifies the native proof, checks concrete traces and measures the direct frontend. It supplies no full-profile Praxis capsule and establishes no extractability theorem for the substituted rows. [gnark commitment interface](https://github.com/Consensys/gnark/blob/v0.16.5/std/multicommit/nativecommit.go) · [Praxis parameters](https://eprint.iacr.asia/2026/2971.pdf#page=36)

## Specialize a trusted public statement and verify decoded coordinates

Supply a gnark BN254 verifying key with six IC points and no commitment sections, plus exactly five canonical decimal strings in the BN254 scalar field. The key may use gnark's compressed or uncompressed binary point encoding. Each point is checked for curve and subgroup membership. Start from the recipient's authenticated key bytes and the intended public inputs.

```sh
go run -mod=readonly . -statement testdata/sp1-v6.1.0.vk testdata/sp1-v6.1.0-inputs.json
go run -mod=readonly . -verify-decoded testdata/sp1-v6.1.0.vk testdata/sp1-v6.1.0-inputs.json < decoded-proof.json
```

The first command needs no proof. It derives the fixed key points, the public-input combination and the SHA-256 digest of the key directly from these files. The v6.1.0 expected output is `testdata/sp1-v6.1.0-statement.json`. The second command accepts exactly `a`, `b`, and `c` proof points on stdin in the coordinate format described below and runs the native verifier. It accepts the all-zero affine encoding for a neutral point according to gnark's convention. The pairing check still applies to the complete proof.

## Pairing witness for the compact frontend

Run `go run -mod=readonly . -export-v6.1` to emit the JSON in `testdata/sp1-v6.1.0-pairing.json`. The `statement` object contains the pinned key digest, five public inputs and fixed group constants. It includes the point `L = IC[0] + Σ xᵢ IC[i+1]`. Each entry of `witnesses` holds a proof's variable points `a,b,c`. Base-field coordinates are decimal integers. The twist coordinates use arrays in the order `[A0,A1]` for `A0 + A1·i`, with `i² = −1`.

Before emitting the JSON, the exporter checks native Groth16 verification and the four-pair equation `e(A,B) e(−C,δ) e(−L,γ) e(−α,β) = 1` on both proofs. It recomputes `L` under a changed public input and checks rejection. The compact frontend must independently constrain the variable proof points and the pairing relation under the fixed constants.

## Public fixtures

| File | SHA-256 | Upstream source |
| --- | --- | --- |
| `testdata/sp1-v6.0.0.json` | `ee35af16543ee044e6a9600251cc0767ebc268d2bd7530b82fbdb2dbca4de799` | [SP1 project template d1b0924](https://github.com/succinctlabs/sp1-project-template/blob/d1b0924587efd7f4b6c2797d6fdd8282da71d088/contracts/src/fixtures/groth16-fixture.json) |
| `testdata/sp1-v6.0.0.vk` | `0e78f4db7a6771a3a6a7d9c3b0de6fe73d58781368967a7fe84d87aefffec896` | [SP1 v6.0.0 f87f8d6](https://github.com/succinctlabs/sp1/blob/f87f8d6ff005d542db22e241928319f5e96a4609/crates/verifier/vk-artifacts/groth16_vk.bin) |
| `testdata/sp1-v6.1.0.json` | `d9920e2875863a23893f1ea2e232ee697305c3b6fafdfd34e6def68a352cd71a` | [Garaga proof fixture 86b6025](https://github.com/keep-starknet-strange/garaga/blob/86b6025567c5e2395947f9c6d40262c9ead2a54c/hydra/garaga/starknet/groth16_contract_generator/examples/proof_sp1.json) · [Original Arcora fixture bb16693](https://github.com/Arcora-labs/arcora-perp/tree/bb166930ac88f65537adc48bee4ffaf09d629d62/contracts/integration/fixtures/clock-pkg3-verified) |
| `testdata/sp1-v6.1.0.vk` | `4388a21c687fdd5f218d7e3d13190cac4c5355818d3605fd5fb811df468ee696` | [SP1 v6.1.0 d454975](https://github.com/succinctlabs/sp1/blob/d454975ac7c1126097e36eceda9bce2cb9899da4/crates/verifier/vk-artifacts/groth16_vk.bin) |

Succinct Labs supplies the proof fixture and verification keys under the included MIT license notices in `testdata/LICENSE-TEMPLATE-MIT` and `testdata/LICENSE-SP1-MIT`. The v6.1.0 clock proof is distributed with Arcora Labs' MIT notice in `testdata/LICENSE-ARCORA-MIT`. Go modules and checksums are pinned in `go.mod` and `go.sum`.
