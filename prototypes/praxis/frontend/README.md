# Fixed-key Groth16 frontend baseline

Run `GOMAXPROCS=2 GOMEMLIMIT=4GiB go run -mod=readonly .` from this directory with Go 1.26.8 or newer. The executable compiles gnark's BN254 Groth16 proof verifier over BN254's scalar field with subgroup checks enabled. It specializes the verification key and all five SP1 public inputs as constants. It generates no outer Groth16 setup.

The v6.0.0 test uses Succinct's public Fibonacci proof and a second proof formed by replacing `(A, B)` with `(2A, B/2)`, which preserves the pairing. Both pass the native verifier and the circuit solver. The program encodes every solved field wire as 254 Boolean digits, recombines those digits in the scalar field, and checks every constraint row. Changing the expected public-values hash rejects the original proof in both verifiers. The second compilation measures the v6.1.0 key on the v6.0.0 fixture's public-input constants. The program checks the version selector and does not present the v6.0.0 proof to the v6.1.0 key as a valid witness.

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

## Public fixtures

| File | SHA-256 | Upstream source |
| --- | --- | --- |
| `testdata/sp1-v6.0.0.json` | `ee35af16543ee044e6a9600251cc0767ebc268d2bd7530b82fbdb2dbca4de799` | [SP1 project template d1b0924](https://github.com/succinctlabs/sp1-project-template/blob/d1b0924587efd7f4b6c2797d6fdd8282da71d088/contracts/src/fixtures/groth16-fixture.json) |
| `testdata/sp1-v6.0.0.vk` | `0e78f4db7a6771a3a6a7d9c3b0de6fe73d58781368967a7fe84d87aefffec896` | [SP1 v6.0.0 f87f8d6](https://github.com/succinctlabs/sp1/blob/f87f8d6ff005d542db22e241928319f5e96a4609/crates/verifier/vk-artifacts/groth16_vk.bin) |
| `testdata/sp1-v6.1.0.vk` | `4388a21c687fdd5f218d7e3d13190cac4c5355818d3605fd5fb811df468ee696` | [SP1 v6.1.0 d454975](https://github.com/succinctlabs/sp1/blob/d454975ac7c1126097e36eceda9bce2cb9899da4/crates/verifier/vk-artifacts/groth16_vk.bin) |

Succinct Labs supplies the proof fixture and verification keys under the included MIT license notices in `testdata/LICENSE-TEMPLATE-MIT` and `testdata/LICENSE-SP1-MIT`. Go modules and checksums are pinned in `go.mod` and `go.sum`.
