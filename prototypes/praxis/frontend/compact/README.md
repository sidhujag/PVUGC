# Fixed-statement compact BN254 encoder

This program derives Boolean quadratic constraints over the BN254 scalar field for the commitment-free, five-public-input SP1 Groth16 verifier. Its public constants come from a validated Groth16 key and five canonical scalar-field inputs. A prover supplies the eight base-field coordinates of A, B and C. The lifter produces the intermediate bits needed to satisfy the public constraints. Generating the constraints requires only the public statement.

The default uses optimal Ate on BN254. A separate reduced Tate implementation serves as a reference. This is an independently derived encoder. Section 6.1 of the Praxis paper gives different dimensions for the authors’ internal SP1 v6.1.0 encoder and does not specify its gates. The researchers explicitly scope that encoder outside their public Lean formalization. [Praxis paper](https://eprint.iacr.asia/2026/2971.pdf#page=35) · [Authors’ implementation boundary](https://github.com/psivesely/praxis-lean/blob/60d3defeebd77caa0e57babe97991e672b948bb6/README.md)

## Measured v6.1.0 statement

| Encoder | Boolean unknowns | Constraint rows |
| --- | ---: | ---: |
| Previous uniform gnark wire expansion | 513,074,158 | 1,264,008 plus a commitment to enforce |
| Independent fused optimal Ate | 3,501,401 | 17,687 |
| Authors’ reported encoder | 391,693 | 1,692 |

For this SP1 statement, the independent backend uses at most 76 products per row and the largest certified integer-limb residual bound is 209 bits. Its packed witness takes 437,676 bytes. The canonical row stream is 10,423,402 bytes, with manifest row digest `ad33ce60212f7d08770d4c13f685405a71211ef1055ceede2ec9d529f9bbc8bf`. Both committed fixture proofs lift to this same public layout. The earlier and new frontend counts represent the same fixed-key verifier using different constraint compilations. No full Praxis ciphertext was generated. At the illustrative old width `K1=192`, two unbatched G1 left-factor arrays with 32-byte elements would alone take approximately 40.1 GiB for this shape. Using the larger shape requires its own parameter analysis. Witness length is distinct from ciphertext size.

## Reproduce from the frontend directory

Python 3.10+ runs the encoder with the standard library. The independent native check uses the pinned Go module and real v6.1.0 fixture documented in [the frontend README](../README.md). These commands use a new working directory for generated outputs.

```sh
out=$(mktemp -d)
go build -mod=readonly -o "$out/native" .
"$out/native" -statement testdata/sp1-v6.1.0.vk testdata/sp1-v6.1.0-inputs.json > "$out/statement.json"
python3 -m compact compile "$out/statement.json" --manifest "$out/manifest.json" --rows "$out/rows.jsonl"
python3 -m compact lift "$out/statement.json" "$out/manifest.json" testdata/sp1-v6.1.0-pairing.json "$out/witness.bin" --index 0
python3 -m compact check "$out/manifest.json" "$out/rows.jsonl" "$out/witness.bin" > "$out/proof.json"
"$out/native" -verify-decoded testdata/sp1-v6.1.0.vk testdata/sp1-v6.1.0-inputs.json < "$out/proof.json"
```

The fixture includes a second valid proof at index 1. Use a fresh witness filename when lifting it. A standalone proof JSON uses the same `a`, `b`, `c` coordinate representation. The raw verifying key and the five public inputs must be authenticated by the caller. The bridge must derive those inputs from its chosen program and withdrawal. The encoder proves only the fixed verifier relation.

## Exact base-field arithmetic in scalar-field rows

Write `p` for the BN254 base-field prime and `r` for its scalar-field prime. Every private field value is represented by a little-endian linear form in 254 Boolean unknowns. A generated solution can use a noncanonical representative of the same residue. The decoder reduces proof coordinates modulo `p` before producing a canonical native point.

For a signed sum of products `S` and its output residue `z`, the lifter supplies an integer quotient `h`. The public compiler derives lower and upper bounds on `h` from the widths of the Boolean operands, represents it with an offset and a bounded binary magnitude, and forms `E = S − z − ph`. The possible values of every bit pattern, including unused slack above the nominal upper bound, are included in the residual bound `B ≥ |E|`.

The first row enforces `E = 0 mod r`. The compiler chooses `t` such that `r·2^t > B`, and enforces the low `t` bits of `E = 0 mod 2^t` with radix carries. It independently bounds each integer carry-row residual below `r` before emitting the field equation. Since `r` is odd, every satisfying assignment gives `E=0` over the integers. Small affine expressions are inlined. Neither this bound nor the row structure depends on the private witness. The native-alias regression demonstrates why the carry rows are necessary.

## Pairing equation

Fix `L = IC[0] + Σ input[i]·IC[i+1]`. The four terms in the Groth16 pairing product use `(A,B), (−C,δ), (−L,γ), (−α,β)`. Only the first two pairs have variable operands. The encoder precomputes the two fixed pairs and fixed-G2 lines. It works in a power basis with `W^6=9+i` and `i²=−1`. Group membership, infinity selection, and intermediate line values are constrained. The main Miller loop also checks that the variable twist point is in G2, including when its G1 operand is infinity. [gnark subgroup criterion](https://github.com/Consensys/gnark/blob/v0.16.5/std/algebra/emulated/sw_bn254/precomputations.go)

For the unreduced Miller product `f`, set `H = p^12−1`, `u = 4965661367192848881`, and `λ = 6u+2+p−p²+p³`. The BN254 constants satisfy `gcd(λ,H)=3r`. Fix an element `η` of order 27 generating the 3-primary subgroup. An accepting product satisfies `f^(H/r)=1`. Equivalently, there exist a nonzero `z` and a selector `e ∈ {0,1,2}` for which `f·η^e·z^λ=1`. In exponents of the cyclic multiplicative group, multiplying by one of the three corrections reaches the subgroup of λ-th powers precisely when the exponent of `f` is divisible by `r`. The implementation verifies the nonzero inverse and allowed selector and checks the final equation inside the rows. It initializes the signed Miller loop at `z` so that the `6u+2` powering is shared. Three Frobenius maps supply the remaining exponent terms. [On Proving Pairings](https://eprint.iacr.org/2024/640)

For the shared subgroup check, write `ψ` for Frobenius on the untwisted curve. The final loop point obeys `[6u+2]Q + ψQ − ψ²Q = −ψ³Q` exactly on the required subgroup. The tests check the gcd of the Frobenius norm with the BN254 twist order, and verify that every affine prefix used without a denominator witness excludes exceptional divisors throughout that group. The G2 check still runs when the other pairing operand is infinity. [gnark fixed subgroup relation](https://github.com/Consensys/gnark/blob/v0.16.5/std/algebra/emulated/sw_bn254/precomputations.go) · [Subgroup membership analysis](https://eprint.iacr.org/2022/348)

## Using the rows

Each row is a sum of product terms `[coefficient, left_start, left_width, right_start, right_width]` equated to zero in Fr. Each slice denotes `Σ 2^j w[start+j]`. The reserved pair `(−1,0)` denotes one. This is a compact encoding of ordinary products of public linear forms in Boolean variables. The manifest commits to the statement and row stream, records dimensions, and locates the proof coordinates. The receiver must pin that manifest. The standalone checker reads only the public rows, manifest and packed bits. It performs no elliptic-curve computation. The native Go verifier can independently check the decoded proof.

This frontend runs without the historical gnark diagnostic hint for the outer commitment. Integration with a full-parameter Praxis QAP, adequate security parameters for this shape, corresponding encryption and decryption, and an actual Syscoin AuxPoW guest remain separate work. No ciphertext runtime or secrecy level follows from the frontend counts.
