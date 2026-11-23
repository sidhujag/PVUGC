# Fixed-statement compact BN254 encoder

This program derives Boolean quadratic constraints over the BN254 scalar field for the commitment-free, five-public-input SP1 Groth16 verifier. Its public constants come from a validated Groth16 key and five canonical scalar-field inputs. A prover supplies the eight base-field coordinates of A, B and C. The lifter produces the intermediate bits needed to satisfy the public constraints. Generating the constraints requires only the public statement.

The default combines consecutive lines of the optimal Ate pairing on BN254 into a conic. A separate reduced Tate implementation serves as a reference. This is an independently derived encoder. Section 6.1 of the Praxis paper gives different dimensions for the authors’ internal SP1 v6.1.0 encoder and does not specify its gates. The researchers explicitly scope that encoder outside their public Lean formalization. [Praxis paper](https://eprint.iacr.asia/2026/2971.pdf#page=35) · [Authors’ implementation boundary](https://github.com/psivesely/praxis-lean/blob/60d3defeebd77caa0e57babe97991e672b948bb6/README.md)

## Measured v6.1.0 statement

| Encoder | Boolean unknowns | Constraint rows |
| --- | ---: | ---: |
| Previous uniform gnark wire expansion | 513,074,158 | 1,264,008 plus a commitment to enforce |
| Optimal Ate with integer limbs (`ate`) | 3,501,401 | 17,687 |
| Fused Miller steps with centered arithmetic (`ate-fused`) | 887,309 | 5,139 |
| Scaled G2 line coefficients (`ate-moving`) | 808,018 | 4,471 |
| Paired lines with packed exact arithmetic checks (`ate-paired`) | 778,861 | 3,837 |
| Conic with affine-product rows (`ate-conic`) | 599,347 | 2,690 |
| Conic with a signed width-four window (`ate-conic-window`) | 573,769 | 2,594 |
| Leading-three window with direct conic checks (`ate-conic-optimized`, default) | 545,856 | 2,476 |
| Authors’ reported encoder | 391,693 | 1,692 |

The default uses at most 2,036 products of linear forms per row. The packed witness is 68,232 bytes. The public constraint recipes occupy 2,638,762 bytes before gzip, with row digest `434494d311acdb55a844e99b595842f92fcd5879fbb8178853c4f6c1b91506f0`. Of the 545,856 bits, 477,520 encode 1,880 base-field coordinates and 68,336 cover exact arithmetic and selectors. Both proof fixtures lift to the layout obtained from public inputs alone. The raw recipe size excludes the cost of evaluating or publishing the full Praxis ciphertext.

The width-four comparison schedule has 65 doublings and 11 signed additions. The default begins at the already constrained point `[3]Q` and uses 62 doublings and 11 additions. A short table supplies the actual curve points and Miller-function factors for odd digits up to seven. Both the point table and the factors are constrained. Larger windows incur additional table costs. The tests check nonzero divisors in the curve prefix calculations and verify that the reduced pairing agrees with the independent reference loop.

## Reproduce from the frontend directory

Python 3.10+ runs the encoder with the standard library. The independent native check uses the pinned Go module and real v6.1.0 fixture documented in [the frontend README](../README.md). These commands use a new working directory for generated outputs.

```sh
out=$(mktemp -d)
go build -mod=readonly -o "$out/native" .
"$out/native" -statement testdata/sp1-v6.1.0.vk testdata/sp1-v6.1.0-inputs.json > "$out/statement.json"
python3 -m compact compile "$out/statement.json" --manifest "$out/manifest.json" --rows "$out/rows.jsonl.gz"
python3 -m compact lift "$out/statement.json" "$out/manifest.json" testdata/sp1-v6.1.0-pairing.json "$out/witness.bin" --index 0
python3 -m compact check "$out/manifest.json" "$out/rows.jsonl.gz" "$out/witness.bin" > "$out/proof.json"
"$out/native" -verify-decoded testdata/sp1-v6.1.0.vk testdata/sp1-v6.1.0-inputs.json < "$out/proof.json"
```

The fixture includes a second valid proof at index 1. Use a fresh witness filename when lifting it. A standalone proof JSON uses the same `a`, `b`, `c` coordinate representation. The raw verifying key and the five public inputs must be authenticated by the caller. The bridge must derive those inputs from its chosen program and withdrawal. The encoder proves only the fixed verifier relation.

## Exact base-field arithmetic in scalar-field rows

Write `p` for the BN254 base-field prime and `r` for its scalar-field prime. Every private field value is represented by a little-endian linear form in 254 Boolean unknowns. A generated solution can use a noncanonical representative of the same residue. The decoder reduces proof coordinates modulo `p` before producing a canonical native point.

For a signed sum of products `S` and its output residue `z`, the lifter supplies an integer quotient `h`. The public compiler derives lower and upper bounds on `h` from the widths of the Boolean operands, represents it with an offset and a bounded binary magnitude, and forms `E = S − z − ph`. The possible values of every bit pattern, including unused slack above the nominal upper bound, are included in the residual bound `B ≥ |E|`.

The first row enforces `E = 0 mod r`. The compiler chooses `t` such that `r·2^t > B`, and enforces the low `t` bits of `E = 0 mod 2^t` with radix carries. It independently bounds each integer carry-row residual below `r` before emitting the field equation. Since `r` is odd, every satisfying assignment gives `E=0` over the integers. Small affine expressions are inlined. Neither this bound nor the row structure depends on the private witness. The native-alias regression demonstrates why the carry rows are necessary.


The default first expands packed multiplication in binary digits and reduces each public digit coefficient to its centered representative modulo the base prime. This narrows the exact quotient and carry ranges. The compiler packs bounded integer check rows only when their combined absolute bound is strictly below the scalar prime and their product count fits the public cap. For two residuals with absolute bounds `B1,B2`, a zero packed value `E1 + (B1+1) E2` implies `E1=0` by reduction modulo `B1+1`, then `E2=0`. The public bounds establish that the integer packed value equals zero whenever its scalar-field row does. [Centered foreign-field coefficients](https://eprint.iacr.org/2025/695)

## Pairing equation

Fix `L = IC[0] + Σ input[i]·IC[i+1]`. The four terms in the Groth16 pairing product use `(A,B), (−C,δ), (−L,γ), (−α,β)`. Only the first two pairs have variable operands. The encoder precomputes the two fixed pairs and fixed-G2 lines. It works in a power basis with `W^6=9+i` and `i²=−1`. Group membership, infinity selection, and intermediate line values are constrained. The main Miller loop also checks that the variable twist point is in G2, including when its G1 operand is infinity. [gnark subgroup criterion](https://github.com/Consensys/gnark/blob/v0.16.5/std/algebra/emulated/sw_bn254/precomputations.go)

The earlier full-field modes test the unreduced Miller product as follows. For the unreduced Miller product `f`, set `H = p^12−1`, `u = 4965661367192848881`, and `λ = 6u+2+p−p²+p³`. The BN254 constants satisfy `gcd(λ,H)=3r`. Fix an element `η` of order 27 generating the 3-primary subgroup. An accepting product satisfies `f^(H/r)=1`. Equivalently, there exist a nonzero `z` and a selector `e ∈ {0,1,2}` for which `f·η^e·z^λ=1`. In exponents of the cyclic multiplicative group, multiplying by one of the three corrections reaches the subgroup of λ-th powers precisely when the exponent of `f` is divisible by `r`. The implementation verifies the nonzero inverse and allowed selector and checks the final equation inside the rows. It initializes the signed Miller loop at `z` so that the `6u+2` powering is shared. Three Frobenius maps supply the remaining exponent terms. [On Proving Pairings](https://eprint.iacr.org/2024/640)

The projected pairing modes check the residue in the cyclic quotient of the nonzero extension-field elements by the nonzero elements of its degree-six subfield. This quotient has order `p^6+1`, with `gcd(λ,p^6+1)=r`. Every valid pairing product has a correcting root in the quotient. If the root is the identity, multiplying it by a fixed public element of order `r` gives another correcting root in the finite chart. This makes the selection available for every valid proof. The six odd coefficients of the final product enforce equality in the quotient.

The paired-line encoder represents a finite line product by `A+W` with six base-field coordinates in `A`. If the original line product is neutral in the quotient, the encoder substitutes the class of `W`, of order two. Since `r` is odd, this class is an `r`-th power and the substitution preserves the reduced pairing. The fixed second line's nonzero norm constrains when the substitution is allowed. A scaled twist trace supplies the first line's evaluated coefficients and retains the G2 subgroup test. Each dense doubling uses `F_next · conjugate(line) = F_old²`; its subfield normalization also preserves the reduced pairing.

For the shared subgroup check, write `ψ` for Frobenius on the untwisted curve. The final loop point obeys `[6u+2]Q + ψQ − ψ²Q = −ψ³Q` exactly on the required subgroup. The tests check the gcd of the Frobenius norm with the BN254 twist order, and verify that every affine prefix used without a denominator witness excludes exceptional divisors throughout that group. The G2 check still runs when the other pairing operand is infinity. [gnark fixed subgroup relation](https://github.com/Consensys/gnark/blob/v0.16.5/std/algebra/emulated/sw_bn254/precomputations.go) · [Subgroup membership analysis](https://eprint.iacr.org/2022/348)

## Conic updates

For a signed addition, the tangent and the following chord share an intermediate point. Their product divided by that point's vertical line is a conic. The factor removed belongs to the degree-six subfield, so its removal preserves the reduced pairing. The encoder checks the three degree-two equations for the conic coefficients and retains the original G2 trace and subgroup check. It also groups the last two Frobenius chords. The prefix and Frobenius scalar checks in `test_conic.py` rule out the zero slope sums on valid subgroup inputs. Disabled inputs and neutral paired lines retain their reduced-pairing semantics.

The default checks a tangent and chord directly using the conic's intersections with the twist. The sum and pairwise products of the four intersection abscissas enforce the repeated tangent root. A nonzero normalization coefficient rules out a degenerate vertical conic. For the final pairing comparison it computes the right-hand Frobenius product in the finite degree-six chart and checks the even and odd halves of the dense result by cross multiplication. The two additional forbidden root choices have nonzero exponents modulo `r`. Rotating the correcting root over its order-`r` choices therefore preserves a lift for each accepting input.

## Using the rows

The default v2 format describes ordinary quadratic rows over Fr. Each row contains public recipes for the coefficients of two linear forms per product. Grouping terms with the same left digit keeps the number of products within the declared cap and permits smaller digit widths. `factored_bqs.praxis_forms` expands a recipe to coefficients on the original Boolean variables. The standalone checker authenticates the recipe stream under the pinned manifest, checks public bounds and evaluates the constraints against a packed assignment. The published recipe size measures the compact description. Expanding all forms or generating a full ciphertext incurs additional work.

In the earlier v1 format each row is a sum of product terms `[coefficient, left_start, left_width, right_start, right_width]` equated to zero in Fr. Each slice denotes `Σ 2^j w[start+j]`. The reserved pair `(−1,0)` denotes one. This is a compact encoding of ordinary products of public linear forms in Boolean variables. The manifest commits to the statement and row stream, records dimensions, and locates the proof coordinates. The receiver must pin that manifest. The standalone checker reads only the public rows, manifest and packed bits. It performs no elliptic-curve computation. The native Go verifier can independently check the decoded proof.

This frontend runs without the historical gnark diagnostic hint for the outer commitment. Integration with a full-parameter Praxis QAP, adequate security parameters for this shape, corresponding encryption and decryption, and an actual Syscoin AuxPoW guest remain separate work. No ciphertext runtime or secrecy level follows from the frontend counts.
