# Praxis cancellation prototype

This crate replaces PVUGC's historical pairing-derived release key in an executable fixed-transaction experiment. It uses the existing PVUGC Bitcoin sighash code. A three-party MuSig2 adaptor pre-signature and a public setup archive let a challenger finish a native Taproot signature offline. The Rust setup uses the Boolean relation `(x − y)² = 1` and a synthetic Bitcoin output. A separate [SP1 signature capsule](frontend/README.md#offline-signature-release) encrypts the resulting signature under a fixed SP1 v6.1.0 Groth16 verifier. This second experiment exercises offline recovery at the full verifier width with a six-copy development profile.

## Run

From the repository root, run the locked release test suite.

```sh
cargo test --release --locked --manifest-path prototypes/praxis/Cargo.toml
```

To run the three-signer experiment in separate processes, build the example. Use a new directory and keep the public receipt hash printed at setup. Supply that hash to both recovery processes.

```sh
cargo build --release --locked --example cancel --manifest-path prototypes/praxis/Cargo.toml
binary=prototypes/praxis/target/release/examples/cancel
receipt=$("$binary" arm ./praxis-fixture 2)
"$binary" recover ./praxis-fixture "$receipt" 01
"$binary" recover ./praxis-fixture "$receipt" 10
```

Each recovery outputs the same 65-byte Bitcoin witness signature. Inputs `00` and `11` exit with a failure. Pass `104` in place of `2` to exercise the larger audit subset on the same reduced relation. Only the public archive and receipt are written to the directory. The setup example simulates all three participants in one process.

The Rust crate has its own manifest and lockfile so it can run on CPU independently of the older SP1 fork.

## Measured CPU run

The existing 16-CPU Linux server built commit `0f55d17` in release mode. All 13 tests passed. Separate arming and recovery processes used fresh randomness, three simulated signers and the reduced fixture. Each pair of valid openings produced identical Bitcoin signature bytes, and the two invalid witnesses returned failures.

| Capsules per signer | Public archive | Setup | Open with 01 | Open with 10 | Peak process RSS |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 82,644 bytes | 0.65 s | 0.42 s | 0.42 s | 4.5 MiB |
| 104 | 4,268,265 bytes | 31.71 s | 16.16 s | 16.20 s | 16.3 MiB |

Each public receipt was 275 bytes. The timings include archive encoding and validation as applicable, with no precomputed decryptor state. The larger run uses 312 small capsules. These measurements do not extrapolate to full Groth16 statements.

## What the experiment checks

- The reduced BN254 backend implements the group-valued left and right factors, extension-field weights and ties, quotient and remainder bases, paired alpha copies, and bounded search in Praxis Figures 6 and 7. The program specializes the QAP to the fixture. The backend uses the hash of the recovered target-group value to unmask a random 100-bit seed. A separate domain-separated hash derives a 32-byte key for the authenticated share encryption. The profile uses 2 Boolean variables, extension degree 4, search parameter 8, and real curve operations.
- Each signer commits to an independently sampled Bitcoin adaptor share. The setup package binds the signer, exact Taproot cancellation sighash, relation, Feldman coefficient points, and ciphertext bytes. The signer proves possession of the scalar behind its constant coefficient. Opening uses the same policy locally. Bitcoin verifies the completed signature under its tweaked output key.
- The fixtures cover both satisfying assignments, both unsatisfying assignments, incorrect audit openings, wrong setup roster or coin board, incorrect archive receipt, missing adaptor shares and changes to the Bitcoin transaction. These are correctness and rejection checks. They provide no concrete estimate of the cost of unauthorized decryption.

## One honest participant at setup

All Bitcoin signers agree on one authenticated roster and session. Each signer privately chooses a separate scalar `s_i` and a degree-at-most-`d` polynomial `f_i` with `f_i(0)=s_i`. The public coefficient points include `T_i=s_i G`. At each of `M` distinct nonzero coordinates, it encrypts `f_i(j)` under an independently randomized capsule. We use `d=floor(M/2)`.

Before revealing any challenge coins, all signers agree on the same package digest and commitment board. They combine their committed coins to choose one common set of `d` coordinates. Each contributor reveals the values and encryption randomness only at those coordinates. Everyone checks the points and recreates the selected ciphertexts byte-for-byte. The single-use opening state pins the exact coin board its owner accepted. Signers approve the same archive ID before providing their MuSig2 partial pre-signatures. Authenticated agreement and durable prevention of a second opening across process restarts are requirements of a deployment. This library models that exchange in memory.

For a fixed committed package, suppose one participant created at most `d` faithfully formed evaluations. At most one of the `binomial(M,d)` possible audit sets can pass. With a uniformly sampled set, the probability that any of `N` such participants escapes detection is at most `N / binomial(M,d)` per attempt. In the implementation the subset is generated from committed coins using SHA-256 and ChaCha20, so using that ideal sampling bound assumes their hiding and pseudorandomness. Selective abort allows another attempt with a completely fresh ceremony. Over `a` attempts the union bound gains a factor of `a`.

For a qualifying witness, if at least one unopened evaluation for each participant decrypts to its committed scalar, the `d` public values plus that one value uniquely determine `f_i(0)`. Recovery verifies the evaluation and the final share point. Every such recovery supplies the same scalar sum to the same pre-signature. Missing an independent honest share leaves an incomplete signature. The resulting secrecy statement is conditional on the WE backend protecting the unopened evaluations in the joint transcript, the discrete-log/signature assumptions, and one setup participant keeping its secrets private. The statistical audit bound only concerns correct formation. Praxis also has a witness-dependent nonzero-weight condition. Its honest fixed-witness correctness bound does not by itself quantify over maliciously selected capsules or adaptive future witnesses.

The Bitcoin test sets `M=2,d=1` to exercise the flow. A separate four-row test enumerates all six audit challenges with two malformed rows and checks that exactly one passes. At `M=104,d=52` the per-signer audit error under ideal sampling falls below `2^-100`. At the paper's estimate of 7.88 GiB per ciphertext this would use about **820 GiB per signer** before other protocol data. An efficient proof of correct Praxis encryption could replace this audit, but would need to verify the actual backend, payload and point binding.

## Full Syscoin integration

The authors report an SP1 v6.1.0 Groth16-verifier encoding with 391,693 Boolean unknowns and 1,692 constraints. Their public Lean repository formalizes parts of the security and correctness argument. The full executable encoder, witness lifting, and corresponding BN254 test vectors were unavailable for this prototype. The [independent compact Boolean frontend](frontend/compact/README.md) now derives and checks a larger encoding for that same verifier. The Go backend consumes those rows, constructs their QAP and streams a BN254 ciphertext. It uses six copies to measure recovery. Evaluating secrecy requires selecting and justifying parameters for this verifier shape. An independently audited AuxPoW fork guest must also bind the withdrawal, ancestry, starting difficulty context and cumulative-work rule to that statement.

We also measured an [independent gnark verifier frontend](frontend/README.md) with real SP1 keys. A uniform 254-bit expansion of its private and internal wires needs 513,074,158 Boolean unknowns. At the paper's left-factor width of 192, those two arrays alone would use 5.73 TiB per capsule. Its raw rows also leave an outer commitment challenge to be enforced. This calculation rules out using that direct port at the claimed compact size on the test server.

The full configuration also requires a correctly generated Groth16 verifying key. Having one honest PVUGC signer does not authenticate an unrelated SP1 setup ceremony. Deployment must pin and qualify that CRS separately.

The full configuration would require end-to-end measurement and qualification of malicious setup, security across multiple related ciphertexts, and correctness for the application's witness distributions. The published construction uses classical bilinear groups. Its operation counts and ciphertext estimates do not describe this fixture's security or runtime.

[Praxis paper, sections 5 and 6](https://eprint.iacr.asia/2026/2971) · [Authors' pinned formalization and assumptions](https://github.com/psivesely/praxis-lean/blob/60d3defeebd77caa0e57babe97991e672b948bb6/README.md)
