# Single-table Bitcoin payout experiment

The prototype opens one native Praxis factor table, selects packets for one exact Bitcoin payout and assembles a 64-byte BIP340 signature. Its Bitcoin script test verifies that the reserve signature commits to John's recipient, amount, change, fee and the winning Close outpoint. The payout builder puts every satoshi of unused reserve principal in a separate change output, and the command checks that output against its pinned fixture policy. The Close input covers the fee and returns its unused contribution separately. The experiment pins the payout during arming. The deposit-time bridge requires those terms to come from a future authenticated Syscoin burn.

## Run from a clean checkout

Use Go 1.26.8 or later. From the repository root, build the command and arm a synthetic receipt. Use a new archive path.

```sh
cd prototypes/praxis/frontend
go test -mod=readonly ./...
go build -mod=readonly -o /tmp/pvugc-shared-pay ./cmd/shared-pay
/tmp/pvugc-shared-pay arm /tmp/synthetic-pay.px
```

Copy the 64 hexadecimal characters printed as `archive_sha256` at arming. In a separate process, pass that pin and the public archive to the opener. An actual ceremony must authenticate the pin independently.

```sh
arming_sha256='paste the digest printed by arm here'
/tmp/pvugc-shared-pay open /tmp/synthetic-pay.px "$arming_sha256"
```

The opener checks the pin, authenticates the eligible packets, interpolates exactly 256 field evaluations, and executes the reserve input's tapscript. The separate two-input test executes the Close input with an ordinary claimant key. The command uses synthetic outpoints and never contacts Bitcoin or Syscoin.

## What goes in the archive

1. The armer samples a disposable Schnorr key and nonce. A random masking polynomial of degree 256 supplies 767 possible evaluations in 265 packets. For one challenge, the selected points have cardinality 256 and their sum equals the BIP340 challenge. Interpolation returns the scalar Bitcoin needs for that payout.
2. The Boolean system pins each packet's eligibility bit and adds three scratch bits to it. Each scratch bit satisfies `(1 - eligible) * scratch = 0`. The armer writes one native table and wraps each packet under the three designated search coefficients. The wraps bind the table, fixture policy, exact receipt, signer and packet index. Wrapped packets and the table are serialized together.
3. The opener runs the native pairing decoder on the baseline witness and again for each legal single-bit change. Subtracting the two unique integer search results yields one wrapping coefficient. A degenerate search returns an error. The selected packets reconstruct the signature. Arming and opening need no shared process memory.

## Size

| Object | Size | Basis |
| --- | ---: | --- |
| Single factor table | 2,045,349 bytes | Serialized native fixture with 265 flags, 795 scratch coordinates and the six-copy development grid |
| All raw evaluation packets | 24,544 bytes | 767 scalars of 32 bytes each |
| All authenticated packets | 31,964 bytes | 265 AES-GCM envelopes including generated nonce and tag |
| Evaluations opened for one Pay | 8,192 bytes | 256 selected scalars |
| Complete fixture archive | About 2.09 MB | Includes table, JSON metadata and base64 encoding of the packets |
| Authors' full Groth16 capsule | 7.88 GiB | Authors' published 100-bit parameter estimate for fixed-message Praxis |
| This repository's full-width SP1 fixture | 1,051,934,251 bytes | Previously measured at the smaller development grid |

At the reviewed revision `c5ede4b`, arming wrote 2,089,486 bytes in 0.139 seconds on an Apple M5 Max. Two separate opener processes using the arming pin each selected 129 packets and performed 388 native searches. They returned byte-identical reserve signatures in 48.962 and 49.990 seconds. A different archive pin was rejected. Each search processes the factor table again. One physical copy does not imply one decoding pass.

The updated fixture uses archive format `PXSPAY02` for separate principal and fee change. It produced a 2,089,541-byte archive in 0.108 seconds. An independent opener selected 140 packets, performed 421 native searches and verified the reserve signature in 51.195 seconds. The file size can vary slightly with JSON metadata, and the number of selected packets depends on the random signer's challenge. Its synthetic transaction pays 0.75 BTC from a 1 BTC reserve, returns 0.25 BTC to the pinned reserve-change script, and pays a 2,000 satoshi fee from the 10,000 satoshi Close input. The remaining 8,000 satoshis return to the fee contributor.

The new fixture has 1,060 Boolean unknowns. It contains no SP1 Groth16 verifier, AuxPoW ancestry or underlying NEVM burn proof. At the authors' published illustrative grid, 795 extra variable columns alone would occupy 17,121,120 bytes. Eligibility constraints, the full verifier, QAP powers, arming and confirmation of the parameter inequalities need independent accounting. This repository's earlier 588,373-variable SP1 layout estimated 11.83 GiB for group arrays at the larger grid. A compact selector fixture therefore establishes the one-table storage layout while leaving deployment size open. [Praxis paper](https://eprint.iacr.org/2026/2971) · [Full-width fixture measurement](frontend/README.md#measured-cpu-run)

## Security and transaction boundaries

**One payout.** In the ideal experiment that releases only the 256 authorized evaluation values, their distribution can be simulated from the one signature response. The 255 lower polynomial coefficients are independent masks. The real opener also has the entire group table, search results and authenticated ciphertexts. The published fixed-message Praxis theorem does not establish secrecy of unselected coordinate triples after legal openings. The development profile has eight possibilities per coordinate, at most nine bits per wrapping tuple. This implementation measures functional correctness only.

**Two payouts.** Two different BIP340 challenges signed by the same disposable key with the same nonce disclose signing authority. This happens offline, regardless of which Pay wins on Bitcoin, and would remain true with perfect packet confidentiality. Repeating the same byte-identical Pay is safe with respect to this specific nonce-reuse issue. A fresh Close outpoint changes the signed message. [BIP340](https://bips.dev/340/) · [BIP341 signature message](https://bips.dev/341/#common-signature-message)

**Work and retries.** A proposed source policy scans each authenticated Bitcoin history in order and fixes the first eligible Close for a reserve. Vetoed attempts can precede that decision indefinitely. If two *different* decisions require 100 strictly subsequent qualifying Bitcoin blocks on incompatible histories, one of the suffixes necessarily contains at least 100 off-path blocks relative to the other. That counts qualifying history. Existing stale or privately supplied blocks, and work shared across withdrawals, change the incremental cost to an attacker. An honest challenger with qualifying published evidence can relay it without mining a replacement chain. A single late inconsistent tag proves neither the required divergence at the burn height nor the required work. The history verifier must enforce both when the policy requires them. A relative input sequence of 100 permits Pay in block `h+100`. Requiring 100 strict descendants already mined before opening is a separate history check. [BIP68](https://bips.dev/68/)

**Deposit setup.** The armer in this fixture knows the signing secrets, polynomial and wrapping coordinates. Separate opening proves it needs no armer online. One-honest-party safety requires private, verifiable arming with up to N−1 corrupt participants and erasure by the honest participant. The implementation has no such ceremony. Stock Praxis uses classical bilinear groups and the native payout uses Schnorr. A post-quantum payout has separate requirements.

For John's future payout, the source proof must authorize the burn amount and recipient, assign the reserve, identify the winning Close and its previous-output script and value, and constrain the fee and change destination. Its verifier must bind those fields to the exact BIP341 message and all 265 flags. The arming pin in the fixture authenticates known bytes. It cannot certify that a future withdrawal happened. The two-input test exercises ordinary Bitcoin signature semantics. A protected marker role and real chain observations would have to enter the protocol and its security argument before a reserve could rely on this design.

## A separate design for two eligible histories

A candidate for two authorized messages derives the public nonce point from the complete Pay using two precommitted nonce points. It replaces the single polynomial's evaluation packets with masked contributions over an XOR circuit. Within an ideal interface that releases only the eligible packets, the connected set of changed wires makes the second view disclose just the second authorized total. Independent labels for each binary wire state permit smaller per-gate ciphertexts. The legal patterns of one XOR gate differ in exactly two of its three positions, so the labels from two local openings can reconstruct only those two legal patterns.

This proposal changes the signing encoder. The existing executable exercises the single-message polynomial. A two-view bridge would still need to show that an evaluator with the complete public archive can obtain only the authorized wire labels, prove security for adaptively chosen Bitcoin messages under the public nonce commitments, and implement the one-honest-party ceremony. The size measured above belongs to the single-message experiment.
