# An exact Bitcoin signer for two authorized payout digests

John can choose a recipient and amount after deposit. A retry that spends a new Close outpoint has a new Bitcoin signature message. This note gives a classical signature reduction for two adaptively authorized messages, assuming an ideal mechanism for releasing just the authorized values. It addresses forgeries under the native reserve key, including signatures with a nonce of the adversary's choice. The public Praxis archive still needs its own confidentiality theorem.

## Deposit and payout

Use a fresh disposable BIP340 key for one reserve and one input role. Let the group order be $n$, the generator $G$, and the even public key $X=xG$. Fix the source policy and context for the lifetime of this key. Sample a uniform nonidentity group point $H$ with unknown discrete log in the real setup. Independently sample three scalars for each of $k,b,\rho$. For each index publish signed points

$$
C_j=k_jG+b_jX, \qquad T_j=b_jH+\rho_jG.
$$

The native fixture resamples each coefficient triple until both public points have compressed encodings. Conditioned on those published points, the masking scalar $b_j$ is still uniform. The public structure contains 295 field bytes including the 32-byte context, 32-byte signing key, 33-byte base and six 33-byte commitments. This measures only the signing parameters.

1. Reconstruct the exact 32-byte BIP341 signature message $m$ for the reserve input. Split it into unsigned big-endian 128-bit halves $L,R_h$. Write $v=(1,L,R_h)$ and $f(v)=\sum_j v_j f_j$ for points or scalars. Every bit of the message survives. Any two distinct messages yield linearly independent rows because both start with one. The source policy must reconstruct the exact authorized transaction, including the reserve and marker inputs, principal, recipient, fees and change. Each input role has its own key.
2. After verifying the source evidence for that message, the first ideal release returns $B=b(v)$ and $Z=\rho(v)$. John checks $BH+ZG=T(v)$, computes $U=C(v)-BX$ and rejects infinity. Set $R=\sigma U$ with even $y$, where $\sigma\in\{1,-1\}$.
3. The second release checks the authorization for the same complete message independently, verifies the opening and derives the nonce parity and native challenge itself. For $e=H_{340}(R_x,X_x,m)\bmod n$ it releases $s=\sigma k(v)+ex$. John sends the normal 64-byte Bitcoin signature $R_x\parallel s$. Its verification equation is $sG=R+eX$. The signature is identical for repeated openings of the exact same message.

The Pedersen opening fixes which nonce can enter the second phase. Two openings of a fixed commitment with different $B$ imply knowledge of the discrete logarithm of $H$ relative to $G$. A valid opening authorizes nothing by itself. In particular, linear combinations of earlier openings can supply valid commitment openings on the span of their message rows. The second phase must authenticate the receipt and source history even when its Pedersen check succeeds.

## Two adaptive grants

The ideal game gives the evaluator the public points and access to the classical BIP340 random oracle. A grant exposes at most the two specified opening scalars and, if separately authorized, the signature. It may be delayed, repeated or abandoned. Count distinct messages receiving *either* positive release, across all histories and archives under the key. A direct second-stage request that releases a response counts as a grant even if the requester skipped the first stage. The game allows at most two such messages. This is a hypothesis about the exposure, not a counter Bitcoin enforces. The ideal transcript contains no additional hash evaluations, branch decisions or setup secrets correlated with unreleased values.

**Reduction.** Give a simulator only the normalized key $X$ from a native key-only BIP340 forgery experiment. Choose $H=hG$ for a uniform nonzero $h$. Sample independent $a_j,c_j,d_j$, publish $C_j=a_jG+c_jX$ and $T_j=d_jG$, and match the real setup's finite-point conditioning. This produces the real distribution of public parameters. It requires a simulatable random-point CRS. Simply hardcoding a particular generator of unknown log would require a separate argument.

On a new grant sample uniform $t\in\mathbb F_n$ and give the requester

$$
B=c(v)+t, \qquad Z=d(v)-hB.
$$

This yields $U=a(v)G-tX$. In its own oracle interface the simulator sets the challenge at $(R_x,X_x,m)$ to a raw 256-bit value reducing to $e=\sigma t$, drawn uniformly from that scalar's raw preimages. It does this before releasing the opening. It answers the second stage with $s=\sigma a(v)$. The equation $sG=R+eX$ holds without knowing $x$. It caches the result for the exact message. Every other challenge query is forwarded unchanged to the external key-only experiment.

**Why this works adaptively.** Condition on the public points. In the real experiment $b$ is uniform because $k$ and $\rho$ each mask its contribution. In the simulation $c$ is uniform because $a$ masks its contribution to $C$. A first programmed transcript fixes at most the one evaluation $c(v_1)=B_1-\sigma_1e_1$. Its $Z_1$ is already determined by $B_1$ and the commitment. Its $s_1$ is already determined by the native verification equation. For any distinct adaptive second message, independence of $v_1,v_2$ leaves $c(v_2)$ uniform. Thus $B=c(v)+t$ is uniform and independent of $t$ at each grant, given the public transcript so far. Conditioned on $B$, the nonce point and its parity are fixed, and the programmed scalar $\sigma t$ is uniform. After conditioning on the two opening scalars, the only distinction from an honest native signature here is the raw-hash bias or a programming collision. The same calculation covers partial reads if they disclose only projections of the granted values and are charged as grants.

Let $q_H$ bound classical challenge queries. Before a fresh grant, $B$ makes $U$ uniform conditional on the prior view. Infinity has probability $1/n$. Any guessed normalized nonce x-coordinate has at most two preimages, so an earlier query at the signing input has probability at most $2q_H/n$ per grant. In the real native hash, let $r=2^{256}-n$. Replacing its reduced-scalar distribution by uniform and choosing uniformly among raw preimages costs total variation

$$
\delta=\frac{r(n-r)}{n\,2^{256}}
$$

per programmed grant. All forwarded queries retain the native raw distribution. For the canonical ideal interface define $E=(4q_H+2)/n+2\delta$. If an implementation allows caller-chosen commitment openings in the second stage, also charge the probability of a successful alternate Pedersen opening. Reserve-policy binding additionally relies on the collision resistance of the exact native transaction message.

**A signature for a third message.** A successful signature for a message that received neither grant verifies under the *external* oracle with any nonce. The wrapper only overrode inputs whose message was one of the granted messages. Its native forgery success is therefore at least the ideal forgery probability minus $E$. There is no guessing of hash-query positions and no extra forking loss on top of the native key-only unforgeability assumption. This is a classical random-oracle proof about the isolated signer. Independent access to the fixed hash function outside the simulated interface or auxiliary signatures under the disposable key are outside this experiment. [BIP340](https://bips.dev/340/) · [BIP341](https://bips.dev/341/#common-signature-message)

**An unsigned message whose guard already opened.** We can cover this case too. Choose a hidden index uniformly in ${0,1,2}$. Index zero uses the wrapper above. A positive index identifies a grant on which the wrapper draws $B$ directly and uniformly, returns $Z=d(v)-hB$, and leaves that message's challenge entirely external. It aborts if it must also supply that message's signature. All other grants use the programmed method. A special first grant reveals no $c(v)$, so the other grant retains the required uniform mask. If the special grant is second, the directly sampled $B$ also has the correct conditional law. Assign each successful real forgery index zero when its message never received a grant, or its grant ordinal when only the opening was released. For the matching guess the simulator never needs to sign that message, and the external verifier agrees. In this stronger game the ideal unsigned-message success is at most $3\,\mathrm{Adv}_{340}^{\rm key\text{-}only}+3E$ by a conservative coupling, plus the separately applicable commitment-binding error. A veto after the first phase is therefore covered at the ideal signing layer. Whether the real capsule can observe and enforce that veto is a source-policy question.

Signing packets in a concrete implementation are a distinct exposure. To apply the unsigned-message claim, either charge the descriptor as signed from its first signing-packet disclosure, or show how to simulate that partial disclosure before obtaining a response. A guard opening by itself is covered.

## One honest signing role on current Bitcoin

The reserve can use a Taproot script leaf that checks an independent signature from every setup participant, with no other spendable leaf and a verified NUMS internal key. Each participant has its own disposable signing key and its own protected release. Every signer commits to the same source policy and exact BIP341/BIP342 message for the final reserve script. Funding occurs only after the reserve script and arming artifacts have been pinned. John can subsequently assemble the Bitcoin witness from their offline releases.

Under these conditions a successful spend of the leaf contains a valid signature under the honest participant's key. The unsigned-message reduction therefore applies to that participant even if all other signers disclose all of their own secrets. This argument needs the honest artifact's selective-release property to hold given all the corrupt participants' transcripts. Independent roles avoid a shared signing key. They cost one signature per role, and separate ciphertexts can cost one archive per role. The key-path bypass assumption and the commitment to the exact leaf must hold. Verification that malicious participants generated usable artifacts *before* funding is a separate liveness requirement. Switching to one aggregated Bitcoin key or one shared set of hidden table factors requires a security argument for that choice. [BIP341](https://bips.dev/341/#constructing-and-spending-taproot-outputs) · [BIP342](https://bips.dev/342/#signature-validation)

## What the prototype checks

The [Go fixture](frontend/guardednonce/fixture.go) uses native secp256k1 operations. Its two independent policy callbacks and secret-holding dealer stand in for the two ideal release interfaces. The test chooses two marker outpoints after setup, computes both real reserve-input sighashes, verifies each native signature, executes the reserve tapscript, checks byte-identical repeat openings and covers odd parity and malformed openings. It does not validate Syscoin history or execute the marker input. The group operations are research fixture code, including variable-time arithmetic inside the dealer. [Tests](frontend/guardednonce/fixture_test.go)

The [two-signer test](frontend/guardednonce/composition_test.go) computes the exact tapscript digest for a two-key reserve and checks both signatures in Bitcoin's script engine. Each independent fixture gets the same message for that script. Replacing the leaf with a different signer set would change the message.

## Mapping the two phases to masked packets

The new signer only requires affine evaluations of private scalars at public bits. Stage A uses the 256 bits of the two digest halves. Two independently masked packet totals return the scalars $B$ and $Z$. Stage B uses 512 bits comprising the same halves and the canonical scalar $\sigma e\bmod n$. Its independently masked total is $k(v)+(\sigma e)x$. Multiplication by the public sign $\sigma$ gives $s$. The release policy must bind every descriptor bit, including parity and the native challenge, to its authorized Pay. Domain-separate both phases and generate fresh masking constants and slopes for every scalar channel.

In the earlier recursive XOR layout, a 256-bit input uses 6,305 gates and 6,561 wires. The 512-bit input uses 19,171 gates and 19,683 wires. Stage A can carry its two independently masked scalars in one packet encrypted under the three required wire-state labels. This gives 52,488 logical wire-state labels across the phases. At three scratch coordinates per label and the illustrative 21,536 bytes per column, the added columns alone project to **3,391,144,704 bytes (3.16 GiB)**. The wrapped gate payloads add 4,067,968 raw bytes before envelope overhead. This is one candidate layout and a conditional accounting exercise. It excludes the source verifier, constraints, QAP powers, metadata and setup transcripts. The new signer has no secure single-table archive size or runtime measurement.

## What the public archive must prove

A single fixed-message Praxis ciphertext gives the same plaintext to every valid witness. For a two-stage signer, the archive must supply different eligible values while concealing the others. The existing shared-table fixture wraps packets under particular search-coefficient triples. The actual evaluator has the full pairing table, scratch toggles, search equations, ciphertexts and the public checks for all previous openings. A real proof must cover this entire joint view and malicious setup participants' information.

Praxis Lemma B.6 gives one partial result. A usable stack of total row-space dimension at most three and with no hash-kernel vector decomposes into honest witness stacks. A nonzero column on a target scratch bit then implies at least one witness whose target bit is set. The conclusion needs **total** dimension at most three. A high-dimensional global stack may have low dimension on the closed target's three coordinates, and the stock fixed-message extraction theorem can return a previously authorized witness. This leaves an unproved case for the shared table. Generating a new table or adding extra scratch coordinates requires a new argument about those actual public factors. [Praxis, Theorem 5.9 and Lemma B.6](https://arxiv.org/pdf/2611.28552)

There is a useful lower bound for a more limited fallback. Suppose a public assembler needs only the payout descriptor and the fixed plaintexts enabled for it. To resist pooling any two eligible descriptors, no third descriptor's enabled set can be contained in the union of theirs. Consequently the empty set, the individual sets, and each unordered pair union must all be distinct (for at least three possible descriptors). With $M$ descriptors and $L$ Boolean releases,

$$
2^L\ge 1+M+\binom{M}{2}.
$$

For all $2^{256}$ digest strings this implies at least 512 **logical** releases. The counting assumes universal set-based confinement. It says nothing about the physical size of a shared algebraic encoding, about policies with fewer admissible messages, or about an assembler that needs additional witness-dependent secrets.

One candidate interface for sharing the verifier is an extractable witness pseudorandom function. Its input names a reserve, input role, wire and requested state. A witness authenticates a complete Pay that selects that state. Every qualifying witness would derive the same pad for that particular label, so the armer could publish the wrapped labels once. This requires security for an adaptively targeted label given the other opened labels and all correlated wraps. The published witness-PRF work identifies the primitive. The published stock Praxis construction establishes a different interface. [Witness PRFs](https://eprint.iacr.org/2014/301) · [Extractable witness PRFs](https://eprint.iacr.org/2014/310)

A complete reserve design still needs a concrete two-stage selective-release proof, verifiable arming tolerating up to $N-1$ corrupt participants with abort, and a future eligibility relation authenticating the NEVM receipt, AuxPoW ancestry, Close, fee policy and both transaction roles. The ideal cap counts positive openings on private histories even when Bitcoin accepts neither Pay. A 100-block delay alone cannot enforce that cap. The 2.09 MB measurement in [the single-table experiment](SHARED_PAY.md#size) belongs to the pinned one-message fixture. A secure two-stage archive has no measured size here.
