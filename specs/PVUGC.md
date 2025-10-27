**Title:** PVUGC — **Proof-Agnostic Verifiable Unique Group Commitments** gated by witness‑encrypted adaptor signatures on Bitcoin.
**License:** CC‑BY 4.0

### Abstract

PVUGC turns **proof existence** for a fixed verification key $\mathsf{vk}$ and public input $x$ into the **ability to complete a Taproot signature** for a pre‑templated transaction. We pre‑arm a Schnorr adaptor signature whose missing scalar $\alpha$ is **witness‑encrypted** under the statement "Groth16 verifies $(\mathsf{vk},x)$" via a **Groth–Sahai (GS)** attestation. Any valid proof yields the same KEM key, enabling decryption of $\alpha$ and completion of the spend. Without a valid proof, the transaction cannot be signed. The approach requires **no new opcodes** and keeps on‑chain script minimal (`OP_CHECKSIG`, optional `OP_CHECKSEQUENCEVERIFY`). It is **use case-agnostic** and applies to any computation compiled to Groth16.

---

### 0) Intuition

* **Goal.** Keep Bitcoin on‑chain tiny (Taproot OP_CHECKSIG ± OP_CHECKSEQUENCEVERIFY) and enforce *off‑chain truth* for a relation $R_{\mathcal{L}}$.
* **How.** Pre‑arm a Schnorr adaptor signature for an exact `SIGHASH_ALL` digest; the finishing scalar $\alpha$ is witness‑encrypted. If and only if a valid proof exists for $(\mathsf{vk},x)$, any party can derive the same KEM key from the GS attestation, decrypt $\alpha$, and finish the signature.
* **Why not "just a SNARK."** Bitcoin still requires a valid Schnorr signature; we transform **proof existence** into the **secret that completes** that Schnorr signature.
* **Why practical.** The **Product‑Key KEM** encrypts to the *verification product* of the GS check, yielding a **proof‑agnostic, instance-deterministic** key: *every* valid attestation for fixed $(\mathsf{vk},x)$ induces the same product in $\mathbb{G}_T$, avoiding pairing inversion and timing paradoxes.
**Key Innovation:** A Product‑Key KEM that maps proof *existence* (not specific witness values) to a deterministic decryption key. This is the first practical WE-backed Taproot adaptor (prove-to-sign) on Bitcoin.

---

### 1) Model & Language

* **Language $\mathcal{L}$.** Fix an NP relation $R_{\mathcal{L}}(x,w)=1$. Examples: VM execution traces, hash‑preimage statements, "state transition" checks, zk‑rollup validity, etc.
* **Gating predicate.** "There exists a Groth16 proof $\pi$ that verifies for $(\mathsf{vk},x)$."
* **Spend semantics.** The Taproot spend **succeeds iff** the gating predicate is true (i.e., the $\alpha$ needed for the adaptor is recoverable).
* **Optimistic flavor.** You can add an **optional Timeout/Abort** path (timelock) or an **optional Opposite‑Predicate path** (gate a *different* computation) depending on your application. None of this is *required* by the core innovation.

---

### 2) Bitcoin script (generic template)

Two Taproot script leaves (key‑path disabled by NUMS‑style internal key):

```
ComputeSpend : <P_compute> OP_CHECKSIG

Timeout/Abort (optional) :
    <Δ> OP_CHECKSEQUENCEVERIFY OP_DROP
    <P_abort> OP_CHECKSIG
```

* **ComputeSpend** is the path whose adaptor signature is witness‑encrypted under $(\mathsf{vk},x)$.
* **Timeout/Abort** is optional: a plain timelock or a different WE‑gated policy.
* **Key‑path**: internal key is a public point with unknown discrete log (NUMS) so only script‑path is usable (a social burn of the key path). Derive deterministically (cycle‑free), using IETF hash‑to‑curve (simplified‑SWU) for secp256k1 with domain tag `"PVUGC/NUMS"` and canonical encodings:

```
Q_nums <- hash_to_curve("PVUGC/NUMS" || vk_hash || H(x) || tapleaf_hash || tapleaf_version || epoch_nonce)
internal_key = xonly_even_y(Q_nums)
```
* **Transaction binding**: all signatures use `SIGHASH_ALL`, bind tapleaf hash **and version**, **annex absent** (BIP‑341 `annex_present = 0`), and include a **small P2TR CPFP hook** output.
* **CPFP hook.** A small P2TR output in a fixed position to allow fee bumping via child‑pays‑for‑parent; changing its value or position invalidates $m$.

---

### 3) Context binding (layered `ctx_hash`)

Use layered hashes to bind the environment without cycles. Transcripts bind to `ctx_hash`, but are not included in these package hashes:

```
y_cols_digest   = H_bytes("PVUGC/YCOLS" || ser([β]_2) || ser(b_g2_query[0]) || ...)
epoch_nonce     = CSPRNG(32 bytes)  // unique per instance
ctx_core        = H_bytes("PVUGC/CTX_CORE" || vk_hash || H_bytes(x) || tapleaf_hash || tapleaf_version || txid_template || path_tag || y_cols_digest || epoch_nonce)
arming_pkg_hash = H_bytes("PVUGC/ARM"      || {D_j} || D_δ || header_meta)
presig_pkg_hash = H_bytes("PVUGC/PRESIG"   || m || T || R || signer_set || musig_coeffs)
ctx_hash        = H_bytes("PVUGC/CTX"      || ctx_core || arming_pkg_hash || presig_pkg_hash || dlrep_transcripts)
```

- `path_tag ∈ {compute, abort}` (or others if you add more paths).
- Include exact output ordering, CPFP hook position, and any deployment/epoch identifiers you need.
- Bind PoK/PoCE and `AdaptorVerify(m,T,R,s′)` to `ctx_hash`. Do not include those transcripts inside the package hashes above.

**Message (m).** $m$ is the 32‑byte BIP‑341 script‑path `sighash` for the pre‑templated transaction, computed with `SIGHASH_ALL`, `annex_present=0`, and binding the exact tapleaf hash and leaf version for this path.

**`txid_template`.** A fully specified transaction template (inputs/outputs/locktime/sequence/fees) used only to define $m$. It does not include any signatures or annex. Any change to `txid_template` changes $m$ and hence `presig_pkg_hash` and `ctx_hash`. `txid_template` MUST NOT reference unknown txids (no forward/self‑references). The CPFP child is outside `ctx_hash`; only the CPFP output (scriptPubKey, index, value) is fixed in `ctx_core`.

**`header_meta`.** A deterministic serialization hash of the public KEM header: share index $i$, $\{D_j\}_{j=0}^{n_B-1}$, $D_\delta$, $T_i$, $h_i$, $\texttt{ct}_i$, $\tau_i$, $\rho\_\text{link}$, `DEM_PROFILE`, `GS_instance_digest`, exact ordering of $Y_j$ column bases. Use strict encodings and reject duplicates.

**Hash functions (normative).**

Let `H_bytes = SHA-256` for byte-level context hashes (`ctx_*`) and tags like `H(x)`. Let `H_p2 = Poseidon2` for KDF/DEM/tag and in-circuit PoCE. Define `H_tag = Poseidon2` domain-tagged as "PVUGC/RHO_LINK"; set `ρ_link = H_tag(ser(ρ_i))`. All hashes MUST be domain‑separated with ASCII tags.

**epoch_nonce (normative).** A 256-bit value sampled from OS CSPRNG (`getrandom`, `getentropy`, or `BCryptGenRandom`) that MUST be unique per protocol instance. Implementations MUST reject nonce reuse and verify all participants agree on the same value before arming. Include in `ctx_core`, NUMS derivation (line 46), and transaction metadata for verification.

**Context/domain tags (normative).**

* `"PVUGC/CTX_CORE"`, `"PVUGC/ARM"`, `"PVUGC/PRESIG"`, `"PVUGC/CTX"` (inputs to H_bytes)
* `"PVUGC/KEM/v1"` (profile tag)
* `"PVUGC/AEAD-NONCE"` (reserved; not used in Poseidon2 profile)
* `"BIP0340/challenge"` (BIP‑340 tagged hash)

**MUST (Span independence in $\mathbb{G}_T$).** The target $R(\mathsf{vk},x) \in \mathbb{G}_T$ MUST be derived deterministically from ($\mathsf{vk}$,$x$) alone. Implementations MUST freeze ($\mathsf{vk}$,$x$) before arming and pin their digests in `GS_instance_digest`. Arming participants MUST have no influence over these derivations. Intuitively, $R(\mathsf{vk},x)$ MUST NOT lie in the public pairing span of $\{Y_j, [\delta]_2\}$ without the committed G₁ variables.

**Production Profile (MUST/SHOULD).**

* **MUST:** BLS12‑381 as the pairing curve family.
* **MUST:** DEM_PROFILE = "PVUGC/DEM-P2-v1" (SNARK‑friendly). KDF(M) = Poseidon2( ser_GT(M) || H_bytes(ctx_hash) || GS_instance_digest ); DEM keystream = Poseidon2(K_i, AD_core); ct = pt ⊕ keystream; τ = Poseidon2(K_i, AD_core, ct). Mixing profiles within a `ctx_hash` is forbidden.
* **SHOULD:** For enhanced security, implementations MAY verify multiple independent PPE formulations (logical AND). For AND‑of‑2, define $M_i^{\text{AND}} := \mathrm{ser}_{\mathbb{G}_T}(M_i^{(1)}) || \mathrm{ser}_{\mathbb{G}_T}(M_i^{(2)})$ and derive $K_i = \text{Poseidon2}( M_i^{\text{AND}} || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest} )$.
* **SHOULD:** Enable Timeout/Abort with $\Delta$ chosen to cover proving+network latency.

---

### 4) Keys & one‑time pre‑sign per path (MuSig2)

For each path that will be WE‑gated (at minimum **ComputeSpend**):

* Run MuSig2 (BIP‑327) once to produce a pre‑signature $s'$ with **unique** session nonce $R$ and **unique** adaptor point $T$.
* **Compartmentalization (MUST):** one adaptor ⇒ one unique $T$ and one unique $R$. Never reuse across paths/epochs or templates.
* **Nonce generation (MUST - BIP‑327):** Each signer MUST generate fresh random nonces $k_{1,i}, k_{2,i}$ per session using a cryptographically secure random number generator. Nonces MUST NOT be fully deterministic from `secret_key` alone (prevents co-signer prediction attacks per BIP‑327 §NonceGen). Implementations SHOULD mix in session-specific data (`secret_key`, aggregate pubkey, message, `ctx_hash`) for defense-in-depth against RNG state repetition.
* **Nonce reuse prevention (MUST):** Implementations MUST maintain a blacklist of aggregate nonce values $R$ and reject any reuse before signing. This provides operational protection against RNG or state management failures.
* Publish an `AdaptorVerify(m,T,R,s′)` transcript **bound to** `ctx_hash`, the signer set, their MuSig coefficients, and the exact `txid_template`.

---

### 5) Distributed setting of (T = $\alpha$·G) (k‑of‑k, public PoK + PoCE)

Each of the $k$ arming participants picks an **adaptor share** $s_i \in \mathbb{Z}_n$, publishes $T_i=s_i G$ with a **Schnorr PoK** of knowledge of $s_i$, and a **PoCE** tying their WE ciphertext to the same randomness used for their mask vector (see §6 and §8). Set:

$$
T = \sum_{i=1}^k T_i \quad\text{and}\quad \alpha = \sum_{i=1}^k s_i
$$

**Arm‑time rule:** verify **all** PoK and PoCE before any pre‑signing; abort on any failure. Never reuse any $s_i$ (or $\alpha$) across contexts.

It publicly proves that the published masks $\{D_\ell\}$ and $\{D_a\}$ were made with the same $\rho_i$, and that $T_i$ matches $s_i$. The ciphertext $\texttt{ct}_i$ is key‑committed at decapsulation time via PoCE‑B. Without PoCE an armer could publish structurally valid but semantically wrong artifacts, undermining decrypt‑on‑proof soundness.

---

### 5.1) KEM Randomness Commitment (Fairness Protection)

To prevent collusive randomness cancellation ($\prod \rho_i = 1$), use three-phase commit-reveal: (1) Each armer publishes $\text{comm}_i = \text{SHA256}(\text{"PVUGC\_RHO\_COMMIT/v1"} \parallel \text{ser}_{\mathbb{F}_r}(\rho_i) \parallel \text{salt}_i)$ before any revelation; (2) After all commitments collected, reveal $(\rho_i, \text{salt}_i)$ with arming packages; (3) Verify commitment match before accepting, abort on mismatch. Prevents adaptive coordination enabling griefing and grinding attacks.

---

### 6) WE via Product‑Key KEM (GS‑attested Groth16‑verify)

**The Challenge:** Standard Groth16 verification has proof elements on both sides of pairings:
$$
e(\pi_A,\pi_B) \cdot e(\pi_C,[\delta]_2) = e([\alpha]_1,[\beta]_2) \cdot e\left(\sum_i x_i [l_i]_1,[\gamma]_2\right) \tag{G16}
$$
where $(\pi_A, \pi_C) \in \mathbb{G}_1$ and $\pi_B \in \mathbb{G}_2$. Direct witness encryption would require pairing inversion (computationally infeasible).

**Solution: One-Sided GS Attestation Layer.** We prove (with Groth–Sahai) that (G16) holds using a one-sided commitment structure. Define the target:
$$
R(\mathsf{vk},x) = e([\alpha]_1,[\beta]_2) \cdot e\left(\sum_i x_i [l_i]_1,[\gamma]_2\right) \in \mathbb{G}_T
$$

The prover forms G₁ variables from its internal coefficients:
- **B-side variables**: 
  - $X^{(B)}_0 = 1 \cdot A$ (constant for $\beta$ column)
  - $X^{(B)}_{j+1} = b_j \cdot A$ for $j \in [0, m-1]$ where $b_j$ are coefficients from b_g2_query
- **$\delta$-side variables**:
  - $X^{(B)}_\delta = s \cdot A$ (the randomness $s$ from B)
  - $C$ (the Groth16 proof element, paired with $[\delta]_2$)

**Y-basis content (normative):** The $Y_j$ list for B includes:
- $Y_0 = [\beta]_2$ (first element, constant column)
- $Y_{j+1} = \text{b\_g2\_query}[j]$ for all $j$ the prover uses in B

Do not deduplicate - $e(A, [\beta]_2)$ must be reconstructed on the B side of the PPE.

**Column-based arming:** Directly arm each statement-only column:
$$
\{D_j = Y_j^\rho\}_{j=0}^{n_B-1}, \quad D_\delta = [\delta]_2^\rho
$$
Column mode directly arms each base without aggregation matrices.

The GS verifier checks the **one-sided product‑of‑pairings equation**:
$$
\prod_{j=0}^{n_B-1} e(X^{(B)}_j, Y_j) \cdot e(X^{(B)}_\delta, [\delta]_2) \cdot e(C, [\delta]_2) = R(\mathsf{vk},x) \tag{GS-PPE}
$$

where:
- $X^{(B)}_0 = 1 \cdot A$ (for the $\beta$ column)
- $X^{(B)}_{j+1} = b_j \cdot A$ (for b_g2_query coefficients)
- $X^{(B)}_\delta = s \cdot A$ (separate $\delta$ column for the $s$ randomness)
- $C$ is the Groth16 proof element (not negated)

**Critical property**: The $Y_j$ and $[\delta]_2$ are **statement‑only** (depend only on VK and $x$, not on the proof). For *every* valid attestation and fixed $(\mathsf{vk},x)$, the product equals the **same** $R(\mathsf{vk},x)$.

**Binding to Groth16 Proof (DLREP proofs - MUST).** The prover MUST include succinct Schnorr-style proofs demonstrating:
- **DLREP_B (MUST)**: Proof in $\mathbb{G}_2$ that $B = \beta_2 + \sum_{j=0}^{m-1} b_j \cdot \text{b\_g2\_query}[j] + s \cdot [\delta]_2$ with:
  - Same-scalar ties: $X^{(B)}_0 = 1 \cdot A$, $X^{(B)}_{j+1} = b_j \cdot A$ for all $j$
  - $X^{(B)}_\delta = s \cdot A$ uses the same $s$ from B's $\delta_2$ term
- **DLREP_C (MUST)**: Proof in $\mathbb{G}_1$ that the committed $C$ is the actual Groth16 proof element

These DLREP transcripts MUST be bound into `ctx_hash`. The verifier accepts either "(Groth16 verify) OR (DLREPs + GS PPE)" as valid attestation.

**Profile parameter**: $N_{\max}$ (max allowed columns for this deployment; e.g., 32 or 48).

**MUST (Column profile):** If $n_B > N_{\max}$, reject under the Column profile and use the **Outer-Compressed profile** (tiny outer verifier + rank-1 PPE), documented separately. Typical column-based encodings require 16-32 pairings.

**GS attestation size bounds (MUST - DoS prevention):** Implementations MUST reject GS attestations where the total number of pairings exceeds 96. Specifically, if $m_1$ is the number of G₁ commitments and $m_2$ is the number of G₂ commitments, then MUST enforce: $m_1 + m_2 \leq 96$. This prevents denial-of-service attacks via oversized attestations while allowing typical Groth16→GS encodings (20-40 pairings). For BLS12-381, 96 pairings requires ~50-100ms verification time on modern hardware - acceptable for one-time decapsulation.

**Independence (MUST).** The statement-only bases $\{Y_j\}$ and $[\delta]_2$, along with the target $R(\mathsf{vk},x)$, are fixed by ($\mathsf{vk}$, $x$) before any armer chooses randomness. The bases are derived directly from the verifying key components. Armers cannot choose or influence these bases.
**Implementation MUST NOT** allow armers to influence $\mathsf{vk}$ or $x$ once arming begins; these are fixed before any $\rho_i$ is chosen.

**γ₂ exclusion enforcement (MUST).** The armed G₂ bases $\{Y_j = [\beta]_2, \text{b\_g2\_query}\}$ and $[\delta]_2$ deliberately exclude $[\gamma]_2$. Implementations MUST derive $Y_j$ from the verifying key's $\{\beta_2, \text{b\_g2\_query}\}$ components only. $[\gamma]_2$ MUST NOT be included in any armed base. This structural exclusion ensures:
- **Algebraic independence:** $R(\mathsf{vk},x) = e(\alpha_1,\beta_2) \cdot e(L(x),\gamma_2)$ cannot be computed from armed bases alone, as the second factor requires $[\gamma]_2^\rho$ (never published).
- **Standard hardness:** Computing $R(\mathsf{vk},x)^\rho$ from $\{Y_j^\rho, [\delta]_2^\rho\}$ reduces to discrete logarithm in $\mathbb{G}_2$ or $\mathbb{G}_T$, not a novel assumption.

**Encapsulation (arm‑time, per share $i$).** Choose $\rho_i \in \mathbb{Z}_r^*$ (where $r = \#\mathbb{G}_1 = \#\mathbb{G}_2 = \#\mathbb{G}_T$, non-zero). Compute:
$$
D_j=Y_j^{\rho_i}\in \mathbb{G}_2 \text{ for } j \in [1,n_B], \quad D_\delta=[\delta]_2^{\rho_i}\in \mathbb{G}_2, \quad M_i=R(\mathsf{vk},x)^{\rho_i}\in \mathbb{G}_T \text{ (do NOT publish)}
$$
$$
K_i=\mathrm{Poseidon2}(\mathrm{ser}_{\mathbb{G}_T}(M_i) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest})
$$
Encrypt $\texttt{enc}_i=(s_i \| h_i)$ with a **key‑committing DEM** (see §8) to get $(\texttt{ct}_i,\tau_i)$.

**Publish only:** $\{D_j\}_{j=0}^{n_B-1}$, $D_\delta$, $\texttt{ct}_i$, $\tau_i$, $T_i$, $h_i$, plus PoK and **PoCE-A** (algebraic proof).
**Keep secret:** $M_i$ (derivable only with valid attestation).

**Degenerate & subgroup guards:** Abort arming if $R(\mathsf{vk}, x) = 1$ (identity in $\mathbb{G}_T$) or if it lies in any proper subgroup of $\mathbb{G}_T$. While negligible for honest setups, these checks prevent trivial keys. PoCE MUST also assert $R(\mathsf{vk},x) \neq 1$ via a public input bit tied to `GS_instance_digest`.
**Serialization (MUST):** Use a canonical, subgroup‑checked encoding $\mathrm{ser}_{\mathbb{G}_T}(\cdot)$ for KDF input; reject non‑canonical encodings.
**Group model.** $\mathbb{G}_1,\mathbb{G}_2,\mathbb{G}_T$ are prime‑order groups of order $r$. Implementations MUST perform subgroup checks using library‑provided tests (and cofactor clearing where applicable) and reject non‑canonical encodings.

**Decapsulation (anyone with a valid attestation).**
Verify GS attestation and DLREP proofs, then compute
$$
\tilde{M}_i = \left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j,D_j)\right) \cdot e(X^{(B)}_\delta, D_\delta) \cdot e(C,D_\delta) = R(\mathsf{vk},x)^{\rho_i} = M_i
$$
derive $K_i'=\mathrm{Poseidon2}(\mathrm{ser}_{\mathbb{G}_T}(\tilde{M}_i) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest})$, decrypt $\texttt{ct}_i\to(s_i \| h_i)$, check $T_i=s_iG$, $H_\text{bytes}(s_i \| T_i \| i)=h_i$, and verify PoCE-B. Sum $\alpha=\sum_i s_i$ and finish the adaptor $s=s'+\alpha \bmod n$.

**Proof‑agnostic key (the critical insight).** For any two valid GS attestations $\mathsf{Att}_1, \mathsf{Att}_2$ for the same $(\mathsf{vk},x)$, the one-sided product equals the same fixed value:
$$
\left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j(\mathsf{Att}_1), Y_j)\right) \cdot e(X^{(B)}_\delta(\mathsf{Att}_1), [\delta]_2) \cdot e(C(\mathsf{Att}_1), [\delta]_2) = R(\mathsf{vk},x)
$$
$$
\left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j(\mathsf{Att}_2), Y_j)\right) \cdot e(X^{(B)}_\delta(\mathsf{Att}_2), [\delta]_2) \cdot e(C(\mathsf{Att}_2), [\delta]_2) = R(\mathsf{vk},x)
$$
Therefore, for any valid attestation:
$$
\tilde{M}_i = \left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j, D_j)\right) \cdot e(X^{(B)}_\delta, D_\delta) \cdot e(C, D_\delta) = R(\mathsf{vk},x)^{\rho_i}
$$

This means *every* valid attestation yields the **same** KEM key $K_i$, regardless of which proof was used.

### 5.1) PoCE-A: Proof of Correct Exponentiation (Arm-time)

**Purpose:** Prove that all armed columns share the same $\rho_i$ and that the published ciphertext is key-committed to the derived KEM key.

**Security rationale:** Without PoCE-A, an armer could publish mixed-$\rho$ arms (some $Y_j^{\rho_1}$, some $Y_k^{\rho_2}$) which would break decapsulation, or publish a ciphertext not bound to the actual derived key.

**Construction:** Multi-base Schnorr proof proving:
- $\forall j: D_j = Y_j^{\rho_i}$ (all columns share same $\rho_i$)
- $D_\delta = [\delta]_2^{\rho_i}$ (delta arm shares same $\rho_i$)
- $T_i = s_i G$ (Schnorr proof for $s_i$)
- Key-commitment: ciphertext is bound to $K_i = \mathrm{Poseidon2}(\mathrm{ser}(M_i) || \texttt{ctx\_hash} || \texttt{GS\_instance\_digest})$

**Verification:** Accept arming only if PoCE-A verification passes.

### 5.2) PoCE-B: Proof of Correct Exponentiation (Decap-time)

**Purpose:** Decapper-local key-commitment verification to detect tampered ciphertexts.

**Construction:** Recompute $K_i'$ from derived $\tilde{M}_i$ and verify the commitment tag $\tau_i$.

**Verification:** Accept decapsulation only if PoCE-B verification passes.

---

### 7) Correctness & Determinism (Key Lemmas)

**Lemma 1 (GS product determinism, one-sided).** For fixed $(\mathsf{vk},x)$, any accepting GS attestation $\mathsf{Att}$ with valid DLREP proofs for the statement "Groth16 verifies $(\mathsf{vk},x)$" yields
$$
\left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j(\mathsf{Att}),Y_j)\right) \cdot e(X^{(B)}_\delta(\mathsf{Att}), [\delta]_2) \cdot e(C(\mathsf{Att}), [\delta]_2) = R(\mathsf{vk},x) \in \mathbb{G}_T
$$
where $Y_j$, $[\delta]_2$ are **statement-only** bases derived from VK components and $R(\mathsf{vk},x) = e([\alpha]_1,[\beta]_2) \cdot e(\sum_i x_i[l_i]_1,[\gamma]_2)$. The value is **independent of prover randomization** because the randomness in commitments cancels through the pairing structure, and the DLREP proofs ensure consistency with the underlying Groth16 proof.

**Lemma 2 (KEM correctness).** For share $i$ with randomness $\rho_i$, the published masks $D_j = Y_j^{\rho_i}$, $D_\delta = [\delta]_2^{\rho_i}$ and any accepting attestation give
$$
\tilde{M}_i = \left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j,D_j)\right) \cdot e(X^{(B)}_\delta, D_\delta) \cdot e(C,D_\delta) = R(\mathsf{vk},x)^{\rho_i} = M_i
$$
Hence $K_i' = \mathrm{Poseidon2}(\mathrm{ser}_{\mathbb{G}_T}(\tilde{M}_i) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest}) = K_i$, and the DEM decrypts $(s_i \| h_i)$.

**Lemma 3 (No‑Proof‑Spend).** Under the following assumption, given only $\{D_j = Y_j^{\rho_i}\}$ and $D_\delta = [\delta]_2^{\rho_i}$ (where $Y_j, [\delta]_2 \in \mathbb{G}_2$) and public parameters, computing $M_i = R(\mathsf{vk},x)^{\rho_i} \in \mathbb{G}_T$ without an accepting attestation is infeasible. Thus $\alpha = \sum_i s_i$ remains hidden and the adaptor cannot be finalized.

> Assumption (GT‑XPDH: External Power in $\mathbb{G}_T$). Let $e:\mathbb{G}_1\times\mathbb{G}_2\to\mathbb{G}_T$ be a non‑degenerate bilinear map over prime‑order groups of order $r$. Sample statement-only base sets $\{Y_j\}, [\delta]_2 \subset\mathbb{G}_2$, an unknown exponent $\rho\leftarrow\mathbb{Z}_r^*$, and the target $R\leftarrow\mathbb{G}_T$. Given $(\{Y_j\},[\delta]_2,\{Y_j^{\rho}\},[\delta]_2^{\rho},R)$, it is hard for any PPT adversary to compute $R^{\rho}$ without valid commitments. In our instantiation, $R=R(\mathsf{vk},x)$ is fixed by ($\mathsf{vk}$,$x$) and independent of the randomness; DLREP soundness prevents producing commitments without knowledge of a valid Groth16 proof.

Generic‑group note. In the bilinear generic/algebraic group model, an adversary with $q$ group/pairing operations has advantage at most $\tilde{O}(q^2/r)$ to compute $R^{\rho}$ when $R$ is independent, since available handles are confined to pairing images of $\{Y_j^{\rho}\},[\delta]_2^{\rho}$ and do not link to $R$. Multi‑instance ($q_\text{inst}$ contexts) is captured by the standard union bound (aka $q$‑GT‑XPDH).

*Proof sketches:* (i) follows from DLREP soundness + randomness cancellation in PPE; (ii) is algebraic as written; (iii) from KEM hardness and Schnorr UF-CMA.

**Transparent CRS:** Groth–Sahai commitments use a **binding CRS (two G₁ bases)** which we derive deterministically via hash-to-curve from the VK/ctx. No trapdoor or ceremony is required. The G₂ right-legs $\{Y_j\}, [\delta]_2$ and the target $R(\mathsf{vk},x)$ are **statement-only and CRS-independent**, derived directly from the Groth16 verifying key components and public inputs. Column-based arming directly arms each statement-only column without matrix aggregation. 
**SHOULD:** To mitigate potential weaknesses, implementations MAY use multiple independent arming approaches and verify all resulting PPEs (logical AND).

**Knowledge‑soundness (SHOULD).** The GS attestation SHOULD be knowledge‑sound for the relation “there exists a Groth16 proof $\pi$ such that $\textsf{Verify}_{\text{G16}}(\mathsf{vk},x,\pi)=1$.” That is, there exists an extractor that, given any accepting GS attestation, outputs a valid Groth16 proof $\pi$ for $(\mathsf{vk},x)$. Plain soundness suffices for correctness/no‑proof‑spend; knowledge‑soundness is a stronger deployment profile.

---

### 8) PoCE and DEM details (normative)

**PoCE (Two-stage verification):**

**PoCE-A (Arm-time verifiable encryption & mask-link, SNARK-friendly).** A NIZK proving, for share $i$:
* Knowledge of $(\rho_i,s_i,h_i)$ s.t. (i) $D_j=Y_j^{\rho_i}$ for all $j \in [0,n_B-1]$, $D_\delta=[\delta]_2^{\rho_i}$; (ii) $T_i=s_iG$; (iii) $\rho\_\text{link}=H_\text{tag}(\rho_i)$.
* Key derivation (in-circuit): $K_i = \mathrm{Poseidon2}(\mathrm{ser}_{\mathbb{G}_T}(R(\mathsf{vk},x)^{\rho_i}) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest})$.
* DEM correctness (SNARK-friendly): $\texttt{ct}_i = (s_i\|h_i) \oplus \mathrm{Poseidon2}(K_i, \text{AD\_core})$ and $\tau_i = \mathrm{Poseidon2}(K_i, \text{AD\_core}, \texttt{ct}_i)$.
* $\rho_i\neq 0$ (via auxiliary $\rho_i\cdot u_i=1$)

**Implementation note (MUST):** PoCE-A MUST use per-column Schnorr commitments ($k_\rho\cdot U_\ell$, $k_\rho\cdot W_a$, $k_\rho\cdot [\delta]_2$) and verify each equal-exponent equation individually. Collapsing all columns into a single sum is insufficient and allows malformed arms that still satisfy the aggregated relation.

**Public arming checks (performed by coordinator/auditors):**
* **Per-share validation (MUST):** For each arming package $i$, verify $T_i \neq \mathcal{O}$ (point at infinity). This detects $s_i = 0$ early (before aggregation) and prevents griefing via invalid null shares.
* **Aggregated validation (MUST):** Compute $T = \sum T_i$ and reject if $T = \mathcal{O}$ (point at infinity). This prevents collusion where $\sum s_i = 0 \bmod n$ (which would make the pre-signature immediately valid without decryption).
* Enforce unique `share_index`; reject duplicates and maintain a replay set keyed by $(\texttt{ctx\_core}, \texttt{presig\_pkg\_hash}, \texttt{header\_meta})$. If the same `header_meta` appears under a different `presig_pkg_hash` for the same `ctx_core`, reject as a replay/misbind.
* Verify $R(\mathsf{vk},x) \neq 1$ (computable from $(\mathsf{vk},x)$ without proof)

**PoCE-B (Decap-time key-commitment check - decapper-local).** After deriving $\tilde{M}_i$ from valid attestation (key-commits the ciphertext to the derived key):
* Recompute $K_i' = \mathrm{Poseidon2}(\mathrm{ser}_{\mathbb{G}_T}(\tilde{M}_i) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest})$
* (P2) No AEAD nonce is used by the DEM; omit nonce.
* Decrypt $\texttt{ct}_i$ with $K_i'$ and verify $T_i = s_iG$ and $H(s_i \| T_i \| i) = h_i$
* Verify key-commit tag: $\tau_i = \mathrm{Poseidon2}(K_i', \text{AD\_core}, \texttt{ct}_i)$
* **Note:** This is a decapper-local check (not publicly verifiable unless plaintext revealed)
* **Shape check (MUST):** Before decryption, verify the lengths and ordering of $\{D_j\}$ and $D_\delta$ match `header_meta` exactly; mismatch ⇒ reject.

Ceremony rule (MUST): do not pre-sign unless all PoCE-A proofs and PoK verify for all shares.
* **Publication (SHOULD):** Implementations SHOULD publish a minimal PoCE‑B verification transcript (hashes of inputs/outputs) alongside the broadcasted spend to aid auditing, without revealing plaintext values.

**AD_core** binds: `PVUGC/WE/v1 || vk_hash || H_bytes(x) || ctx_hash || tapleaf_hash || tapleaf_version || txid_template || path_tag || share_index || T_i || T || {D_j} || D_\delta || GS_instance_digest`.

**Decapper requirement:** Upon decapsulation, reject if the tuple $(K_i, \text{AD\_core})$ repeats for the same published header/`ctx_core` (indicates encapsulation reuse).

**DEM (key‑committing):**

* **Hash‑only DEM (P2)**: $\texttt{ct}_i=(s_i \| h_i)\oplus \mathrm{Poseidon2}(K_i,\text{AD\_core})$, $\tau_i=\mathrm{Poseidon2}(K_i,\text{AD\_core},\texttt{ct}_i)$.
**Mandatory hygiene:** subgroup checks ($\mathbb{G}_1$, $\mathbb{G}_2$, $\mathbb{G}_T$), cofactor clearing, constant‑time pairings, constant‑time DEM decryption, strict encodings (reject non‑canonical), strict BIP‑340 canonical encodings for $R$ and $s$ (reject non‑canonical signatures), rejection sampling for derived scalars, fresh $\rho_i$, fresh $T$, fresh MuSig2 $R$.
**Why PoCE is needed:** Without PoCE-A, a malicious armer could publish masks/ciphertexts not derived from the same $\rho_i$, breaking decrypt-on-proof soundness.

---

### 9) Activation patterns (optimistic options, orthogonal to the core)

* **N‑of‑N arming.** All armers must publish valid $(T_i,\text{PoK},\text{PoCE},\texttt{ct}_i,\{D_\ell\},\{D_a\})$ before pre‑signing. No one learns $\alpha$.
* **1‑of‑N trigger.** After arming, **any** prover who can produce a valid Groth16+GS attestation can finish the spend by decapsulating $\alpha$ (permissionless).
* **Timeout/Abort path.** `CSV=Δ` path sending funds to a neutral sink or alternate policy. **RECOMMENDED** to mitigate griefing if malformed arming data passes PoK but breaks decryption. This is a liveness/UX mitigation.
* **Challenge path (optional).** If your application benefits from a *negative* predicate (e.g., "there exists a valid proof that $\neg R_{\mathcal{L}}$"), you may WE‑gate a separate script leaf under a different $(\mathsf{vk}',x')$. Not required by PVUGC itself.
**Takeaway:** The **only requirement** to understand the main innovation is the WE‑gated **ComputeSpend** path. Timeout/Abort/Challenge are **patterns**, not prerequisites.

---

### 10) Adaptor verification (normative)

Define the adaptor pre-signature check and binding:

$$
\text{AdaptorVerify}(m,T,R,s'): \quad s'G + T \stackrel{?}{=} R + cP
$$

Where:
- $c = \text{tagged\_hash}(\text{"BIP0340/challenge"}, R_x || P_x || m)$
- $R$ is normalized to even-$y$
- $R \neq \mathcal{O}$ (reject point at infinity)

Bind `AdaptorVerify` to `ctx_hash`, including the signer set and MuSig2 coefficients via `presig_pkg_hash` (see §3). One adaptor implies one unique $T$ and one unique $R$.

Use x‑only encodings for $R_x$ and $P_x$; $R$ MUST be normalized to even‑$y$ at pre‑sign time per BIP‑340. Witnesses with `annex_present=1` MUST be rejected.
**Key aggregation binding.** `presig_pkg_hash` MUST include the key list $L=(X_1,\dots,X_k)$ and the per‑key coefficients $a_i=\textsf{KeyAggCoeff}(L,X_i)$ as actually used by MuSig2 for $P=\sum a_i X_i$.

---

### 11) Security Analysis

**Security Games (Formal Properties):**

| **Game** | **Definition** | **Holds By** |
|----------|---------------|--------------|
| **Completeness** | Valid proof $\pi$ for $(\mathsf{vk},x)$ ⇒ spend finalizes correctly | GS soundness + KEM correctness (Lemma 2) |
| **No-Proof-Spend** | No valid attestation ⇒ negligible probability to finalize | GT‑XPDH + Schnorr UF-CMA (Lemma 3) |
| **Context-Binding** | Valid attestation for $(\mathsf{vk},x)$ cannot finalize different template/leaf/path | AD binding in `ctx_hash` |
| **Witness Privacy** | Decapsulation reveals only $\alpha = \sum s_i$, not witness $w$ | SNARK zero-knowledge |

**Security Sketch:**

* **No proof ⇒ no spend.** Without a valid attestation, an attacker knows $D_j = Y_j^{\rho}$ and $D_\delta = [\delta]_2^{\rho}$ (where $Y_j, [\delta]_2 \in \mathbb{G}_2$) but cannot compute $M_i = R(\mathsf{vk},x)^{\rho} \in \mathbb{G}_T$ without either:
  - A valid attestation (Groth16 proof + DLREP proofs)
  - Breaking GT‑XPDH: given $\{Y_j^{\rho}\},[\delta]_2^{\rho}$ and independent $R\in\mathbb{G}_T$, compute $R^{\rho}$.
  Since $M_i$ is required to derive $K_i$ and decrypt $\alpha$, the adaptor cannot be finished.
**Independence.** $R(\mathsf{vk},x)$ is fixed by ($\mathsf{vk}$,$x$) and independent of the published bases $\{Y_j\},[\delta]_2$ and their $\rho$‑powers. DLREP soundness prevents crafting commitments that correlate $R(\mathsf{vk},x)$ with the published masks.
* **Proof ⇒ spend (right context).** DLREP soundness + PPE verification ⇒ any verifying attestation enforces the *same* product $R(\mathsf{vk},x)$; AD/`ctx_hash` bind $(\mathsf{vk},x)$, tapleaf(+version), tx template, path tag, $T_i$, $T$, and the mask vector.
* **Arming integrity.** Schnorr PoK ties $T_i$ to $s_i$; **PoCE‑A** proves one $\rho_i$ for both mask vectors and that $T_i$ corresponds to $s_i$; **PoCE‑B** key‑commits the ciphertext to the derived key and AD.
* **Compartmentalization.** Unique $T$ and MuSig2 $R$ per adaptor eliminate cross‑protocol nonce reuse and Wagner‑style collisions.
* **On‑chain minimalism.** Bitcoin validates a standard Taproot Schnorr signature; any break implies forging Schnorr or breaking pairings/GS/Groth16/DEM assumptions.

**Post‑spend learnability.** Given on‑chain $s$ and published $s'$, $\alpha=s-s' \pmod n$ becomes public (by design). This does not harm prior confidentiality.

---

### 12) Engineering checklist

* **Script:** script‑path only; NUMS internal key; leaves for ComputeSpend (and optional Timeout/Abort).
* **SIGHASH:** `SIGHASH_ALL`; annex absent (BIP‑341 `annex_present = 0`); bind tapleaf hash **and version**; pin exact output order and CPFP anchor.
* **MuSig2:** BIP‑327 two‑point nonces with fresh CSPRNG randomness per session (NOT deterministic from secret_key alone); mix in session data for defense-in-depth; maintain R blacklist; normalize $R$ to even y; erase secnonces; publish `AdaptorVerify(m,T,R,s′)` bound to `ctx_hash`.
* **Adaptor compartmentalization:** one adaptor ⇒ one $T$, one $R$; fresh per path/template/epoch.
* **ρ commit-reveal (MUST):** Phase 1: collect all commitments $\text{comm}_i = \text{SHA256}(\text{"PVUGC\_RHO\_COMMIT/v1"} \parallel \rho_i \parallel \text{salt}_i)$; Phase 2: reveal $(\rho_i, \text{salt}_i)$ with arming; Phase 3: verify commitment match before accepting arming package.
* **KEM/DEM:** constant‑time pairings; subgroup checks (verify $R(\mathsf{vk},x) \neq 1$, prime-order only); $\rho_i\neq 0$; canonical $\mathrm{ser}_{\mathbb{G}_T}$; GS size limit ($m_1 + m_2 \leq 96$); nonce‑free, key‑committing DEM (Poseidon2); reject non‑canonical encodings.
* **k‑of‑k arming:** verify all PoK + PoCE + ciphertexts + ρ commitments before pre‑sign; check per-share $T_i \neq \mathcal{O}$ and aggregated $T \neq \mathcal{O}$; abort on any mismatch.
* **Artifacts to publish:** $\{D_j\}_{j=0}^{n_B-1}$, $D_\delta$, $(\texttt{ct}_i,\tau_i)$, $(T_i,h_i)$, PoK, PoCE-A, DLREP transcripts, GS attestation (commitments + proof), `AdaptorVerify`, and the hashes composing `ctx_hash`.
* **Side-channel protection:** Pairings, scalars, and DEM MUST be constant-time; avoid cache-tunable table leakage across different `ctx_hash` values.

---

### 13) Minimal example

**Language**: $R_{\mathcal{L}}$ = "SHA‑256(preimage) = $h$" expressed via a tiny Groth16 circuit.

* Fix $\mathsf{vk}$ for that circuit; set $x := h$.
* Build `ctx_hash` from $(\mathsf{vk\_hash}, H(x))$, your exact tapleaf(+version), and `txid_template`.
* Arm k‑of‑k: publish $\{D_j\}$, $D_\delta$, $(\texttt{ct}_i,\tau_i)$, $(T_i,h_i)$, PoK, PoCE-A; verify; pre‑sign $(m,T,R)\Rightarrow s'$.
* A holder of a valid $\pi$ + GS attestation computes $\tilde{M}_i$, derives $K_i$, decrypts each $\texttt{ct}_i\to s_i$, sums $\alpha$, and outputs the final signature $s=s'+\alpha \pmod n$. Broadcast the ComputeSpend transaction.

**Curve note.** For concreteness, implementers may target an asymmetric Type‑3 pairing (e.g., a BLS12 family). The spec is agnostic; choose libraries with constant‑time pairings and explicit subgroup checks.

---

### 14) Limitations & scope

* **Trusted setup for Groth16** ($\mathsf{vk}$ pinned to a public ceremony transcript).
* **Fixed circuit**: Changing $\mathsf{vk}$ or $x$ changes `ctx_hash` and requires re‑arming.
* **Proving cost**: Proof generation time dominates; WE/KEM work is milliseconds.
* **Security assumptions**: Discrete log hardness in $\mathbb{G}_2$; Groth16 soundness; **GT‑XPDH (External Power in $\mathbb{G}_T$) as in §7, Lemma 3**; Schnorr unforgeability for DLREP proofs; DEM key‑commitment. The GS binding CRS is derived transparently via hash-to-curve (no trusted setup ceremony needed for GS, unlike Groth16 itself).

---

### 15) Related work

* Witness Encryption: GGSW13; BL20; algebraic‑language WE (CVW18); KZG WE (BCGJM23).
* Adaptor signatures / Scriptless scripts: Poe18; DHLST19; MuSig2 (BIP‑327, NRS21).
* Computation on Bitcoin: BitVM (Linus23) discusses general compute; our construction removes on‑chain predicates by gating signature completion with WE.

---

### 16) Minimal equations

**Column-Profile GS‑PPE & KEM:**

**Verifier PPE (column mode):**
$$
\prod_{j=0}^{n_B-1} e(X^{(B)}_j, Y_j) \cdot e(X^{(B)}_\delta, [\delta]_2) \cdot e(C, [\delta]_2) = R(\mathsf{vk},x)
$$

**Arming (per share $i$):**
$$
D_j = Y_j^{\rho_i} \text{ for } j \in [0, n_B-1], \quad D_\delta = [\delta]_2^{\rho_i}
$$
$$
M_i = R(\mathsf{vk},x)^{\rho_i} \in \mathbb{G}_T, \quad K_i = \text{Poseidon2}(\text{ser}_{\mathbb{G}_T}(M_i) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest})
$$

**Decap (permissionless):**
$$
\tilde{M}_i = \left(\prod_{j=0}^{n_B-1} e(X^{(B)}_j, D_j)\right) \cdot e(X^{(B)}_\delta, D_\delta) \cdot e(C, D_\delta) = R(\mathsf{vk},x)^{\rho_i} = M_i
$$
$$
K_i' = \text{Poseidon2}(\text{ser}_{\mathbb{G}_T}(\tilde{M}_i) || H_\text{bytes}(\texttt{ctx\_hash}) || \texttt{GS\_instance\_digest})
$$

**Adaptor finalize:**
$$
\alpha = \sum_i s_i, \quad s = s' + \alpha \pmod{n}
$$

We turn validity into a key, and on Bitcoin that key is exactly the missing scalar that completes a Taproot signature.