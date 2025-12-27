Got it. Below is a clean, advisor‑facing writeup that (a) incorporates the three mandatory tweaks your agent asked for and (b) lays out the full streaming math/algebra + system design for the “optimal” Model‑A solution (flat access, no ORAM/TEE), centered on the dense keyed fingerprint / streaming tag idea (not MBP unrolling, not per‑step PRG).

Status note (important):
- This document describes a target **cryptographic architecture** (dense fingerprint + WZ17-style CCO/LO). It is **not implemented end-to-end** in this repository today (in particular: no production FHE / CCO lock artifact generator here).
- This repo *does* build and contains the SP1-oracle tooling + local checkers used to develop the Track‑A A2 relation (e.g., `oracle_check`, `oracle_corrupt`, parity encoders, streaming reader).

⸻

PVUGC Track‑A Streaming Unlock: Dense Keyed Fingerprint + WZ17‑style CCO

1) What this solves (in one paragraph)

We want an operatorless, one‑sided armed, proof‑agnostic PVUGC unlock layer under a self‑decap adversary who can instrument the client and observe file access patterns. Therefore, any “hidden query schedule” must survive the file model: the decapsulator must not perform random access whose offsets encode secret indices. The correct response is to avoid sparse spot‑checks entirely and instead compute a dense keyed fingerprint of a streamed residual vector derived from the witness/oracle bundle \pi. The lock releases salt shares \sigma_i iff the fingerprint matches a secret high‑entropy target \alpha_i (compute‑and‑compare form), using LWE‑based CCO/LO (WZ17 family) rather than generic “public decryption of FHE noise.”  ￼

Recommended “vault profile” design (what we are aiming for)
- **Armers**: \(N=15\), require N-of-N shares for decap.
- **One-time per circuit-shape blob**: use a **shared encrypted basis** (Appendix below) so the large download is amortized across many statements.
- **Tag domain**: 256-bit domain (for negligible brute-force/collision on invalid \(\pi\)); implement via CRT primes (so use a small coordinate count, e.g. \(d=4\) with ~64-bit primes).
- **Basis size**: choose \(s \ge N\) (e.g. \(s=16\)) and enforce the full-rank \(W(x)\) condition so N-of-N soundness amplification does not collapse.
- **SIMD slots**: \(B\approx 16384\) as a starting point (implementation-dependent).
- **Decap**: fully local/operatorless; pre-aggregate basis for each statement, then perform a single streaming pass.

⸻

2) Mandatory fixes (the ones your agent requested)

(A) Make the “residual stream” definition explicit

Define r(\pi,x) as the vector (or stream) of all constraint residuals for the fixed relation you are targeting, including:
	•	per‑row AIR/local constraints (main trace),
	•	boundary constraints (statement binding, public values digest, vk hash, padding rules),
	•	cross‑table wiring constraints (chip boundary equalities, routed wires),
	•	lookup / permutation / memory‑consistency constraints (exec vs sorted views, etc.).

Then the correctness predicate is:

R(x,\pi)=1 \quad \Longleftrightarrow \quad r(\pi,x)=\mathbf{0}.

This is the safe phrasing: it prevents an expert from saying “you only checked the easy local part.”

(B) Plaintext \pi-only input interface

The only input to the lock is plaintext \pi. Any ciphertext material (e.g., encrypted coefficient blocks, evaluation keys) is embedded inside the lock artifact. The adversary cannot supply chosen ciphertexts as inputs to the compare gate; they can only supply plaintext \pi, from which the lock internally derives whatever ciphertext it needs.

This directly addresses the “decrypt‑and‑compare oracle on chosen ciphertexts” concern and avoids the trivial “encrypt the target” break that happens when the compare value is public (e.g., 0) and ciphertexts are accepted as inputs.

(C) One mandatory parameter line (brute‑force soundness of the CC target)

Choose tag parameters so that the accidental accept probability is negligible:

Pick a tag domain \mathbb{Z}_t^d such that \log_2(|\mathbb{Z}_t|^d)\ge 128. Then for any invalid \pi, \Pr[\mathrm{tag}_i(\pi)=\alpha_i]\le 2^{-128} (up to the fingerprint/universality argument below).

Concrete note: if \(t\approx 2^{31}\) (BabyBear-ish prime), then \(d=4\) gives only ~124 bits; use \(d=5\) for comfortable \(\ge 128\) bits (or choose a larger modulus / CRT).

That’s the sentence reviewers will demand.

(D) Don’t overclaim “succinctness” for offline coefficient blocks

If you use offline‑sampled, SIMD‑packed coefficient ciphertext blocks, the artifact is not “polylog in |\pi|” in the strict complexity‑theory sense. It’s linear in the number of SIMD blocks, i.e., O(\#\text{blocks}). In the 100–300 MiB regime, even with aggressive packing, \#\text{blocks} is typically in the **thousands** (see §7.1 example), so the honest phrasing is:
	•	“linear‑but‑feasible,” not “succinct.”

Practical hygiene note: sample fresh coefficient blocks per arming instance (at least per statement \(x\)); don’t reuse the exact same coefficient set across many unrelated statements together with a long-lived accept/reject interface.

⸻

3) Core construction (math)

3.1 Objects
	•	Statement x: fixed SP1 terminal relation identifier + bound public values (e.g., recursion PV digest, program id/vk digest, shape/version id).
	•	Oracle/witness \pi: SP1 “A2” wrapper witness bundle (e.g., shrink‑wrapper traces), treated as a byte stream of length |\pi| (typically 100–300 MiB).

For each armer A_i:
	•	salt share \sigma_i\in\{0,1\}^{\kappa}, commitment c_i = H(\sigma_i).
	•	secret target \alpha_i\in\mathbb{Z}_t^d (high entropy).
	•	secret coefficient vectors k_i that define a fingerprint over the residual stream.

3.2 Residual stream definition

Partition the witness bundle into T “positions” (or “micro‑steps”) consistent with your fixed relation shape. For each position j, the verifier computes a residual vector:

r_j(\pi,x) \in \mathbb{Z}_t^{m}

where m is the number of residual components you expose per position. This may be:
	•	one scalar residual per position (preferred): e.g., a deterministic “composition” residual,
	•	or a small fixed vector of residuals (still fine).

Correctness requirement:
R(x,\pi)=1 \iff \forall j,\ r_j(\pi,x)=\mathbf{0}.

3.3 Dense keyed fingerprint (“streaming tag”)

Define the tag:

\mathrm{tag}_i(\pi)
\;:=\;
\alpha_i
\;+\;
\sum_{j=1}^{T}
\langle k_{i,j},\ r_j(\pi,x)\rangle
\;\in\;
\mathbb{Z}_t^d.
	•	Here k_{i,j}\in \mathbb{Z}_t^{m\times d} (or equivalently d vectors of length m).

Properties:
	•	If \pi is valid: all r_j=0 ⇒ \mathrm{tag}_i(\pi)=\alpha_i.
	•	If \pi is invalid: residual stream not identically zero ⇒ the dot product behaves like a universal hash.

3.4 Why false accepts are 1/|t|^d (the key algebra)

Work in a field \mathbb{F} (take t prime, or use multiple primes / CRT). Let R\neq 0 be the flattened residual vector, and K be uniformly random. Then:

\langle K,R\rangle
\text{ is uniform in }\mathbb{F}.

Proof sketch (one‑line): pick an index \ell where R_\ell\neq 0. Condition on all K_j for j\neq \ell; then \langle K,R\rangle = c + K_\ell R_\ell where R_\ell is invertible, so as K_\ell is uniform, the inner product is uniform.

Thus:
\Pr[\mathrm{tag}_i(\pi)=\alpha_i] = 1/|\mathbb{F}|^d.

That’s the precise basis for the parameter line in §2(C).

⸻

4) The lock program (what CCO/LO must implement)

For each armer i, publish an obfuscation of the program:

P_i(\pi)\;=\;
\begin{cases}
\sigma_i & \text{if } \mathrm{tag}_i(\pi)=\alpha_i \\
\bot & \text{otherwise}.
\end{cases}

This is a compute‑and‑compare program CC[f_i,\alpha_i,\sigma_i] where:
	•	f_i(\pi)=\mathrm{tag}_i(\pi),
	•	\alpha_i is the secret lock value,
	•	\sigma_i is the payload.

This is exactly the “compute‑and‑compare” pivot that resolves the “noise paradox” critique: you are not asking the public to distinguish raw FHE noise; you are publishing a CCO/LO object that conditionally reveals a secret when the predicate holds.  ￼

Recommended framing (to answer “ct×pt leakage?” cleanly):
- **Public published material**: \(pk_i\), encrypted coefficient blocks \(\{\mathrm{ctK}^{(b,\ell)}_i\}_{b,\ell}\), and any evaluation/rotation keys.
- **Public deterministic computation**: a procedure `EvalTag_i(x, π)` that streams plaintext \(\pi\) and outputs ciphertext(s) encrypting \(\mathrm{tag}_i(\pi)\). This stage is homomorphic linear algebra (ct×pt, adds, rotations).
- **The actual CCO/LO gate**: a compute-and-compare gate that releases \(\sigma_i\) iff the ciphertext decrypts to the secret high-entropy target \(\alpha_i\).

Under the IND-CPA security of RLWE/LWE, publishing many ciphertext encryptions of coefficient blocks is intended to be safe; the only leakage channel should be whether the CC gate releases \(\sigma_i\).

Implementation nuance: secure CCO/LO instantiations should not be described as “embedding the raw secret key” as a white-box value. Conceptually the CC gate has decryption capability, but in secure constructions it is represented via obfuscated/algebraic lock material derived from that key.

⸻

Appendix: Artifact-size “knobs” (what is safe, and what can break)

This section summarizes the practical knobs to reduce per-armer artifact size, with the condition under which each knob remains sound in the Model‑A self‑decap setting.

- **Knob 1: reduce tag dimension \(d\)**: safe if the total tag domain satisfies \(\log_2(|\mathbb{Z}_t|^d)\ge 128\) (or, if you rely on N-of-N soundness allocation, see Knob 6 below) and the coefficient distribution remains high-entropy/universal over the chosen domain.
- **Knob 2: reduce \(T\) / reduce block count \(B_{\text{cnt}}\)**: safe only by (a) actually shrinking \(|\pi|\), (b) redesigning the fixed relation to use fewer cells/residual positions, or (c) changing packing so each “position” carries more information. **Unsafe**: dropping residuals or replacing a vector of residuals by a *public* linear combination (cancellations exist). If you compress a vector of local residuals \(\mathbf c\), you need a map \(g\) such that \(g(\mathbf c)=0 \iff \mathbf c=\mathbf 0\); generic public linear combinations do not satisfy this.
- **Knob 3: increase slots \(B\)**: often neutral for artifact size because larger rings increase both slots and ciphertext size; it can still help runtime. Also account for evaluation-key overhead (rotations).
- **Knob 4: reduce ciphertext size \(\textsf{ctsize}\)**: safe if parameters remain at target hardness and noise budget supports all ct×pt multiplies, additions, and rotations. Practical subknobs include **seeded ciphertexts** for coefficient blocks and **minimizing/compressing rotation keys** (e.g., only power-of-two rotations needed for slot-sum).
- **Knob 5: seed expansion of coefficients**: safe only if the seed remains hidden. If coefficients become public/predictable, an attacker can target the kernel of the known sketch. The hidden-seed version usually pushes cost into heavy encrypted/PRG expansion, so it is typically rejected for v0 latency.

Two extra knobs that matter in practice:

- **Knob 6: N-of-N armer soundness allocation**: if decap requires all \(N\) shares and armers use independent \((k_i,\alpha_i)\), then false-unlock probability multiplies. For \(Q\) attempted inputs,
  \[
  \Pr[\text{false unlock in }Q\text{ tries}] \;\lesssim\; Q \cdot \prod_{i=1}^N \frac{1}{|\mathbb{Z}_t|^{d_i}}.
  \]
  This can let you choose smaller per-armer tag spaces \((t,d_i)\) while maintaining an overall target (e.g. 128-bit) **soundness**. It does *not* make the derived key “\(256N\)-bit secure”; it only allocates the collision/false-accept budget across armers.
- **Knob 7: choose ring degree to minimize eval-key overhead**: artifact size is “coeff ciphertexts + rotation keys.” Optimizing for fewer/cheaper keys can matter more than maximizing slots.

---

Appendix: One-time “shared encrypted basis” blob (per circuit shape, reusable across statements)

If you are willing to ship a **large one-time blob** (10–100+ GB) per circuit shape, you can avoid per-statement
multi-GB downloads *without* homomorphic PRG expansion by storing a **basis** of encrypted coefficient blocks.

#### Construction sketch

Let \(s\) be the basis size. For each block \(b\) and coordinate \(\ell\), publish \(s\) basis ciphertexts under a global key:

\[
\mathrm{ctK}^{(b,\ell)}[j] := \mathrm{Enc}_{pk_g}(V^{(b,\ell)}_j)\in \mathbb{Z}_t^B,\quad j=0,\dots,s-1
\]

For a statement \(x\), derive public weights \(w(x)\in \mathbb{Z}_t^s\) (e.g., from a statement hash mapped into \(\mathbb{Z}_t\)). Define the effective per-statement coefficient ciphertext as a linear combination:

\[
\mathrm{ctK}^{(b,\ell)}(x) := \sum_{j=0}^{s-1} w_j(x)\cdot \mathrm{ctK}^{(b,\ell)}[j].
\]

Then run the usual streaming `EvalTag(x, π)` using \(\mathrm{ctK}^{(b,\ell)}(x)\). This uses only ciphertext additions and ciphertext×plaintext scalar multiplies to precompute \(\mathrm{ctK}(x)\), and ct×pt multiplies during the stream.

#### N-of-N independence condition (important if the blob is shared across armers)

If **multiple armers share the same basis blob**, you must ensure armers’ effective coefficient vectors are **independent**. Otherwise, all armers accept/reject together and N-of-N does *not* amplify soundness.

A clean sufficient condition:
- choose \(s \ge N\),
- for each statement \(x\), derive a full-rank weight matrix \(W(x)\in \mathbb{Z}_t^{N\times s}\) (domain-separated hash-to-field), and
- let armer \(i\) use row \(w_i(x)\) as its weights.

Then for each fixed \((b,\ell)\), the induced map \((V_0,\dots,V_{s-1}) \mapsto (K_1,\dots,K_N)=W(x)\cdot (V_0,\dots,V_{s-1})\) is surjective when \(\mathrm{rank}(W)=N\), so the per-armer coefficient blocks are jointly uniform (information-theoretically, conditioned on the hidden basis).

Implementation-friendly choices include Vandermonde-style full-rank matrices or “random until full-rank” matrices derived from \(H(\text{domain}\,||\,x)\).

Rank-cap sanity check: if coefficient vectors are derived from an \(s\)-dimensional basis, then N-of-N soundness amplification is capped at about \(1/|\mathbb{Z}_t|^{\min(N,s)}\). In particular, if you want the “\(N\) armers gives \(\approx 1/|\mathbb{Z}_t|^N\)” exponent, you need \(s\ge N\) and \(\mathrm{rank}(W)=N\).

Micro-optimization: if you restrict weights \(w_{i,j}(x)\in\{0,1\}\), the mixing step becomes only ciphertext additions (no scalar multiplies). A sum of uniform basis vectors remains uniform as long as not all weights are 0.

#### “Pre-aggregation” optimization (runtime)

The streaming pass cost does **not** need to multiply by \(s\): precompute the effective coefficients \(\mathrm{ctK}(x)\) once (cheap relative to ct×pt), then run the streaming scan at the same per-block cost as the \(s=1\) baseline. You still pay \(O(s\cdot d\cdot B_{\mathrm{cnt}})\) ciphertext add/scalar-mul work up front.

Practical point: ciphertext add/scalar-mul is typically much cheaper than ct×pt multiply (and rotations). So increasing \(s\) usually increases a small “startup” cost more than it increases the streaming latency.

#### Security notes / caveats

- This replaces “fresh iid \(k\) per statement” with “\(k(x)\) derived from a fixed secret basis and public \(w(x)\).” The basis is hidden by IND-CPA encryption; the only intended leakage is accept/reject of the CC gate.
- Avoid any API that exposes chosen-ciphertext queries to the compare/decrypt logic; keep “input = plaintext \(\pi\)” only.

#### Size scaling

With basis size \(s\), coefficient ciphertext storage scales as:
\[
\#\mathrm{ctK} \approx s\cdot d\cdot B_{\mathrm{cnt}}.
\]
This is where the “tens of GB one-time download” comes from.

Concrete sizing example (order-of-magnitude):
- Take \(s=32\), \(d=2\), \(B_{\mathrm{cnt}}\approx 4800\) (e.g., \(|\pi|\approx 300\) MiB with \(B=16384\) and 32-bit residuals).
- If a **seeded ciphertext** for one SIMD coefficient block serializes to ~128 KB, then the basis blob is:
  \[
  32 \cdot 2 \cdot 4800 \cdot 128\text{ KB} \approx 39.3\text{ GB}.
  \]
Actual size depends on RLWE parameters, serialization, and evaluation keys.

Vault-profile sizing (example aligned with \(N=15\), 256-bit tag domain):
- Take \(N=15\), \(s=16\), 256-bit tag domain via CRT so \(d=4\), and \(B_{\mathrm{cnt}}\approx 4800\).
- Using the same 128 KB/seeded-ciphertext rough size:
  \[
  16 \cdot 4 \cdot 4800 \cdot 128\text{ KB} \approx 39.3\text{ GB}.
  \]
This lands in the same “tens of GB one-time blob” regime, while enabling full-rank independence for \(N=15\) and a 256-bit tag domain.

---

Appendix: Optional key-switching variant (keep global \(sk_g\) out of per-armer CC gates)

In the simplest shared-basis design, the CC gate would decrypt under the same \(sk_g\) as the coefficient blob.
If you want each armer \(i\) to have its own \(pk_i,sk_i\) and avoid embedding \(sk_g\) into per-armer gates, add public
key-switching keys \(KSK_{g\to i}\) (generated in the setup ceremony):

- Compute \(\mathrm{ctTag}\) under \(pk_g\) using the shared blob.
- Key-switch locally: \(\mathrm{ctTag}_i := \mathrm{KeySwitch}(\mathrm{ctTag}, KSK_{g\to i})\) to a ciphertext under \(pk_i\).
- Feed \(\mathrm{ctTag}_i\) to the per-armer CC gate that decrypts with \(sk_i\).

This keeps decap local/operatorless (no contacting armers) while isolating the common-mode secret to the setup ceremony.

⸻

5) Optimal streaming implementation strategy (no ORAM, no sparse hidden schedule)

The design goal is: flat sequential scan of \pi + blockwise SIMD so evaluation cost is linear in |\pi| but with very large constants amortized.

5.1 Block / SIMD packing

Let the FHE plaintext space support B SIMD “lanes” (slots). Treat the residual stream as grouped into B-sized blocks:
	•	block index b=1..B_{\text{cnt}},
	•	within block, positions j=(b-1)B+1 .. bB.

Define a residual plaintext vector for each block:

R^{(b)} = (r_{(b-1)B+1},\dots,r_{bB}) \in (\mathbb{Z}_t^{m})^{B}.

Now pack the coefficients for that block into ciphertext(s). For each armer and each coordinate \ell \in [d], you have a ciphertext:

\mathrm{ctK}^{(b,\ell)}_i = \mathrm{Enc}_{pk_i}\big( (k^{(\ell)}_{i,(b-1)B+1},\dots,k^{(\ell)}_{i,bB}) \big)

(one ciphertext per block per coordinate; if m>1, you either:
	•	pack the m residual components into separate passes, or
	•	pre‑aggregate residuals into a single scalar per position so m=1.)

5.2 Streaming evaluation loop (flat access)

The evaluator runs P_i(\pi) and it performs:
	1.	Initialize encrypted accumulators \mathrm{ctAcc}^{(\ell)} \leftarrow \mathrm{Enc}(0) for \ell=1..d.
	2.	Sequentially read \pi once in a fixed order, and for each block b:
	•	compute plaintext residual vector R^{(b)} from the streamed witness chunk(s) and statement x,
	•	encode R^{(b)} into plaintext slot polynomials.
	•	compute per coordinate:
\mathrm{ctProd}^{(b,\ell)} \leftarrow \mathrm{ctK}^{(b,\ell)}_i \odot R^{(b)}
where \odot is ciphertext×plaintext slotwise multiply (cheap; no ct×ct).
	•	reduce slots to a scalar by rotations:
\mathrm{ctSum}^{(b,\ell)} \leftarrow \mathrm{SlotSum}(\mathrm{ctProd}^{(b,\ell)})
	•	accumulate:
\mathrm{ctAcc}^{(\ell)} \leftarrow \mathrm{ctAcc}^{(\ell)} + \mathrm{ctSum}^{(b,\ell)}.
	3.	Form encrypted tag:
\mathrm{ctTag}^{(\ell)} \leftarrow \mathrm{Enc}(\alpha_i^{(\ell)}) + \mathrm{ctAcc}^{(\ell)}.
	4.	Decrypt and compare internally (the CC gate): if \mathrm{Dec}(\mathrm{ctTag})=\alpha_i, release \sigma_i.

5.3 Why this is “optimal” for Model‑A
	•	Access pattern leakage is neutralized: you read \pi in a fixed sequential order regardless of any secret. There is no “schedule” to learn from offsets.
	•	No per‑position PRG stepping: coefficients are sampled offline, then stored encrypted per SIMD block. You pay O(B_{\text{cnt}}) ciphertext multiplications, not O(T) PRG transitions.
	•	No bootstrapping requirement (typically): the homomorphic work is dominated by ct×pt multiplies, additions, rotations/key‑switches. You avoid deep ct×ct multiplication chains.

This matches your “finite‑state chain vs tree” intuition: the logic is a sequential streaming automaton; the noise growth problem is handled by using FHE ops that don’t consume multiplicative depth aggressively, and by keeping multiplications ciphertext×plaintext. (Parallel reduction is optional for throughput, but not required for correctness.)

⸻

6) PVUGC salt‑share key derivation (proof‑agnostic)

Armers publish c_i=H(\sigma_i) and locks CT_i implementing P_i(\cdot).

User decap with any valid \pi:
	1.	\sigma_i \leftarrow CT_i(\pi).
	2.	Check H(\sigma_i)=c_i.
	3.	\sigma = \bigoplus_i \sigma_i.
	4.	K(x) = \mathrm{HKDF}(\text{salt}=\sigma,\ \text{info}=H(x)).

Because \sigma is armer‑chosen and independent of the witness randomness, K(x) is proof‑agnostic for fixed x.

⸻

7) Artifact size and compute cost (honest framing)

7.1 Artifact size per armer (linear‑but‑feasible)

Let:
	•	\textsf{ctsize} be ciphertext size (depends on RLWE params),
	•	B slots per ciphertext,
	•	T positions (after packing/oracle layout),
	•	B_{\text{cnt}} = \lceil T/B\rceil blocks,
	•	d tag coordinates.

Then encrypted coefficient material is:

\text{Coeff bytes} \approx d \cdot B_{\text{cnt}} \cdot \textsf{ctsize}.

Plus evaluation keys (rotations) and the CCO “compare‑and‑release” wrapper.

This is not \Omega(T) ciphertexts if B is large; it’s \Omega(T/B). In your regime, this can range from **hundreds to thousands** of ciphertext blocks depending on packing and the concrete FHE slot count.

Concrete sizing example (order-of-magnitude):
- Suppose \(|\pi| = 300\) MiB and residuals are represented as 32-bit words, so \(T \approx |\pi|/4 \approx 78.6\) million positions.
- With \(B = 16{,}384\) slots, the block count is \(B_{\text{cnt}} \approx \lceil T/B \rceil \approx 4{,}800\) blocks.
- Coefficient ciphertext count is then \(\approx d \cdot B_{\text{cnt}}\) (times any factor from representing \(m>1\) residual components).
Call this “linear in blocks,” not “succinct.”

7.2 Runtime

Runtime decomposes into:
	1.	Plaintext streaming residual extraction: O(|\pi|) work; dominated by parsing + computing local constraints (can be SIMD’d; this is where “Binius/binary‑tower mindset” helps: make residual extraction XOR/linear‑heavy).
	2.	Homomorphic accumulation: for each block and each coordinate:

	•	one ct×pt multiply,
	•	\log_2 B rotations/adds to slot‑sum (or a baby‑step/giant‑step slot‑sum if you optimize),
	•	plus a final decrypt+compare.

You can now benchmark this concretely once you pick RLWE parameters and slot count.

⸻

8) Where Binius / binary‑tower helps (precisely, without hype)

Binius/binary‑tower ideas help at the streaming boundary, not by magically making LO cheap:
	1.	Reduce T: pack more witness “meaning” per streamed position (more lanes per block, fewer blocks).
	2.	Make residual extraction cheap: choose/check constraints that are mostly XOR / linear maps over \mathbb{F}_2 or small towers; avoid heavy nonlinear hashing inside the residual definition.
	3.	Keep residuals in a small modulus so ct×pt is cheap and noise growth is mild.

The big win in this specific architecture remains offline‑sampled, SIMD‑packed encrypted coefficients (no per‑step PRG).

⸻

9) Why this avoids the “compressible no‑op layers” dead end

You no longer have a hidden sparse set S\subset [T] of “real checks” and T-|S| no‑ops. There is no “identity step reuse” vulnerability because:
	•	every position contributes to the fingerprint, and
	•	the secret coefficients prevent the adversary from crafting a \pi that makes the fingerprint land exactly on \alpha except with 2^{-128}-scale probability.

So you’re not trying to compress \Omega(L) explicit MBP layers; you’re computing a single encrypted tag via a streaming dot‑product.

Practical note on “soundness under many tries”:
- The \(2^{-128}\)-style bound is per attempted decapsulation. Under \(Q\) attempted inputs, a conservative bound is \(\le Q \cdot 2^{-128}\) (before accounting for any additional structure in the residual extractor).

⸻

10) Minimal “send to GPT Pro” patch text (if you want a short delta)

If what you literally want is the patch request to “the pro writeup,” it’s:
	1.	Add the residual definition:

“Define r(\pi,x) as the vector of all local+boundary+wiring+memory residuals for the fixed relation; then r=0 \iff R(x,\pi)=1.”

	2.	Add the interface sentence:

“The only input is plaintext \pi; all ciphertext material is internal to the object; adversary cannot provide chosen ciphertext inputs.”

	3.	Add the parameter sentence:

“Choose (t,d) so \log_2(|\mathbb{Z}_t|^d)\ge 128; then invalid \pi passes with probability \le 2^{-128}.”

	4.	Fix “succinct” wording:

“Artifact scales with the number of SIMD blocks T/B (linear‑but‑feasible), not strictly polylog in T.”

⸻

If you want, I can also rewrite this into a single‑page diagram + pseudocode format (Arming/Decap + block loop + tag compare) so it’s drop‑in for docs/WE_NC1_TrackA.md.