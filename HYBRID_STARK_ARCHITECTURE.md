# Hybrid STARK Architecture for PVUGC

## Table of Contents
1. [Overview](#overview)
2. [Architecture](#architecture)
3. [Mathematical Construction](#mathematical-construction)
4. [Security Analysis](#security-analysis)
5. [Connection to PVUGC](#connection-to-pvugc)

---

## Overview

### The Problem

Traditional STARK proofs are **large** (100-300 KB) and require expensive verification operations (polynomial commitments, multiple Merkle path checks, FRI protocol). To use PVUGC (Grover-Sahai based key extraction) on STARK proofs, we would need to:

1. Wrap the STARK in a SNARK (to get constant-size Groth16 proof)
2. Verify STARK in-circuit (expensive: Merkle checks, FRI, DEEP)
3. Apply PVUGC to the outer Groth16 proof

This would create a **massive circuit** with high proving costs.

### The Hybrid Solution

Instead of wrapping a STARK proof, we **directly prove STARK verification constraints** in a Groth16 circuit, eliminating the need for an actual STARK proof object.

```
Traditional: Application → STARK Proof → SNARK Wrapper → Groth16 → PVUGC
Hybrid:      Application → STARK Witnesses → Groth16 (STARK constraints) → PVUGC
```

**Key insight**: We don't need the STARK proof bytes - we just need to prove that STARK verification would succeed!

---

## Architecture

### Three-Layer Proof System

```
Layer 1: Inner Circuit (BLS12-377 Groth16)
├─ Proves: "STARK verification constraints hold"
├─ Public inputs: Merkle roots, transcript bytes, L (FRI depth)
└─ Witness: Merkle paths, FRI query data, DEEP evaluations

Layer 2: Outer Circuit (BW6-761 Groth16)  
├─ Proves: "Inner Groth16 proof verifies"
├─ Public inputs: Compressed (via BooleanInputVar)
└─ Witness: Inner proof (A, B, C)

Layer 3: PVUGC (Grover-Sahai on BW6-761)
├─ Extracts: Symmetric key K = M^ρ
├─ Input: Outer Groth16 proof
└─ Property: Proof-agnostic (same K for different witnesses of same statement)
```

### Data Flow

```
Application Trace
    ↓ [Winterfell prover generates witnesses, NO proof object]
Merkle leaves, FRI queries, DEEP evaluations
    ↓ [Inner circuit proves STARK constraints]
Inner Groth16 Proof (A₁, B₁, C₁) on BLS12-377
    ↓ [Outer circuit proves inner verifies]
Outer Groth16 Proof (A₂, B₂, C₂) on BW6-761
    ↓ [PVUGC extracts key]
Symmetric Key K = M^ρ (statement-dependent, proof-agnostic)
```

---

## Mathematical Construction

### Inner Circuit: STARK Verification Constraints

The inner circuit over **BLS12-377** encodes the following STARK verifier logic:

#### 1. **Poseidon Merkle Path Verification**

For each query `i` at position `pos` with leaf `v` and claimed root `r`:

```
Constraint: Poseidon₂-Merkle-Verify(v, path, pos) = r

Implementation:
  cur ← v
  for each (sibling, is_right) in (path, pos):
    left  ← is_right ? sibling : cur
    right ← is_right ? cur : sibling
    cur ← Poseidon₂(left, right)
  enforce: cur = r
```

**Circuit cost**: O(log n) Poseidon hashes per query, where n = trace size

#### 2. **Fiat-Shamir Transcript Binding**

```
Transcript: tag || num_oracles || GL_roots (32B each) || P2_roots (48B each) || tail
            ↓ [RPO-256 sponge]
Challenges: α, β₁, ..., βₗ, ζ

Constraints:
  state ← RPO-Init()
  state ← RPO-Absorb(state, transcript_bytes)
  α ← RPO-Squeeze(state)
  for i = 1..L:
    βᵢ ← RPO-Squeeze(state)
  ζ ← RPO-Squeeze(state)
```

**Circuit cost**: O(1) RPO permutations (independent of STARK size)

**Security**: Binding ensures challenges depend on public commitments (roots). Tampering with any transcript byte → different challenges → verification fails.

#### 3. **DEEP Composition**

For each query at point `x`:

```
DEEP(x) = Σᵢ αⁱ · (fᵢ(x) - fᵢ(ζ)) / (x - ζ)

Constraint:
  sum ← 0
  for i in traces:
    numerator ← oₓ[i] - o_ζ[i]
    denominator ← x - ζ
    enforce: denominator · denominator⁻¹ = 1  // Division check
    sum ← sum + αⁱ · numerator · denominator⁻¹
  enforce: sum = composition_claim
```

**Circuit cost**: O(k) field operations, where k = number of trace polynomials

**Security**: Ensures queried values lie on the claimed polynomials with overwhelming probability (Schwartz-Zippel).

#### 4. **FRI Folding Verification**

For each FRI layer `j`:

```
FRI-Fold(vₗₒ, vₕᵢ, β) = vₗₒ + β · vₕᵢ

Constraint (per layer):
  enforce: v_next = v_lo + βⱼ · v_hi
```

**Circuit cost**: O(L) field operations, where L = log(domain size)

**Security**: Ensures degree reduction at each layer. After L layers, remaining polynomial has constant degree → can be checked directly.

#### 5. **Goldilocks ↔ Bytes Bridging**

Since Winterfell uses Goldilocks field (64-bit) but we're in BLS12-377 (~253-bit):

```
For each GL limb (u64):
  bytes ← little-endian 8-byte encoding
  enforce: Σᵢ bytesᵢ · 256ⁱ = limb (in GL field embedded in Fr377)
```

**Circuit cost**: O(1) per limb

**Purpose**: Connects Poseidon-committed bytes (in Fr377) to GL trace values

---

## Security Analysis

### Soundness Theorem

**Claim**: If the inner circuit verification passes, then the original STARK verification would pass.

**Proof Sketch**:

1. **Merkle Binding**: Poseidon collision resistance ensures:
   ```
   Pr[prover opens to wrong leaf | same root] < 2⁻¹²⁸
   ```

2. **FS Binding**: RPO sponge constraints ensure:
   ```
   challenges = FS(transcript_bytes)
   ```
   Prover cannot choose challenges independently of commitments.

3. **DEEP Soundness**: Schwartz-Zippel lemma:
   ```
   Pr[polynomial degree > d | DEEP check passes] < d / |field|
   ```
   For d = trace_degree and field = Goldilocks (2⁶⁴), negligible.

4. **FRI Soundness**: Each fold reduces degree by half:
   ```
   deg(Pⱼ₊₁) ≤ deg(Pⱼ) / 2
   ```
   After L layers: deg(Pₗ) ≤ deg(P₀) / 2ᴸ

5. **Groth16 Knowledge Soundness**: Prover must "know" valid witnesses:
   ```
   Pr[proof verifies | prover doesn't know witness] < 1 / |Fr|
   ```

**Combined Security**: 
```
ε_total ≈ ε_collision + ε_DEEP + ε_FRI + ε_Groth16
        ≈ 2⁻¹²⁸ + d/2⁶⁴ + (soundness_parameter)⁻¹ + 2⁻²⁵³
        < 2⁻⁶⁴ for reasonable parameters
```

### Completeness

**Claim**: Any valid STARK proof can be converted to valid hybrid witnesses.

**Construction**:
Given a STARK proof `π = (commitments, queries, fri_data)`:

1. Extract Merkle roots from commitments → `poseidon_roots`
2. Extract query openings → `leaf_bytes`, `poseidon_path_nodes`
3. Extract FRI query data → `fri_o_x_gl`, `fri_o_z_gl`
4. Extract FRI layer data → `fri_layers_*`
5. Compute DEEP composition → `fri_comp_claim_gl`

The inner circuit will accept these witnesses iff the original STARK would verify.

### Zero-Knowledge (Optional)

The hybrid approach is **NOT zero-knowledge** by default:
- Inner Groth16 is ZK for the witness (Merkle paths, FRI values)
- But the statement (Merkle roots) is **public**

To add ZK: Commit to roots using a hiding commitment, add randomness to FS transcript.

---

## Connection to PVUGC

### Why This Enables PVUGC

PVUGC (Grover-Sahai based key extraction) works on **Groth16 proofs** with specific properties:

1. **Constant size**: Groth16 proofs are 3 group elements (fixed size)
2. **Pairing-based**: Verification equation uses pairings
3. **Proof-agnostic**: Different proofs of same statement extract same key

### The Chain

```
Step 1: STARK Witnesses → Inner Groth16 (BLS12-377)
├─ Input: Merkle paths, FRI data, DEEP evaluations
├─ Statement: Merkle roots (public)
└─ Output: Inner proof π₁ = (A₁, B₁, C₁)

Step 2: Inner Proof → Outer Groth16 (BW6-761)
├─ Input: π₁, inner VK
├─ Statement: Inner public inputs (94 field elements → compressed to 64)
└─ Output: Outer proof π₂ = (A₂, B₂, C₂)

Step 3: Outer Proof → PVUGC Key Extraction
├─ Input: π₂, statement, randomness ρ
├─ Process: Arm bases, generate commitments, extract via pairing
└─ Output: K = M^ρ (statement-dependent, proof-agnostic)
```

### PVUGC Properties on Outer Proof

#### Proof-Agnostic Extraction

**Setup**:
```
Statement S = (inner_vk, public_inputs_compressed)
```

**Property**:
```
For any two valid inner proofs π₁, π₁' with the same statement S:
  Let π₂ = OuterProve(π₁), π₂' = OuterProve(π₁')
  Then: PVUGC-Decap(π₂) = PVUGC-Decap(π₂') = K_S
```

**Why it holds**:
- PVUGC extraction depends only on **statement encoding**
- Statement = (VK, compressed public inputs)
- Inner public inputs = (Merkle roots, transcript bytes)
- Different witnesses (Merkle paths, FRI data) → Same roots → Same K

#### Statement Binding

**Property**:
```
For different statements S ≠ S':
  K_S ≠ K_{S'} (with overwhelming probability)
```

**Why it holds**:
- Different Merkle roots → Different public inputs → Different statement
- PVUGC extraction: M^ρ is computed from statement-dependent target R(vk, x)
- R(vk, x₁) ≠ R(vk, x₂) for x₁ ≠ x₂

### Constant-Size Scalability

**Key Result**: Outer proof size is **independent of STARK trace size**

| STARK Trace Size | Inner Circuit | Outer Circuit | PVUGC Cost |
|------------------|---------------|---------------|------------|
| 2¹⁰ rows | ~500K constraints | ~20M constraints | ~2K columns |
| 2²⁰ rows | ~500K constraints | ~20M constraints | ~2K columns |
| 2³⁰ rows | ~500K constraints | ~20M constraints | ~2K columns |

**Why**:
- Inner circuit size depends on:
  - Merkle path depth: O(log n) ← **logarithmic**
  - FRI layers: O(log n) ← **logarithmic**
  - DEEP composition: O(k) ← **constant** (k = #traces)
- Outer circuit size: **constant** (just verifies one Groth16 proof)
- PVUGC cost: **constant** (dozens of columns vs millions for full circuit)

---

## Mathematical Construction (Detailed)

### Notation

- **Fr377**: Scalar field of BLS12-377, modulus ~253 bits
- **Fq377**: Base field of BLS12-377 (= Fr of BW6-761)
- **GL**: Goldilocks field, modulus p = 2⁶⁴ - 2³² + 1
- **E₁**: BLS12-377 pairing \( e : G₁ × G₂ → G_T \)
- **E₂**: BW6-761 pairing \( e : G₁' × G₂' → G_T' \)

### Inner Circuit (Over Fr377)

#### Public Inputs (94 field elements)

```
x_inner = [
  r₁, ..., rₙ,           // n Poseidon Merkle roots (Fr377)
  gl₁, ..., gl₃₂ₙ,       // GL root bytes (32B × n, each byte as Fr377 ∈ [0,255])
  p2₁, ..., p2₄₈ₙ,       // Poseidon root bytes (48B × n, each byte as Fr377 ∈ [0,255])
  t₁, ..., tₘ,           // Tail bytes (Winterfell metadata)
  L                      // FRI depth (u8 as Fr377)
] ∈ Fr377^{1+32n+48n+m+1}
```

For minimal test: n=1, m=12 → |x_inner| = 94

#### Witness Data (per query)

```
W_query = {
  leaf_bytes: [u8; 48],                    // Leaf data (Fr377 encoded)
  merkle_path: [(Fr377, bool); depth],     // (sibling, position_bit)
  gl_limbs: [u64; k],                      // GL field elements
  fri_x: GL,                               // Query point
  fri_evaluations: [(GL, GL); num_traces], // (f(x), f(ζ))
  fri_composition: GL,                     // DEEP result
  fri_layers: [(GL, GL, GL); L],          // (v_lo, v_hi, v_next)
}
```

#### Constraint System

**Total constraints**: ~500K (independent of STARK trace size!)

1. **Merkle Verification** (per query)
   ```
   Poseidon₂(leaf, sibling, pos) = parent
   ``` 
   - Constraints: ~1K per hop
   - Depth: log₂(trace_size)
   - Total: ~1K × log₂(n) per query

2. **Fiat-Shamir**
   ```
   state ← RPO256(transcript_bytes)
   α, β₁, ..., βₗ, ζ ← squeeze(state)
   ```
   - Constraints: ~50K (Rescue-Prime permutation)
   - Cost: **O(1)** (independent of STARK size)

3. **DEEP Composition**
   ```
   ∀i: numᵢ = fᵢ(x) - fᵢ(ζ)
   ∀i: denᵢ = x - ζ
   ∀i: denᵢ · denᵢ⁻¹ = 1
   sum = Σᵢ αⁱ · numᵢ · denᵢ⁻¹
   sum = composition_claim
   ```
   - Constraints: ~100 per trace
   - Total: ~100k (for k=10 traces)

4. **FRI Folding**
   ```
   ∀j ∈ [1, L]: v_next[j] = v_lo[j] + βⱼ · v_hi[j]
   ```
   - Constraints: ~10 per layer
   - Total: ~100 (for L ≈ 10)

5. **GL ↔ Bytes Bridging**
   ```
   ∀limb: Σᵢ bytesᵢ · 256ⁱ = limb (mod GL modulus)
   ```
   - Constraints: ~50 per limb
   - Total: ~500k (for large traces)

### Outer Circuit (Over Fq377 = Fr_BW6)

#### Public Inputs (64 field elements - compressed!)

```
x_outer = BooleanInputVar(x_inner)
```

`BooleanInputVar` compresses 94 inner field elements to **64 outer field elements** via hash-based compression.

**Note**: This compression is handled by arkworks for recursion efficiency. The actual compression formula is internal to `ark-crypto-primitives`.

#### Constraint System

**Total constraints**: ~20M (Groth16 pairing check in-circuit)

```
Groth16-Verify-In-Circuit(VK_inner, x_inner, π_inner):
  1. Compute L(x) = Σᵢ xᵢ · γᵢ  [MSM: ~100K constraints for 94 inputs]
  2. Pairing check: e(A,B) = e(α,β) · e(L(x),γ) · e(C,δ)
     [Each pairing: ~5M constraints over BW6-761]
  
Total: ~20M constraints (independent of inner circuit size!)
```

### PVUGC Layer (Over BW6-761)

#### PPE Construction

The outer Groth16 verification equation:
```
e(A, B) = e(α, β) · e(L(x), γ) · e(C, δ)
```

Rearranges to PPE form:
```
e(A, B) · e(-α, β) · e(-L(x), γ) · e(-C, δ) = 1
```

Or in multiplicative notation:
```
R(vk, x) = e(α, β) · e(L(x), γ)  [statement-only]
V(π) = e(A, B) · e(C, δ)⁻¹       [proof-only, but actually depends on statement via randomness]
```

**PVUGC extracts** from the target R(vk, x)^ρ where ρ is the arming randomness.

#### Key Extraction

```
1. Arm bases (at deposit):
   Y_bases = {β_G₂, δ_G₂}
   Y_arms = {β^ρ_G₂, δ^ρ_G₂}

2. Prove (at transaction):
   Generate commitments to proof elements and randomness
   
3. Decap (permissionless):
   M^ρ ← Extract(commitments, arms, statement)
   where M = e(α, β) · e(L(x), γ)
```

**Key property**: M depends only on (vk, x), not on the proof (A, B, C)!

---

## Security Analysis

### Threat Model

**Attacker Goals**:
1. Forge a proof for an invalid STARK computation
2. Malleate a valid proof to get a different key K
3. Reuse witnesses across different statements

### Security Properties

#### 1. **Computational Soundness**

**Property**: Cannot forge proofs for false statements

**Relies on**:
- Poseidon collision resistance
- Schwartz-Zippel (DEEP soundness)
- FRI soundness
- Groth16 knowledge soundness

**Security level**: min(2⁻¹²⁸, 2⁻⁸⁰, 2⁻⁶⁴) ≈ **2⁻⁶⁴** (Goldilocks soundness parameter)

#### 2. **Proof-Agnostic Extraction**

**Property**: Different proofs of same statement extract same K

**Formal**:
```
∀π₁, π₁' such that InnerVerify(vk, x, π₁) = InnerVerify(vk, x, π₁') = true:
  Let π₂ ← OuterProve(π₁)
  Let π₂' ← OuterProve(π₁')
  Then: PVUGC-Decap(π₂, (vk,x)) = PVUGC-Decap(π₂', (vk,x))
```

**Why it holds**:
- PVUGC extraction uses only statement-encoding: R(vk, x)
- R depends on VK and public inputs, not on proof elements
- Different witnesses → same roots → same x_inner → same R → same K

#### 3. **Statement Binding**

**Property**: Different statements extract different keys

**Formal**:
```
∀(vk, x) ≠ (vk', x'):
  Pr[PVUGC-Decap(π, (vk,x)) = PVUGC-Decap(π', (vk',x'))] < 2⁻²⁵³
```

**Why it holds**:
- Different public inputs → different L(x) → different R(vk, x)
- Different R → different extracted key (with overwhelming probability)

#### 4. **Non-Malleability**

**Property**: Cannot tamper with transcript without detection

**Validated by**:
- `tamper_poseidon_root_bytes_fails`: Flipping root byte → verify fails
- `tamper_gl_roots_bytes_fails_fs`: Flipping GL byte → challenges change → verify fails

**Mechanism**: FS challenges are **constrained** to depend on transcript bytes. Any tampering changes challenges, breaking DEEP/FRI checks.

---

## Connection to PVUGC

### Full Flow: STARK → Key Extraction

```python
# 1. Application executes computation
trace = execute_computation(input_data)

# 2. Build Poseidon Merkle tree over trace rows
merkle_tree = build_poseidon_merkle(trace)
root = merkle_tree.root()

# 3. Extract witnesses for inner circuit
witnesses = []
for query_idx in query_indices:
    leaf = trace[query_idx]
    path = merkle_tree.proof(query_idx)
    fri_data = compute_fri_query(trace, query_idx)
    witnesses.append(HybridQueryWitness {
        leaf_bytes: serialize(leaf),
        poseidon_path_nodes: path.siblings,
        poseidon_path_pos: path.positions,
        fri_o_x_gl: fri_data.evaluations_x,
        fri_o_z_gl: fri_data.evaluations_z,
        fri_comp_claim_gl: fri_data.composition,
        fri_layers_*: fri_data.fold_layers,
        ...
    })

# 4. Prove inner (STARK constraints)
inner_proof = prove_inner_stark(
    merkle_roots=[root],
    witnesses=witnesses,
    ...
)

# 5. Prove outer (recursion)
outer_proof, compressed_public_inputs = prove_outer(
    inner_vk,
    inner_public_inputs,
    inner_proof
)

# 6. PVUGC operations
pvugc_vk = extract_pvugc_vk(outer_vk)
rho = random()
arms = arm_columns(pvugc_vk, rho)
bundle = pvugc_prove(outer_proof, arms, statement)

# 7. Key extraction (permissionless)
K = pvugc_decap(bundle, statement)
```

### Why This Matters for PVUGC

Traditional PVUGC works on **application circuits** (e.g., "prove x = y + z"):
- Circuit size: application-specific (could be millions of constraints)
- PVUGC cost: proportional to circuit size

**Hybrid STARK + PVUGC**:
- Circuit size: **constant** (outer circuit, ~20M constraints regardless of STARK size)
- PVUGC cost: **constant** (dozens of columns)
- Enables PVUGC for **arbitrary computations** without per-application circuit design!
