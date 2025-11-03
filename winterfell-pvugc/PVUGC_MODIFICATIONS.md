# Winterfell-PVUGC Modifications

This is a **modified version** of Winterfell STARK library with PVUGC-specific witness extraction hooks.

**DO NOT replace with upstream Winterfell** - this fork contains custom modifications required for hybrid STARK verification in PVUGC.

## Base Version

- **Upstream**: Winterfell 0.13.1
- **Source**: https://github.com/facebook/winterfell
- **License**: MIT

## PVUGC Modifications

### 1. Witness Extraction Hooks (In Progress)

**Location**: `winterfell/src/verifier/pvugc_hooks.rs`

**Purpose**: Extract FRI fold data and DEEP composition witnesses during STARK verification

**Pattern**: Similar to `ark-groth16-pvugc` coefficient recording
- Provides `WitnessLog` structure
- Adds `LoggingVerifierChannel` wrapper
- Captures data without changing verification semantics

**Status**: Scaffold created, needs completion

### 2. Prover Instrumentation (Planned)

**Alternative approach**: Add hooks in prover to emit witness sidecar

**Files**: TBD based on expert guidance

## Why We Fork

PVUGC's hybrid STARK architecture requires access to internal proof data:
- FRI layer fold values: `(v_lo, v_hi, v_next)` per layer
- DEEP composition: `x, ζ, o_x[], o_z[], comp_claim`
- Query positions and leaf values

Winterfell's public API doesn't expose these (private fields in `Proof` struct).

Our options:
1. **Hook the verifier** - Log data during verification (current approach)
2. **Hook the prover** - Emit sidecar during proving (alternative)
3. **Parse proof bytes** - Deserialize and extract (fragile)

We chose approach #1/#2 following our Groth16 coefficient recording pattern.

## Maintenance

When updating to newer Winterfell versions:
1. Check if upstream added public witness accessors (may eliminate need for hooks)
2. Rebase our modifications onto new version
3. Test with `cargo test --test stark_witness_extraction`

## Usage in PVUGC

```rust
use winterfell_pvugc::verifier::pvugc_hooks::{verify_and_log, WitnessLog};

// Generate Winterfell proof
let (proof, trace) = generate_stark_proof(...);

// Extract witnesses via logging verifier
let log = verify_and_log(&air, proof, &options)?;

// Convert to HybridQueryWitness
let witnesses = extract_for_inner_from_proof(&proof, log);

// Feed to inner circuit
let (inner_proof, vk) = prove_inner_stark(..., witnesses, ...);
```

## Related Code

- **Inner circuit**: `src/inner_stark.rs` (STARK constraints in Groth16)
- **Extractor**: `src/witness/winterfell_extract.rs`
- **Test**: `tests/stark_witness_extraction.rs`
- **Documentation**: `HYBRID_STARK_ARCHITECTURE.md`

---

**Last Modified**: November 2, 2025  
**Status**: Modifications in progress  
**Contact**: See main PVUGC repository

