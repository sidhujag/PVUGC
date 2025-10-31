# PVUGC Security Mutation Tests — 2025-02-14

## Overview
- Added a dedicated security harness (`tests/security_mutations.rs`) to stress the PVUGC verification pipeline without altering core library logic.
- Purpose: exercise high-risk failure modes (proof tampering, cross-session replay, DEM tag manipulation) and assert that existing safeguards reject them.
- Scope limited to unit tests; no production code behavior changes.

## Test Suites

1. `verify_rejects_mutated_bundles`
   - Builds honest PVUGC bundles using Groth16 proofs and recorded commitments.
   - Mutates individual components (Groth16 A/C points, DLREP responses, GS commitments and theta limbs).
   - Confirms `OneSidedPvugc::verify` rejects each mutation.

2. `poce_cross_session_replay_fails`
   - Generates two independent arming sessions.
   - Replays PoCE proofs, ciphertext/tag pairs, and column arms across sessions.
   - Ensures `verify_column_arming` fails every replay attempt.

3. `dem_tag_binding_checks_metadata`
   - Uses DEM-SHA256 helper APIs on an honest ciphertext/tag pair.
   - Flips bits in `ad_core`, ciphertext, and tag to verify `verify_key_commitment_dem` detects tampering.
   - Recomputes the tag to prove determinism.

## Outcomes
- All three suites pass; tampering attempts are rejected as expected.
- Provides regression coverage for verifier misuse and replay scenarios without requiring production patches.
- Tests can be expanded for fuzzing or randomized inputs in future work.

## Next Steps
- Optionally integrate these tests into CI for continuous signal.
- Consider extending harnesses with randomized malformed Groth16 attestations or multi-party fuzzing.
