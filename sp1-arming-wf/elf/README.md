# Production SP1 Guest ELF

This folder is for the **production-distributed** SP1 guest ELF for the PVUGC arming
well-formedness proof.

The arming-time verifier can use this ELF (plus the SP1 verifying key derived by `client.setup`)
to verify arming well-formedness proofs offline in SP1's native STARK proof modes.

## Expected Filename

`sp1-arming-wf/elf/pvugc-sp1-arming-wf-program.elf`

## Notes

- This ELF is intended to be committed and used in production workflows (not a test-only artifact).
- Integration test `tests/test_sp1_arming_wf.rs` defaults to this path, but you can override locally
  by setting `PVUGC_SP1_ARMING_WF_ELF=/abs/path/to/pvugc-sp1-arming-wf-program.elf`.

