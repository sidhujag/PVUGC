# PVUGC One-Sided GS Review (follow-up)

## Summary of previously reported issues

### 1. KEM key derivation and DEM profile
The current `OneSidedPvugc::setup_and_arm` helper still exposes `K = R^\rho` directly via `compute_r_to_rho` with no Poseidon2 KDF or key-committing DEM enforcement, so the product key is not domain-separated from `ctx_hash` as mandated by the spec’s Poseidon2 profile.【F:src/api.rs†L27-L164】【F:specs/PVUGC.md†L82-L139】

### 2. Decapsulation ignores armed bases
The new `decap_one_sided` path computes the product against the published `U_\ell^\rho`/`\delta^\rho` arms, so the earlier issue where decapsulation trusted a caller-supplied `target^\rho` is resolved.【F:src/api.rs†L144-L149】【F:src/decap.rs†L21-L53】

### 3. Groth16 target derivation
`compute_groth16_target` now multiplies in both the CRS constant term `e(\alpha,\beta)` and the instance-dependent `e(L(x),\gamma)`, so the Groth16 target is tied to `(\mathsf{vk},x)` again.【F:src/ppe.rs†L13-L72】

## Additional observations
* The code base still lacks any implementation of the Poseidon2-based KEM/DEM profile that `specs/PVUGC.md` marks as **MUST**, so ciphertext handling remains undefined beyond exposing `R^\rho`.
