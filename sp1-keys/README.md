# SP1 BLS12-377 Groth16 Keys

This directory contains the universal Groth16 verification keys for SP1 on BLS12-377.

**These keys are universal** - the same VK works for ALL SP1 programs. Only need to generate once.

## Directory Structure

```
sp1-keys/
├── test/           # Smaller params for fast testing
│   ├── groth16_vk.bin
│   └── groth16_pk.bin (optional, for local proving)
├── production/     # Full security params
│   ├── groth16_vk.bin
│   └── groth16_pk.bin
└── README.md
```

## Generating Keys

Run SP1's trusted setup with the `syscoin/sp1` fork:

```bash
cd /path/to/syscoin/sp1

# For test params (faster setup, lower security)
SP1_DEV=1 cargo run -p sp1-prover --release --bin build_groth16_bn254 --features native-gnark -- \
  --build-dir /path/to/PVUGC/sp1-keys/test

# For production params (full setup, ~128-bit security)
cargo run -p sp1-prover --release --bin build_groth16_bn254 --features native-gnark -- \
  --build-dir /path/to/PVUGC/sp1-keys/production
```

## Key Properties

| Param Set   | Security | Setup Time | Proof Size | VK Size |
|-------------|----------|------------|------------|---------|
| test        | ~80-bit  | ~minutes   | ~384 bytes | ~1 KB   |
| production  | ~128-bit | ~hours     | ~384 bytes | ~1 KB   |

## Usage

The `sp1_bridge` module automatically loads the appropriate VK:

```rust
use arkworks_groth16::sp1_bridge::SP1_GROTH16_VK;

// VK is loaded at compile time from sp1-keys/production/groth16_vk.bin
let vk = SP1_GROTH16_VK.clone();
```

## Important Notes

1. **Never regenerate in production** - The VK is tied to the trusted setup ceremony
2. **Keep pk.bin secure** - Only needed for proving, not verification
3. **VK is public** - Safe to commit to repo
4. **Same VK for all programs** - SP1's wrapper circuit is universal





