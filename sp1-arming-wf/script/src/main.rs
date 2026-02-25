use anyhow::{Context, Result};
use clap::Parser;
use serde::{Deserialize, Serialize};
use sp1_sdk::{utils, ProverClient, SP1Stdin};

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingPackagePublic {
    pub profile: Vec<u8>,
    pub delta_base: Vec<u8>,
    pub delta_arm: Vec<u8>,
    pub r_baked: Vec<u8>,
    pub ad_digest: [u8; 32],
    pub ciphertext: Vec<u8>,
    pub tau: [u8; 32],
    pub t_i_bytes: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingPackageWitness {
    pub rho: Vec<u8>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingWfInput {
    pub public: ArmingPackagePublic,
    pub witness: ArmingPackageWitness,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct ArmingWfOutput {
    pub pkg_digest: [u8; 32],
}

/// Run the SP1 arming well-formedness guest.
///
/// This is a thin runner to help generate/verify proofs locally.
/// It expects `--input` to be a bincode-serialized `ArmingWfInput`.
#[derive(Parser, Debug)]
struct Args {
    /// Path to the guest ELF (built from the program crate).
    #[arg(long)]
    elf: String,

    /// Path to a bincode file containing `ArmingWfInput`.
    #[arg(long)]
    input: String,

    /// Verify the produced proof (recommended).
    #[arg(long, default_value_t = true)]
    verify: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();
    utils::setup_logger();

    let elf = std::fs::read(&args.elf).with_context(|| format!("read elf {}", args.elf))?;
    let input_bytes =
        std::fs::read(&args.input).with_context(|| format!("read input {}", args.input))?;

    let input: ArmingWfInput =
        bincode::deserialize(&input_bytes).context("bincode deserialize ArmingWfInput")?;

    let mut stdin = SP1Stdin::new();
    // The guest reads a single `ArmingWfInput` via sp1_zkvm::io::read::<T>().
    stdin.write(&input);

    let client = ProverClient::from_env();
    let (pk, vk) = client.setup(&elf);
    let mut proof = client.prove(&pk, &stdin).run().context("prove")?;

    if args.verify {
        client.verify(&proof, &vk).context("verify")?;
    }

    // Read the committed output.
    let out = proof.public_values.read::<ArmingWfOutput>();
    println!("pkg_digest: {}", hex32(&out.pkg_digest));

    Ok(())
}

fn hex32(b: &[u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut s = String::with_capacity(64);
    for &x in b {
        s.push(HEX[(x >> 4) as usize] as char);
        s.push(HEX[(x & 0x0f) as usize] as char);
    }
    s
}

