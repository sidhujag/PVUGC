//! Separate setup and recovery processes for the three-signer synthetic Bitcoin fixture.
mod support;

use bitcoin::hex::{DisplayHex, FromHex};
use rand::rngs::OsRng;
use std::env;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::Path;
use support::{receipt_hash, setup, DemoResult, Receipt, RECEIPT_LEN};

const USAGE: &str =
    "usage: cancel arm NEW_DIRECTORY [ROWS] | cancel recover DIRECTORY RECEIPT_SHA256 BITS";

fn save_new(path: &Path, bytes: &[u8]) -> DemoResult<()> {
    let mut file = File::options().create_new(true).write(true).open(path)?;
    file.write_all(bytes)?;
    Ok(file.sync_all()?)
}

fn load_exact(path: &Path, len: usize) -> DemoResult<Vec<u8>> {
    let mut data = Vec::new();
    File::open(path)?
        .take(len as u64 + 1)
        .read_to_end(&mut data)?;
    if data.len() != len {
        return Err(format!("{} has an unexpected length", path.display()).into());
    }
    Ok(data)
}

fn arm_command(path: &Path, rows: usize) -> DemoResult<()> {
    if !(2..=256).contains(&rows) {
        return Err("ROWS must be in 2..=256".into());
    }
    if path.try_exists()? {
        return Err("arm requires a new directory".into());
    }
    let (receipt, archive) = setup(&mut OsRng, rows)?;
    let bytes = receipt.to_bytes();
    fs::create_dir(path)?;
    save_new(&path.join("archive.bin"), &archive)?;
    save_new(&path.join("receipt.bin"), &bytes)?;
    // The caller records this public digest independently at setup.
    println!("{}", receipt_hash(&bytes).to_lower_hex_string());
    Ok(())
}

fn recover_command(path: &Path, hash: &str, bits: &str) -> DemoResult<()> {
    let witness = match bits {
        "00" => [false, false],
        "01" => [false, true],
        "10" => [true, false],
        "11" => [true, true],
        _ => return Err("BITS must be exactly two binary digits".into()),
    };
    let pinned = <[u8; 32]>::from_hex(hash)?;
    let receipt = Receipt::parse(&load_exact(&path.join("receipt.bin"), RECEIPT_LEN)?, pinned)?;
    let archive = load_exact(&path.join("archive.bin"), receipt.archive_len)?;
    let shares = receipt.shares(&archive, witness)?;
    let signature = receipt.signature(&shares)?;
    println!("{}", signature.to_vec().to_lower_hex_string());
    Ok(())
}

fn run() -> DemoResult<()> {
    let args: Vec<_> = env::args().skip(1).collect();
    match args.as_slice() {
        [cmd, path] if cmd == "arm" => arm_command(Path::new(path), 2),
        [cmd, path, rows] if cmd == "arm" => arm_command(Path::new(path), rows.parse()?),
        [cmd, path, hash, bits] if cmd == "recover" => recover_command(Path::new(path), hash, bits),
        _ => Err(USAGE.into()),
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("cancel: {error}");
        std::process::exit(1);
    }
}
