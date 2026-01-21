//! End-to-end pipeline scaffold: SP1 shrink-verifier export → LF+ oneproof → (future) DPP→LWE locks.
//!
//! Goal: integrate the repos so we can drive the existing `latticefold-plus` SP1 oneproof harness from PVUGC.
//!
//! Current behavior:
//! - Step 1 (SP1): runs `sp1-prover`'s `dump_shrink_verify_constraints` to write:
//!   - `SP1_R1LF`     (R1LF file; fixed-shape shrink verifier)
//!   - `SP1_WITNESS`  (witness bundle "SP1W"; per-statement)
//! - Step 2 (LF+): runs `latticefold-plus` example `lf_plus_sp1_oneproof` against those artifacts.
//!
//! Program is dynamic via SP1 env vars:
//! - `ELF_PATH=/path/to/program.elf` (optional; default is SP1's fibonacci example ELF)
//! - `ELF_STDIN_U32=<n>` (optional; default is 10 for fibonacci)
//! - `SHRINK_PROOF_CACHE=/path/to/cache.bin` (optional; speeds up repeated runs)
//! - `REBUILD_SHRINK_PROOF=1` (optional; force rebuild even if cache exists)
//!
//! Debug knobs forwarded into LF+:
//! - `FLIP_PUBLIC_INPUT0=1`
//! - `LFP_SKIP_PREFIX_BINDING_CHECK=1`

use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn env_or(default: &str, key: &str) -> String {
    std::env::var(key).unwrap_or_else(|_| default.to_string())
}

fn run(mut cmd: Command) -> anyhow::Result<String> {
    let out = cmd.stdout(Stdio::piped()).stderr(Stdio::inherit()).output()?;
    if !out.status.success() {
        return Err(anyhow::anyhow!("command failed: status={}", out.status));
    }
    Ok(String::from_utf8_lossy(&out.stdout).to_string())
}

fn ensure_dir(p: &Path) -> anyhow::Result<()> {
    std::fs::create_dir_all(p)?;
    Ok(())
}

fn main() -> anyhow::Result<()> {
    // Workspace-relative defaults (can be overridden by env).
    let sp1_repo = PathBuf::from(env_or("../sp1", "SP1_REPO"));
    let latticefold_repo = PathBuf::from(env_or("../latticefold", "LATTICEFOLD_REPO"));

    // Output paths (local to PVUGC repo).
    let out_dir = PathBuf::from(env_or("target/lfwe_artifacts", "LFWE_OUT_DIR"));
    ensure_dir(&out_dir)?;
    let r1lf_path = out_dir.join("shrink_verifier.r1lf");
    let witness_path = out_dir.join("shrink_verifier.witness.bundle");

    // Debug knobs (propagated into the LF+ oneproof harness).
    let flip_public_input0 = std::env::var("FLIP_PUBLIC_INPUT0").ok().as_deref() == Some("1");
    let skip_prefix_check =
        std::env::var("LFP_SKIP_PREFIX_BINDING_CHECK").ok().as_deref() == Some("1");

    eprintln!("[pvugc/we_latticefold_pipeline] sp1_repo={}", sp1_repo.display());
    eprintln!(
        "[pvugc/we_latticefold_pipeline] latticefold_repo={}",
        latticefold_repo.display()
    );
    eprintln!("[pvugc/we_latticefold_pipeline] out_dir={}", out_dir.display());
    eprintln!("[pvugc/we_latticefold_pipeline] SP1_R1LF={}", r1lf_path.display());
    eprintln!(
        "[pvugc/we_latticefold_pipeline] SP1_WITNESS={}",
        witness_path.display()
    );
    eprintln!(
        "[pvugc/we_latticefold_pipeline] debug: FLIP_PUBLIC_INPUT0={} LFP_SKIP_PREFIX_BINDING_CHECK={}",
        flip_public_input0, skip_prefix_check
    );

    // -------------------------------------------------------------------------
    // Step 1: export shrink-verifier R1LF + witness bundle from SP1.
    // -------------------------------------------------------------------------
    let sp1_stdout = run({
        let mut c = Command::new("cargo");
        c.current_dir(&sp1_repo);
        c.env("SP1_R1LF", &r1lf_path);
        c.env("SP1_WITNESS", &witness_path);

        // Forward dynamic program selection knobs if present.
        if let Ok(p) = std::env::var("ELF_PATH") {
            c.env("ELF_PATH", p);
        }
        if let Ok(v) = std::env::var("ELF_STDIN_U32") {
            c.env("ELF_STDIN_U32", v);
        }
        if let Ok(p) = std::env::var("SHRINK_PROOF_CACHE") {
            c.env("SHRINK_PROOF_CACHE", p);
        }
        if std::env::var("REBUILD_SHRINK_PROOF").ok().as_deref() == Some("1") {
            c.env("REBUILD_SHRINK_PROOF", "1");
        }

        c.args([
            "run",
            "-p",
            "sp1-prover",
            "--bin",
            "dump_shrink_verify_constraints",
            "--release",
        ]);
        c
    })?;
    eprintln!("\n[pvugc/we_latticefold_pipeline] sp1-prover output (stdout):\n{sp1_stdout}");

    // -------------------------------------------------------------------------
    // Step 2: run LF+ oneproof harness on the exported artifacts.
    // -------------------------------------------------------------------------
    let lf_stdout = run({
        let mut c = Command::new("cargo");
        c.current_dir(&latticefold_repo);
        c.env("SP1_R1LF", &r1lf_path);
        c.env("SP1_WITNESS", &witness_path);
        // propagate optional debug knobs
        if flip_public_input0 {
            c.env("FLIP_PUBLIC_INPUT0", "1");
        }
        if skip_prefix_check {
            c.env("LFP_SKIP_PREFIX_BINDING_CHECK", "1");
        }
        c.args([
            "run",
            "-p",
            "latticefold-plus",
            "--example",
            "lf_plus_sp1_oneproof",
            "--features",
            "we_gate",
            "--release",
        ]);
        c
    })?;
    eprintln!(
        "\n[pvugc/we_latticefold_pipeline] latticefold-plus output (stdout):\n{lf_stdout}"
    );

    // Best-effort parsing hooks for downstream integration.
    if let Some(line) = lf_stdout.lines().find(|l| l.contains("stmt_digest=0x")) {
        eprintln!("[pvugc/we_latticefold_pipeline] parsed {line}");
    }
    if let Some(line) = lf_stdout.lines().find(|l| l.contains("lock_coin_seed=0x")) {
        eprintln!("[pvugc/we_latticefold_pipeline] parsed {line}");
    }

    eprintln!("\n[pvugc/we_latticefold_pipeline] OK (pipeline scaffold complete)");
    Ok(())
}
