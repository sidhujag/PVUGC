"""Run the PVUGC six-copy SP1 signature-release experiment on the public fixture."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time


PROTOTYPE = Path(__file__).resolve().parent
FRONTEND = PROTOTYPE / "frontend"
FIXTURES = FRONTEND / "testdata"


def run(*command, cwd=FRONTEND, capture=False, stdin=None):
    return subprocess.run(
        command, cwd=cwd, check=True, input=stdin,
        stdout=subprocess.PIPE if capture else None,
    ).stdout


def require_rejection(command, cwd, reason=None):
    result = subprocess.run(command, cwd=cwd, capture_output=True)
    if result.returncode <= 0 or (reason is not None and reason not in result.stderr):
        raise RuntimeError(
            f"expected rejection from {command[0]} {command[1]}, "
            f"got {result.returncode}: {result.stderr.decode(errors='replace')}"
        )


def demo(out):
    # Refuse existing directories so stale outputs cannot turn a failed run into a pass.
    out.mkdir(mode=0o700)
    public = out / "public"
    arming = out / "arming"
    public.mkdir()
    arming.mkdir()
    native = out / "native"
    capsule_cli = out / "capsule-cli"
    print(f"Building tools for {out}", flush=True)
    run("go", "build", "-mod=readonly", "-o", native, ".")
    run("go", "build", "-mod=readonly", "-o", capsule_cli, "./cmd/praxis-capsule")
    # Cargo may use a configured target directory. Read its selected artifact path.
    build = run("cargo", "build", "--locked", "--release", "--example", "cancel",
                "--message-format=json-render-diagnostics", cwd=PROTOTYPE, capture=True)
    artifacts = (json.loads(line) for line in build.splitlines())
    signer = next((Path(msg["executable"]) for msg in artifacts
                   if msg["reason"] == "compiler-artifact" and msg["target"]["name"] == "cancel"
                   and msg.get("executable")), None)
    if signer is None:
        raise RuntimeError("Cargo did not report a cancel example executable")

    compact = [sys.executable, "-B", "-m", "compact"]
    vk = FIXTURES / "sp1-v6.1.0.vk"
    inputs = FIXTURES / "sp1-v6.1.0-inputs.json"
    fixtures = FIXTURES / "sp1-v6.1.0-pairing.json"
    statement = public / "statement.json"
    manifest = public / "manifest.json"
    rows = public / "rows.jsonl.gz"
    print("Compiling the public SP1 verifier", flush=True)
    statement.write_bytes(run(native, "-statement", vk, inputs, capture=True))
    run(*compact, "compile", statement, "--arithmetic", "narrow-factored",
        "--manifest", manifest, "--rows", rows, capture=True)

    # The armer wraps a completed Bitcoin signature from the separate synthetic fixture.
    bitcoin = arming / "bitcoin"
    bitcoin_pin = run(signer, "arm", bitcoin, "2", capture=True).decode().strip()
    # Verifiers need only the pinned receipt, including the fixture transaction's output key.
    bitcoin_public = public / "bitcoin"
    bitcoin_public.mkdir()
    (bitcoin_public / "receipt.bin").write_bytes((bitcoin / "receipt.bin").read_bytes())
    (bitcoin_public / "pin.txt").write_text(bitcoin_pin + "\n")
    signature = arming / "signature.bin"
    expected = bytes.fromhex(run(signer, "recover", bitcoin, bitcoin_pin, "01", capture=True).decode())
    if len(expected) != 65:
        raise ValueError("fixture returned an unexpected Bitcoin signature length")
    signature.write_bytes(expected)
    capsule = public / "capsule.bin"
    print("Arming the signature capsule", flush=True)
    started = time.monotonic()
    pin = run(capsule_cli, "arm", manifest, rows, signature, capsule, capture=True).decode().strip()
    arm_seconds = time.monotonic() - started
    (public / "capsule-pin.txt").write_text(pin + "\n")

    open_command = [capsule_cli, "open", manifest, rows, capsule]
    open_seconds = []
    proofs = []
    for i in range(2):
        work = out / f"open-{i}"
        work.mkdir()
        witness = work / "witness.bin"
        opened = work / "signature.bin"
        run(*compact, "lift", statement, manifest, fixtures, witness, "--index", str(i), capture=True)
        decoded = run(*compact, "check", manifest, rows, witness, capture=True)
        run(native, "-verify-decoded", vk, inputs, stdin=decoded)
        proofs.append(json.loads(decoded))
        print(f"Opening with proof {i + 1}", flush=True)
        started = time.monotonic()
        run(*open_command, pin, witness, opened, cwd=work)
        open_seconds.append(time.monotonic() - started)
        if opened.read_bytes() != expected:
            raise ValueError(f"proof {i + 1} recovered a different signature")
        run(signer, "verify", bitcoin_public, bitcoin_pin, opened, cwd=work)
    if proofs[0] == proofs[1]:
        raise ValueError("the two decoded Groth16 proofs were identical")

    print("Checking the invalid witness, receipt and Bitcoin signature", flush=True)
    checks = out / "negative"
    checks.mkdir()
    good_witness = out / "open-0" / "witness.bin"
    altered = bytearray(good_witness.read_bytes())
    # This bit lies in proof A's x-coordinate for the pinned clock fixture.
    altered[3] ^= 0x80
    bad_witness = checks / "changed-witness.bin"
    bad_witness.write_bytes(altered)
    rejected = checks / "rejected-output.bin"
    require_rejection([*open_command, pin, bad_witness, rejected], checks, b"unsatisfied BQS row")
    if rejected.exists():
        raise RuntimeError("an invalid witness published an output")
    bad_pin = ("1" if pin[0] == "0" else "0") + pin[1:]
    require_rejection([*open_command, bad_pin, good_witness, rejected], checks, b"capsule receipt mismatch")
    if rejected.exists():
        raise RuntimeError("a mismatched receipt published an output")
    altered_sig = bytearray(expected)
    altered_sig[0] ^= 1
    bad_signature = checks / "changed-signature.bin"
    bad_signature.write_bytes(altered_sig)
    require_rejection([signer, "verify", bitcoin_public, bitcoin_pin, bad_signature], checks)

    summary = {
        "fixture": "SP1 v6.1.0 clock / synthetic Taproot cancellation",
        "capsule_bytes": capsule.stat().st_size,
        "capsule_receipt": pin,
        "bitcoin_receipt": bitcoin_pin,
        "recovered_signature_sha256": hashlib.sha256(expected).hexdigest(),
        "arm_seconds": round(arm_seconds, 2),
        "open_seconds": [round(seconds, 2) for seconds in open_seconds],
    }
    (out / "result.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(f"Both proofs recovered the verified signature. Results are in {out / 'result.json'}.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path, help="new directory for the public capsule and fixture outputs")
    args = parser.parse_args()
    try:
        demo(args.output.absolute())
    except (OSError, ValueError, RuntimeError, subprocess.CalledProcessError) as exc:
        parser.exit(1, f"{parser.prog}: {exc}\n")


if __name__ == "__main__":
    main()
