"""Compile fixed-statement rows, lift a proof, or verify the packed witness."""

import argparse
import hashlib
import json
from contextlib import ExitStack
from pathlib import Path

from . import curve
from .bqs import Builder, P, R, bit_value, check_row

FORMAT = "pvugc-packed-bqs-v1"
DUMMY = {
    "a": {"x": "1", "y": "2"},
    "b": {"x": [str(c) for c in curve.G2[0]], "y": [str(c) for c in curve.G2[1]]},
    "c": {"x": "1", "y": "2"},
}
ORDER = ("ax", "ay", "bx0", "bx1", "by0", "by1", "cx", "cy")


def load_json(path):
    return json.loads(Path(path).read_text())


def same_public_statement(raw):
    statement = raw.get("statement", raw)
    # Constants come from the trusted fixed-key/public-input specialization.
    # The encoder deliberately ignores any proof fixtures bundled with them.
    return statement


def encoder(which):
    if which == "tate":
        return curve.verify
    from . import ate

    return ate.verify


def emit(statement, proof, which, sink=None):
    circuit = Builder(sink, layout_only=proof is None)
    coords = encoder(which)(circuit, statement, DUMMY if proof is None else proof)
    metadata = dict(format=FORMAT, fr=str(R), pairing=which, **circuit.shape())
    public_bytes = json.dumps(statement, sort_keys=True, separators=(",", ":")).encode()
    metadata["statement_sha256"] = hashlib.sha256(public_bytes).hexdigest()
    metadata["coordinates"] = {
        name: [w.start, w.width] for name, w in zip(ORDER, coords, strict=True)
    }
    return circuit, metadata


def compile_command(args):
    statement = same_public_statement(load_json(args.statement))
    with ExitStack() as files:
        sink = files.enter_context(Path(args.rows).open("xb")) if args.rows else None
        _, metadata = emit(statement, None, args.pairing, sink)
    if args.manifest:
        with Path(args.manifest).open("x") as f:
            json.dump(metadata, f, indent=2)
            f.write("\n")
    print(json.dumps(metadata))


def lift_command(args):
    metadata = load_json(args.manifest)
    raw = load_json(args.proof)
    witness = raw["witnesses"][args.index] if "witnesses" in raw else raw
    b, derived = emit(
        same_public_statement(load_json(args.statement)), witness, metadata["pairing"]
    )
    if derived != metadata:
        raise ValueError("public layout differs from the pinned compilation")
    with Path(args.witness).open("xb") as f:
        f.write(b.assignment)
    print(f"wrote {b.bits} bits ({len(b.assignment)} bytes)")


def check_command(args):
    meta = load_json(args.manifest)
    if meta["format"] != FORMAT or meta["fr"] != str(R):
        raise ValueError("unexpected BQS format or field")
    data = Path(args.witness).read_bytes()
    n = meta["unknowns"]
    if len(data) != (n + 7) // 8 or (n % 8 and data[-1] >> (n % 8)):
        raise ValueError("invalid Boolean witness length or padding")
    shape = hashlib.sha256(b"PVUGC Boolean quadratic rows v1\n")
    count = 0

    def get(atom):
        if atom != (-1, 0) and (atom[0] < 0 or atom[1] <= 0 or atom[0] + atom[1] > n):
            raise ValueError("row references bits outside the statement")
        return bit_value(data, atom)

    with Path(args.rows).open("rb") as f:
        for count, line in enumerate(f, 1):
            shape.update(line)
            if not check_row(json.loads(line), get):
                raise ValueError(f"unsatisfied row {count}")
    if count != meta["constraints"] or shape.hexdigest() != meta["digest"]:
        raise ValueError("constraint stream differs from the pinned manifest")
    coords = [str(get(tuple(meta["coordinates"][key])) % P) for key in ORDER]
    print(
        json.dumps(
            {
                "a": {"x": coords[0], "y": coords[1]},
                "b": {"x": coords[2:4], "y": coords[4:6]},
                "c": {"x": coords[6], "y": coords[7]},
            }
        )
    )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    cmds = parser.add_subparsers(dest="op", required=True)
    compile_ = cmds.add_parser("compile")
    compile_.add_argument("statement")
    compile_.add_argument("--pairing", choices=["tate", "ate"], default="ate")
    compile_.add_argument("--rows")
    compile_.add_argument("--manifest")
    compile_.set_defaults(run=compile_command)
    lift = cmds.add_parser("lift")
    for name in ["statement", "manifest", "proof", "witness"]:
        lift.add_argument(name)
    lift.add_argument("--index", type=int, default=0)
    lift.set_defaults(run=lift_command)
    check = cmds.add_parser("check")
    for name in ["manifest", "rows", "witness"]:
        check.add_argument(name)
    check.set_defaults(run=check_command)
    args = parser.parse_args()
    try:
        args.run(args)
    except (OSError, ValueError, KeyError, IndexError) as err:
        parser.exit(1, f"{parser.prog}: {err}\n")


if __name__ == "__main__":
    main()
