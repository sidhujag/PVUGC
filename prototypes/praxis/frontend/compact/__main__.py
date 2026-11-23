"""Compile fixed-statement rows, lift a proof, or verify the packed witness."""

import argparse
import gzip
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
CENTERED_PAIRINGS = (
    "ate-fused",
    "ate-moving",
    "ate-paired",
    "ate-moving-projected",
    "ate-conic",
    "ate-conic-window",
    "ate-conic-optimized",
)


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
    if which == "ate-fused":
        from . import ate_fused

        return ate_fused.verify
    if which == "ate-moving":
        from . import moving_lines

        return moving_lines.verify
    if which == "ate-paired":
        from . import paired_torus

        return paired_torus.verify_dense
    if which == "ate-moving-projected":
        from . import paired_torus

        return paired_torus.verify_moving_dense
    if which == "ate-conic":
        from . import conic

        return conic.verify
    if which == "ate-conic-window":
        from . import conic_window

        return conic_window.verify
    if which == "ate-conic-optimized":
        from . import conic_window

        return conic_window.verify_optimized
    if which != "ate":
        raise ValueError(f"unknown pairing encoder {which}")
    from . import ate

    return ate.verify


def emit(statement, proof, which, sink=None, arithmetic="integer-limbs"):
    from . import factored_bqs
    from .residue_bqs import PackedResidueBuilder, ResidueBuilder

    builders = {
        "integer-limbs": Builder,
        "centered": ResidueBuilder,
        "packed-centered": PackedResidueBuilder,
        "factored": factored_bqs.FactoredBuilder,
        "packed-factored": factored_bqs.PackedFactoredBuilder,
        "min-bits-factored": factored_bqs.MinBitsFactoredBuilder,
        "narrow-factored": factored_bqs.NarrowFactoredBuilder,
    }
    if which in CENTERED_PAIRINGS and arithmetic == "integer-limbs":
        raise ValueError("the fused pairing requires centered arithmetic")
    circuit = builders[arithmetic](sink, layout_only=proof is None)
    coords = encoder(which)(circuit, statement, DUMMY if proof is None else proof)
    fmt = (
        factored_bqs.FORMAT
        if isinstance(circuit, factored_bqs.FactoredBuilder)
        else FORMAT
    )
    metadata = dict(format=fmt, fr=str(R), pairing=which, **circuit.shape())
    if arithmetic != "integer-limbs":
        metadata["arithmetic"] = arithmetic
    public_bytes = json.dumps(statement, sort_keys=True, separators=(",", ":")).encode()
    metadata["statement_sha256"] = hashlib.sha256(public_bytes).hexdigest()
    metadata["coordinates"] = {
        name: [w.start, w.width] for name, w in zip(ORDER, coords, strict=True)
    }
    return circuit, metadata


def open_rows(path, mode):
    if Path(path).suffix == ".gz":
        return gzip.open(path, mode, compresslevel=1)
    return Path(path).open(mode)


def compile_command(args):
    statement = same_public_statement(load_json(args.statement))
    with ExitStack() as files:
        sink = files.enter_context(open_rows(args.rows, "xb")) if args.rows else None
        arithmetic = args.arithmetic or {
            "ate-paired": "packed-centered",
            "ate-moving-projected": "factored",
            "ate-conic": "min-bits-factored",
            "ate-conic-window": "min-bits-factored",
            "ate-conic-optimized": "min-bits-factored",
            "ate-fused": "centered",
            "ate-moving": "centered",
        }.get(args.pairing, "integer-limbs")
        _, metadata = emit(statement, None, args.pairing, sink, arithmetic)
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
        same_public_statement(load_json(args.statement)),
        witness,
        metadata["pairing"],
        arithmetic=metadata.get("arithmetic", "integer-limbs"),
    )
    if derived != metadata:
        raise ValueError("public layout differs from the pinned compilation")
    with Path(args.witness).open("xb") as f:
        f.write(b.assignment)
    print(f"wrote {b.bits} bits ({len(b.assignment)} bytes)")


def check_command(args):
    from . import factored_bqs

    meta = load_json(args.manifest)
    if meta["format"] not in (FORMAT, factored_bqs.FORMAT) or meta["fr"] != str(R):
        raise ValueError("unexpected BQS format or field")
    data = Path(args.witness).read_bytes()
    n = meta["unknowns"]
    if len(data) != (n + 7) // 8 or (n % 8 and data[-1] >> (n % 8)):
        raise ValueError("invalid Boolean witness length or padding")
    if meta["format"] == factored_bqs.FORMAT:
        with open_rows(args.rows, "rb") as rows:
            proof = factored_bqs.validate_stream(rows, data, meta)
        print(json.dumps(proof))
        return
    shape = hashlib.sha256(b"PVUGC Boolean quadratic rows v1\n")
    count = 0

    def get(atom):
        if atom != (-1, 0) and (atom[0] < 0 or atom[1] <= 0 or atom[0] + atom[1] > n):
            raise ValueError("row references bits outside the statement")
        return bit_value(data, atom)

    with open_rows(args.rows, "rb") as f:
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
    compile_.add_argument(
        "--pairing",
        choices=["tate", "ate", *CENTERED_PAIRINGS],
        default="ate-conic-optimized",
    )
    compile_.add_argument(
        "--arithmetic",
        choices=[
            "integer-limbs",
            "centered",
            "packed-centered",
            "factored",
            "packed-factored",
            "min-bits-factored",
            "narrow-factored",
        ],
    )
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
