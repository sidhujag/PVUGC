"""Exact BN254 foreign-field constraints on a packed Boolean witness over Fr.

Each emitted JSON row is a sum of [coefficient, bit_start, width, bit_start,
width] products. A bit slice is the little-endian linear form on those input
bits; (-1,0) denotes the constant one. Rows are equal to zero modulo R.
"""

import hashlib
import json
from dataclasses import dataclass

P = 21888242871839275222246405745257275088696311157297823662689037894645226208583
R = 21888242871839275222246405745257275088548364400416034343698204186575808495617
RADIX_BITS = 96
BASE = 1 << RADIX_BITS
ONE = (-1, 0)


@dataclass(frozen=True)
class Wire:
    start: int
    width: int


@dataclass(frozen=True)
class Affine:
    # Entries are (coefficient, bit slice); ONE carries the integer constant.
    # These are syntax substitutions, never independently assignable advice.
    entries: tuple


def bit_value(data, atom):
    start, width = atom
    if start == -1 and width == 0:
        return 1
    if start < 0 or width <= 0 or start + width > len(data) * 8:
        raise ValueError("invalid bit range in constraint")
    low = start // 8
    high = (start + width + 7) // 8
    return (int.from_bytes(data[low:high], "little") >> (start % 8)) & (
        (1 << width) - 1
    )


def check_row(terms, get, modulus=R):
    return sum(c * get((i, n)) * get((j, m)) for c, i, n, j, m in terms) % modulus == 0


class Builder:
    def __init__(self, sink=None, layout_only=False):
        self.sink = sink
        self.layout_only = layout_only
        self.assignment = bytearray()
        self.bits = self.rows = self.max_products = self.max_limb_residual = 0
        self.digest = hashlib.sha256(b"PVUGC Boolean quadratic rows v1\n")

    def unsigned(self, value, width):
        if width < 1 or not 0 <= value < (1 << width):
            raise ValueError("unsigned witness exceeds its allocation")
        start = self.bits
        self.bits += width
        self.assignment.extend(bytes((self.bits + 7) // 8 - len(self.assignment)))
        low = start // 8
        chunk = (value << (start % 8)).to_bytes(len(self.assignment) - low, "little")
        self.assignment[low] |= chunk[0]
        self.assignment[low + 1 :] = chunk[1:]
        return Wire(start, width)

    def witness(self, value):
        return self.unsigned(int(value) % P, P.bit_length())

    def bit(self, value):
        return self.unsigned(int(value), 1)

    def value(self, arg):
        if isinstance(arg, Wire):
            return bit_value(self.assignment, (arg.start, arg.width))
        if isinstance(arg, Affine):
            return (
                sum(c * bit_value(self.assignment, atom) for c, atom in arg.entries) % P
            )
        return int(arg) % P

    def equal(self, a, b):
        self.assert_zero([], [(1, a), (-1, b)])

    def inverse(self, a):
        v = self.value(a)
        if not v and not self.layout_only:
            raise ValueError("required inverse of zero")
        inv = pow(v, -1, P) if v else 0
        if not isinstance(a, int):
            inv = self.witness(inv)
        self.assert_zero([(1, a, inv)], constant=-1)
        return inv

    def _row(self, terms, exact_bound=None):
        if exact_bound is not None:
            if exact_bound >= R:
                raise ValueError("integer residual may wrap in Fr")
            self.max_limb_residual = max(self.max_limb_residual, exact_bound)
        combined = {}
        for c, a, b in terms:
            pair = (a, b) if a <= b else (b, a)
            combined[pair] = combined.get(pair, 0) + c
        products = [[c, *a, *b] for (a, b), c in sorted(combined.items()) if c % R]
        if not products:
            return
        if not self.layout_only and not check_row(
            products, lambda a: bit_value(self.assignment, a)
        ):
            raise ValueError("unsatisfied Boolean quadratic row")
        row = json.dumps(products, separators=(",", ":")).encode() + b"\n"
        self.digest.update(row)
        if self.sink is not None:
            self.sink.write(row)
        self.rows += 1
        self.max_products = max(self.max_products, len(products))

    @staticmethod
    def _entries(x):
        if isinstance(x, Wire):
            return ((1, (x.start, x.width)),)
        if isinstance(x, Affine):
            return x.entries
        return ((int(x) % P, ONE),)

    @staticmethod
    def _bound(atom):
        return 1 if atom == ONE else (1 << atom[1]) - 1

    @staticmethod
    def _slices(atom):
        if atom == ONE:
            return [ONE]
        start, width = atom
        return [
            (start + k, min(RADIX_BITS, width - k)) for k in range(0, width, RADIX_BITS)
        ]

    def mod(self, terms=(), linear=(), constant=0):
        return self._gate(terms, linear, constant, False)

    def assert_zero(self, terms=(), linear=(), constant=0):
        self._gate(terms, linear, constant, True)

    def _gate(self, terms, linear, constant, force_zero):
        # Fold all public arithmetic before deciding what needs a witness bit.
        summed = {}
        for coeff, a, b in terms:
            for av, aa in self._entries(a):
                for bv, bb in self._entries(b):
                    key = (aa, bb) if aa <= bb else (bb, aa)
                    summed[key] = summed.get(key, 0) + coeff * av * bv
        for coeff, a in linear:
            for v, aa in self._entries(a):
                key = (ONE, aa)
                summed[key] = summed.get(key, 0) + coeff * v
        summed[(ONE, ONE)] = summed.get((ONE, ONE), 0) + constant
        # Signed residues minimize public coefficient sizes without changing Fp.
        polynomial = []
        for (a, b), c in summed.items():
            c = (c + P // 2) % P - P // 2
            if c:
                polynomial.append((c, a, b))
        get = lambda atom: bit_value(self.assignment, atom)
        v = sum(c * get(a) * get(b) for c, a, b in polynomial)
        if all(a == b == ONE for _, a, b in polynomial):
            if force_zero and v % P:
                raise ValueError("impossible fixed public constraint")
            return v % P
        # Inlining a small affine combination costs no witness values or rows.
        # Both admissibility tests depend exclusively on the public syntax.
        if (
            not force_zero
            and len(polynomial) <= 8
            and all(a == ONE and (b == ONE or abs(c) <= 256) for c, a, b in polynomial)
        ):
            return Affine(tuple((c, b) for c, _, b in polynomial))
        if force_zero and v % P and not self.layout_only:
            raise ValueError("false base-field equation")
        output = None if force_zero else self.witness(v % P)
        if output is not None:
            polynomial.append((-1, (output.start, output.width), ONE))
            v -= v % P

        lower = sum(
            min(c, 0) * self._bound(a) * self._bound(b) for c, a, b in polynomial
        )
        upper = sum(
            max(c, 0) * self._bound(a) * self._bound(b) for c, a, b in polynomial
        )
        q_min, q_max = lower // P, upper // P
        q_width = (q_max - q_min).bit_length()
        if q_width:
            q = self.unsigned(v // P - q_min, q_width)
            polynomial.append((-P, (q.start, q.width), ONE))
        if q_min:
            polynomial.append((-P * q_min, ONE, ONE))
        # One native-field equation, then just enough low 2-adic digits that
        # the product R * BASE**k dominates the absolute integer residual.
        self._row(polynomial)
        abs_bound = sum(
            abs(c) * self._bound(a) * self._bound(b) for c, a, b in polynomial
        )
        low_bits = (abs_bound // R).bit_length()
        columns = (low_bits + RADIX_BITS - 1) // RADIX_BITS
        buckets = [[] for _ in range(columns)]
        for coeff, a, b in polynomial:
            mag, sign = abs(coeff), 1 if coeff > 0 else -1
            for h in range(columns):
                if mag == 0:
                    break
                digit, mag = mag % BASE, mag // BASE
                if not digit:
                    continue
                for i, aa in enumerate(self._slices(a)):
                    for j, bb in enumerate(self._slices(b)):
                        if h + i + j < columns:
                            buckets[h + i + j].append((sign * digit, aa, bb))
        for i, bucket in enumerate(buckets):
            radix = BASE
            if i == columns - 1 and low_bits % RADIX_BITS:
                # Only low_bits are needed for the CRT bound. At the terminal
                # digit, throwing away higher bits of each factor preserves
                # the required congruence and shortens the final carry.
                width = low_bits % RADIX_BITS
                radix = 1 << width

                def low(atom, width=width):
                    return (atom[0], min(atom[1], width)) if atom != ONE else ONE

                bucket = [
                    ((c + radix // 2) % radix - radix // 2, low(a), low(b))
                    for c, a, b in bucket
                ]
            total = sum(c * get(a) * get(b) for c, a, b in bucket)
            lo = sum(min(c, 0) * self._bound(a) * self._bound(b) for c, a, b in bucket)
            hi = sum(max(c, 0) * self._bound(a) * self._bound(b) for c, a, b in bucket)
            cmin, cmax = lo // radix, hi // radix
            width = (cmax - cmin).bit_length()
            carry = self.unsigned(total // radix - cmin, width) if width else None
            if carry:
                atom = (carry.start, carry.width)
                bucket.append((-radix, atom, ONE))
                if i + 1 < columns:
                    buckets[i + 1].append((1, atom, ONE))
            if cmin:
                bucket.append((-radix * cmin, ONE, ONE))
                if i + 1 < columns:
                    buckets[i + 1].append((cmin, ONE, ONE))
            max_abs = sum(
                abs(c) * self._bound(a) * self._bound(b) for c, a, b in bucket
            )
            self._row(bucket, exact_bound=max_abs)
        return output

    def shape(self):
        return {
            "unknowns": self.bits,
            "constraints": self.rows,
            "max_products": self.max_products,
            "max_limb_residual_bits": self.max_limb_residual.bit_length(),
            "digest": self.digest.hexdigest(),
        }
