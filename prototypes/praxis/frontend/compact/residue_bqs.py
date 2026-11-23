"""Centered foreign-coefficient lowering for exact Boolean rows over BN254 Fr.

The limb coefficient reduction is from Efficient Foreign-Field Arithmetic in
PLONK (ePrint 2025/695, Eq. 2). This backend does its range checks with bits
and certifies equality with both Fr and a power of two, without lookup tables.
It emits the same bit-slice product row format as bqs.Builder.
"""

from functools import lru_cache

from .bqs import Affine, Builder, ONE, P, R, Wire, bit_value

MAX_PRODUCTS = 2047
# Small digits reduce the quotient, subject to the number of products a row can hold.
WIDTHS = (8, 10, 12, 14, 16, 19, 22, 26, 29, 32, 37, 43, 51, 64)


def centered(c, modulus):
    return (c + modulus // 2) % modulus - modulus // 2


@lru_cache(maxsize=4096)
def weighted(c, shift):
    return centered(c << shift, P)


def slices(atom, width):
    if atom == ONE:
        return [(ONE, 0)]
    start, size = atom
    return [
        ((start + shift, min(width, size - shift)), shift)
        for shift in range(0, size, width)
    ]


def add(terms, c, a, b):
    pair = (a, b) if a <= b else (b, a)
    terms[pair] = terms.get(pair, 0) + c


def limits(terms):
    lo = hi = 0
    for c, a, b in terms:
        magnitude = Builder._bound(a) * Builder._bound(b)
        if c < 0:
            lo += c * magnitude
        else:
            hi += c * magnitude
    return lo, hi


def chunks(terms, width):
    groups = {}
    for c, a, b in terms:
        aa = slices(a, width)
        bb = aa if a == b else slices(b, width)
        for x, left in aa:
            for y, right in bb:
                add(groups, weighted(c, left + right), x, y)
    return [(v, a, b) for (a, b), c in groups.items() if (v := centered(c, P))]


def low_terms(terms, bits):
    modulus = 1 << bits
    group = {}
    for c, a, b in terms:

        def low(atom):
            return atom if atom == ONE else (atom[0], min(bits, atom[1]))

        add(group, centered(c, modulus), low(a), low(b))
    return [(v, a, b) for (a, b), c in group.items() if (v := centered(c, modulus))]


def basis(start, width):
    return (start, width) if width else ONE


def quotient_row(terms, start, modulus, lo, hi):
    offset = lo // modulus
    width = (hi // modulus - offset).bit_length()
    row = list(terms)
    if width:
        row.append((-modulus, basis(start, width), ONE))
    if offset:
        row.append((-modulus * offset, ONE, ONE))
    return row, offset, width


class ResidueBuilder(Builder):
    """Use small foreign residues when their product layout fits the public cap."""

    affine_limit = 16
    digit_widths = WIDTHS
    fold_square_bound = False

    def _gate(self, terms, linear, constant, force_zero):
        merged = {}
        for c, a, b in terms:
            for av, aa in self._entries(a):
                for bv, bb in self._entries(b):
                    add(merged, c * av * bv, aa, bb)
        for c, a in linear:
            for av, aa in self._entries(a):
                add(merged, c * av, ONE, aa)
        add(merged, constant, ONE, ONE)
        raw = [(v, a, b) for (a, b), c in merged.items() if (v := centered(c, P))]
        if all(a == b == ONE for _, a, b in raw):
            return super()._gate(terms, linear, constant, force_zero)
        if (
            not force_zero
            and len(raw) <= self.affine_limit
            and all(a == ONE for _, a, b in raw)
        ):
            return Affine(tuple((c, b) for c, _, b in raw))
        get = lambda a: bit_value(self.assignment, a)
        v = sum(c * get(a) * get(b) for c, a, b in raw)
        if force_zero and not self.layout_only and v % P:
            raise ValueError("false base-field equation")
        out_width = 0 if force_zero else P.bit_length()
        if out_width:
            raw.append((-1, ONE, (self.bits, out_width)))
        q_start = self.bits + out_width
        for width in self.digit_widths:
            # Conservative upper bound accounts for all slice products, two
            # offset terms, and the additional carry/offset in the second row.
            def n(a):
                return 1 if a == ONE else (a[1] + width - 1) // width

            def count(a, b):
                x = n(a)
                if self.fold_square_bound and a == b:
                    return x * (x + 1) // 2
                return x * n(b)

            if sum(count(a, b) for _, a, b in raw) + 4 > MAX_PRODUCTS:
                continue
            digits = chunks(raw, width)
            lo, hi = limits(digits)
            native, q_off, q_width = quotient_row(digits, q_start, P, lo, hi)
            nlo, nhi = limits(native)
            # Every Boolean assignment satisfies |E| <= bound; this includes
            # the rounded-up range of the encoded quotient. Require R*2^t>B.
            bound = max(-nlo, nhi)
            t = (bound // R).bit_length()
            if t:
                residue = low_terms(native, t)
                rlo, rhi = limits(residue)
                exact, k_off, k_width = quotient_row(
                    residue, q_start + q_width, 1 << t, rlo, rhi
                )
                elo, ehi = limits(exact)
                exact_bound = max(-elo, ehi)
                if exact_bound >= R or len(exact) > MAX_PRODUCTS:
                    continue
            if len(native) > MAX_PRODUCTS:
                continue

            out = None if force_zero else self.witness(v % P)
            digit_value = sum(c * get(a) * get(b) for c, a, b in digits)
            if q_width:
                self.unsigned(digit_value // P - q_off, q_width)
            self._row(native)
            if t:
                low_value = sum(c * get(a) * get(b) for c, a, b in residue)
                if k_width:
                    self.unsigned(low_value // (1 << t) - k_off, k_width)
                self._row(exact, exact_bound=exact_bound)
            return out

        # Dense folded gates may exceed the product cap or the residual carry
        # range at every width. Bound the fan-in before lowering the sum.
        source = raw[:-1] if out_width else raw
        if len(source) <= 16:
            raise ValueError("no certified digit width for a bounded gate")
        partials = []
        for i in range(0, len(source), 16):
            group = source[i : i + 16]
            val = sum(c * get(a) * get(b) for c, a, b in group)
            part = self.witness(val % P)
            args = [
                (c, 1 if a == ONE else Wire(*a), 1 if b == ONE else Wire(*b))
                for c, a, b in group
            ]
            self.assert_zero(args, [(-1, part)])
            partials.append((1, part))
        return self._gate([], partials, 0, force_zero)


class FineResidueBuilder(ResidueBuilder):
    """Select the narrowest admissible binary digit, folding square symmetry."""

    digit_widths = range(1, 65)
    fold_square_bound = True


class PackedResidueBuilder(FineResidueBuilder):
    """Pack bounded exact rows; call shape() after emitting the last gate."""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.pending = []

    def _row(self, terms, exact_bound=None):
        if exact_bound is None:
            return super()._row(terms)
        if not 0 <= exact_bound < R:
            raise ValueError("uncertified bounded CRT row")
        # The integral residuals satisfy |E_i|<=B_i. Vanishing of
        # E_1+(B_1+1)E_2 mod R implies first equality over the integers if
        # (B_1+1)(B_2+1)-1<R, and then both E_i=0 by reduction mod B_1+1.
        for i, (prev, bound) in enumerate(self.pending):
            radix = bound + 1
            combined = radix * (exact_bound + 1) - 1
            if len(prev) + len(terms) <= MAX_PRODUCTS and combined < R:
                prev.extend((c * radix, a, b) for c, a, b in terms)
                self.pending[i] = (prev, combined)
                return
        if len(self.pending) == 24:
            old, bound = self.pending.pop(0)
            super()._row(old, exact_bound=bound)
        self.pending.append((list(terms), exact_bound))

    def shape(self):
        for terms, bound in self.pending:
            super()._row(terms, exact_bound=bound)
        self.pending.clear()
        return super().shape()
