"""Structured affine-product form for centered Boolean CRT rows over BN254 Fr.

Each row stores its coefficient recipe, not an expanded limb-product matrix.
The entry for a product of digit i of x and digit j of y depends on i+j.
Kronecker substitution computes all digit diagonals with one integer multiply.
The sparse wire-graph cover bounds the number of exported affine products.
"""

import hashlib
import json
import tempfile
from collections import defaultdict
from functools import lru_cache

from .bqs import ONE, Affine, Builder, P, R, bit_value
from .residue_bqs import MAX_PRODUCTS, add, centered

VERSION = b"PVUGC affine-product BQS v2\n"
FORMAT = "pvugc-affine-product-bqs-v2"


def count(atom, w):
    return 1 if tuple(atom) == ONE else (atom[1] + w - 1) // w


@lru_cache(maxsize=8192)
def coefficients(c, n, w, t):
    a = centered(c, P)
    out = []
    for _ in range(n):
        out.append(centered(a, 1 << t) if t else a)
        a = centered(a << w, P)
    return tuple(out)


@lru_cache(maxsize=16384)
def embed(v, size, w, t):
    if not size:
        return 1
    limb = (1 << w) - 1
    clipped = (1 << min(w, t)) - 1 if t else limb
    packed = 0
    spacing = 2 * w + ((254 + w - 1) // w).bit_length()
    for i in range((size + w - 1) // w):
        packed |= (v & clipped) << (i * spacing)
        v >>= w
    return packed


@lru_cache(maxsize=4096)
def diagonals(x, y, n, w):
    z = x * y
    shift = 2 * w + ((254 + w - 1) // w).bit_length()
    mask = (1 << shift) - 1
    digits = []
    for _ in range(n):
        digits.append(z & mask)
        z >>= shift
    return tuple(digits)


def weight(c, x, y, w, t, get):
    x, y = tuple(x), tuple(y)
    n = count(x, w) + count(y, w) - 1
    a, b = (embed(get(u), u[1], w, t) for u in (x, y))
    coeff = coefficients(c, n, w, t)
    return coeff, diagonals(a, b, n, w)


@lru_cache(maxsize=8192)
def term_limits(c, nx, ny, w, t):
    x, y = ((0, n) if n else ONE for n in (nx, ny))
    coeff, mag = weight(c, x, y, w, t, Builder._bound)
    lo = hi = 0
    for k, m in zip(coeff, mag):
        if k < 0:
            lo += k * m
        else:
            hi += k * m
    return lo, hi


def measure(raw, w, t=0):
    # All-one limbs maximize each digit diagonal. Correlations between
    # diagonals may safely be ignored for these signed interval bounds.
    lo = hi = 0
    for c, x, y in raw:
        a, b = term_limits(c, x[1], y[1], w, t)
        lo += a
        hi += b
    return lo, hi


def dot(raw, w, t, get):
    v = 0
    for c, x, y in raw:
        coeff, scores = weight(c, x, y, w, t, get)
        v += sum(k * m for k, m in zip(coeff, scores))
    return v


def cover(raw, w):
    # Each digit of a chosen wire supplies one left factor for ALL incident
    # terms. Self-products mandate that vertex. All linear terms use left 1.
    edges = {
        (tuple(x), tuple(y)) for c, x, y in raw if tuple(x) != ONE and tuple(y) != ONE
    }
    taken = {x for x, y in edges if x == y}
    edges = {e for e in edges if not taken.intersection(e)}
    while edges:
        degree = defaultdict(int)
        for x, y in edges:
            degree[x] += 1
            degree[y] += 1
        chosen = min(degree, key=lambda x: (-(degree[x] * 65536 // count(x, w)), x))
        taken.add(chosen)
        edges = {e for e in edges if chosen not in e}
    return taken


def plan(raw, w, chosen):
    fmax = 1 + sum(count(a, w) for a in chosen)
    if fmax > MAX_PRODUCTS:
        return None
    lo, hi = measure(raw, w)
    q0 = lo // P
    qw = (hi // P - q0).bit_length()
    upper = (1 << qw) - 1
    B = max(-lo + P * (q0 + upper), hi - P * q0)
    t = (B // R).bit_length()
    k0 = kw = bound = 0
    if t:
        rlo, rhi = measure(raw, w, t)
        modulus = 1 << t
        c0 = centered(-P * q0, modulus)
        cq = centered(-P, modulus)
        m = (1 << min(qw, t)) - 1
        rlo += c0 + min(0, cq * m)
        rhi += c0 + max(0, cq * m)
        k0 = rlo // modulus
        kw = (rhi // modulus - k0).bit_length()
        bound = max(-rlo + modulus * (k0 + (1 << kw) - 1), rhi - modulus * k0)
        if bound >= R:
            return None
    return [q0, qw, t, k0, kw, bound, fmax]


def _clip_atom(a, t):
    return a if tuple(a) == ONE or not t else (a[0], min(t, a[1]))


def affine_products(row):
    """Materialize the certified public rank-one decomposition for ONE row.

    Yields (single bit slice, [(coefficient, bit slice)]) pairs. The first
    coordinate may be the constant one. No advice or mutable state is used.
    """
    if row[0] == "pack":
        grouped = defaultdict(list)
        for multiplier, subrow in row[1]:
            for left, right in affine_products(subrow):
                grouped[left].extend((multiplier * c, a) for c, a in right)
        yield from sorted(grouped.items())
        return
    if row[0] == "plain":
        grouped = defaultdict(list)
        for c, i, n, j, m in row[1]:
            grouped[(i, n)].append((c, (j, m)))
        yield from sorted(grouped.items())
        return
    _, w, t, raw, q0, qa, k0, ka = row
    raw = [(c, tuple(a), tuple(b)) for c, a, b in raw]
    chosen = cover(raw, w)
    rows = defaultdict(list)
    for left in factor_atoms(row):
        rows[left] = []

    def digits(a):
        if a == ONE:
            return [(0, ONE)]
        return [
            (j // w, _clip_atom((a[0] + j, min(w, a[1] - j)), t))
            for j in range(0, a[1], w)
        ]

    for c, a, b in raw:
        if a != ONE and b != ONE and a not in chosen:
            a, b = b, a
        coeff = coefficients(c, count(a, w) + count(b, w) - 1, w, t)
        for i, x in digits(a):
            for j, y in digits(b):
                k = coeff[i + j]
                if k:
                    rows[x].append((k, y))
    q = tuple(qa) if qa else None
    k = tuple(ka) if ka else None
    if t:
        radix = 1 << t
        const = centered(-P * q0, radix) - radix * k0
        if q:
            rows[ONE].append((centered(-P, radix), _clip_atom(q, t)))
        if k:
            rows[ONE].append((-radix, k))
    else:
        const = -P * q0
        if q:
            rows[ONE].append((-P, q))
    if const:
        rows[ONE].append((const, ONE))
    yield from sorted(rows.items())


@lru_cache(maxsize=1024)
def _sliding_coefficients(c, n, ny, w, t):
    # A signed Toeplitz matrix times an unsigned digit vector. A uniform
    # offset makes all coefficients nonnegative, permitting integer Kronecker
    # multiplication; subtract its dot product with the digit vector after.
    coeff = coefficients(c, n, w, t)
    bias = max(0, -min(coeff))
    byte_width = max(
        1, ((max(coeff) + bias).bit_length() + w + ny.bit_length() + 7) // 8
    )
    packed = int.from_bytes(
        b"".join((z + bias).to_bytes(byte_width, "little") for z in coeff), "little"
    )
    return packed, byte_width, bias


@lru_cache(maxsize=2048)
def _reversed_digits(v, n, w, t, byte_width):
    if n == 0:
        return 1, 1
    mask = (1 << min(t or w, w)) - 1
    digits = [(v >> i) & mask for i in range(0, n, w)]
    return int.from_bytes(
        b"".join(z.to_bytes(byte_width, "little") for z in reversed(digits)), "little"
    ), sum(digits)


def _right_values(row, get):
    if row[0] == "pack":
        out = defaultdict(int)
        for m, subrow in row[1]:
            for a, v in _right_values(subrow, get).items():
                out[a] += m * v
        return out
    if row[0] == "plain":
        vals = defaultdict(int)
        for c, i, n, j, m in row[1]:
            vals[(i, n)] += c * get((j, m))
        return vals
    _, w, t, raw, q0, qa, k0, ka = row
    chosen = cover(raw, w)
    vals = {a: 0 for a in factor_atoms(row)}
    for c, x, y in raw:
        x, y = tuple(x), tuple(y)
        if x != ONE and y != ONE and x not in chosen:
            x, y = y, x
        nx, ny = count(x, w), count(y, w)
        packed, width, bias = _sliding_coefficients(c, nx + ny - 1, ny, w, t)
        reverse, ysum = _reversed_digits(get(y), y[1], w, t, width)
        # At diagonal ny−1+i, convolution with the reversed y stores
        # exactly sum_j (c[i+j]+bias)*y[j]. No lane can carry into its neighbor.
        buf = (packed * reverse).to_bytes((nx + 2 * ny - 2) * width, "little")
        for i in range(nx):
            lane = (ny - 1 + i) * width
            # Each input wire is split into disjoint base-2^w slices. The low
            # CRT row truncates an individual slice if its width exceeds t.
            key = (
                ONE if x == ONE else _clip_atom((x[0] + i * w, min(w, x[1] - i * w)), t)
            )
            vals[key] += (
                int.from_bytes(buf[lane : lane + width], "little") - bias * ysum
            )
    q = get(tuple(qa)) if qa else 0
    if t:
        mod = 1 << t
        vals[ONE] += (
            centered(-P * q0, mod)
            + centered(-P, mod) * (q % mod)
            - mod * (k0 + (get(tuple(ka)) if ka else 0))
        )
    else:
        vals[ONE] -= P * (q0 + q)
    return vals


def instantiated_factors(row, get):
    """Return the value of each named affine factor, as in affine_products().

    Uses a sliding dot product per left digit. This evaluates the actual
    factors individually and independently of the total-diagonal evaluator.
    """
    vals = _right_values(row, get)
    for a in sorted(vals):
        yield a, get(a) % R, vals[a] % R


def _boolean_linear(slices):
    constant = 0
    bits = defaultdict(int)
    for c, a in slices:
        if tuple(a) == ONE:
            constant += c
            continue
        start, n = a
        for i in range(n):
            bits[start + i] += c << i
    return constant % R, [(index, v % R) for index, v in sorted(bits.items()) if v % R]


def praxis_forms(row, nbits):
    """Yield actual affine forms (constant, sparse bit-index/Fr-coefficient list).

    The returned pair represents L(a)*R(a) on the original Boolean inputs.
    Sum the pairs for the row. Digits, diagonal values, and the factor cover are
    public notation and introduce no Boolean unknowns. Authenticate the complete
    stream against the trusted compiled manifest before calling this exporter.
    """
    inspect_row(row, nbits)
    for a, right in affine_products(row):
        yield _boolean_linear([(1, a)]), _boolean_linear(right)


def evaluate(row, get):
    if row[0] == "pack":
        return sum(m * evaluate(subrow, get) for m, subrow in row[1])
    if row[0] == "plain":
        return sum(c * get((i, n)) * get((j, m)) for c, i, n, j, m in row[1])
    _, w, t, raw, q0, q, k0, k = row
    v = dot(raw, w, t, get)
    z = get(tuple(q)) if q else 0
    if not t:
        return v - P * (q0 + z)
    radix = 1 << t
    return (
        v
        + centered(-P * q0, radix)
        + centered(-P, radix) * (z % radix)
        - radix * (k0 + (get(tuple(k)) if k else 0))
    )


class FactoredBuilder(Builder):
    affine_limit = 16
    target_products = MAX_PRODUCTS

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.digest = hashlib.sha256(VERSION)
        self.public_bytes = 0

    def shape(self):
        return dict(super().shape(), recipe_bytes=self.public_bytes)

    def record(self, row, fmax):
        if fmax > MAX_PRODUCTS:
            raise ValueError("affine-product cap exceeded")
        s = json.dumps(row, separators=(",", ":")).encode() + b"\n"
        self.digest.update(s)
        self.public_bytes += len(s)
        self.rows += 1
        self.max_products = max(self.max_products, fmax)
        if self.sink is not None:
            self.sink.write(s)

    def bounded(self, row, fmax, bound):
        self.max_limb_residual = max(self.max_limb_residual, bound)
        self.record(row, fmax)

    def _row(self, terms, exact_bound=None):
        if exact_bound is not None:
            if exact_bound >= R:
                raise ValueError("direct integer row wraps in Fr")
            self.max_limb_residual = max(self.max_limb_residual, exact_bound)
        row = ["plain", [[c, *a, *b] for c, a, b in terms if c % R]]
        if row[1]:
            if (
                not self.layout_only
                and evaluate(row, lambda a: bit_value(self.assignment, a)) % R
            ):
                raise ValueError("invalid direct Fr row")
            n = len({(i, n) for c, i, n, j, m in row[1]})
            if exact_bound is None:
                # A direct native row can also be objectively bounded without
                # a supplied certificate. Reflect that finite bound in shape.
                _, actual_bound = inspect_row(row, self.bits)
                if actual_bound is not None:
                    self.max_limb_residual = max(self.max_limb_residual, actual_bound)
                self.record(row, n)
            else:
                self.bounded(row, n, exact_bound)

    def _gate(self, terms, linear, constant, force_zero):
        merge = {}
        for c, x, y in terms:
            for d, a in self._entries(x):
                for e, h in self._entries(y):
                    add(merge, c * d * e, a, h)
        for c, x in linear:
            for d, a in self._entries(x):
                add(merge, c * d, a, ONE)
        add(merge, constant, ONE, ONE)
        raw = [
            (c, a, h) for (a, h), v in sorted(merge.items()) if (c := centered(v, P))
        ]
        if all(a == h == ONE for _, a, h in raw):
            return super()._gate(terms, linear, constant, force_zero)
        if (
            not force_zero
            and len(raw) <= self.affine_limit
            and all(a == ONE for _, a, h in raw)
        ):
            return Affine(tuple((c, h) for c, a, h in raw))
        get = lambda a: bit_value(self.assignment, a)
        v = sum(c * get(a) * get(h) for c, a, h in raw)
        if force_zero and not self.layout_only and v % P:
            raise ValueError("false Fp equation")
        out = None if force_zero else self.witness(v % P)
        if out:
            raw.append((-1, ONE, (out.start, out.width)))
        for w in range(1, 65):
            result = plan(raw, w, cover(raw, w))
            if result is not None and result[-1] <= self.target_products:
                break
        else:
            raise ValueError("rank or CRT range exceeds this structured backend")
        q0, qw, t, k0, kw, bound, fmax = result
        j = dot(raw, w, 0, get)
        z = j // P - q0
        q = self.unsigned(z, qw) if qw else None
        qa = (q.start, q.width) if q else None
        native = ["digit", w, 0, raw, q0, qa, 0, None]
        if not self.layout_only and (j - P * (z + q0)) % R:
            raise ValueError("invalid first CRT row")
        self.record(native, fmax)
        if t:
            radix = 1 << t
            jlo = (
                dot(raw, w, t, get)
                + centered(-P * q0, radix)
                + centered(-P, radix) * (z % radix)
            )
            k = self.unsigned(jlo // radix - k0, kw) if kw else None
            ka = (k.start, k.width) if k else None
            low = ["digit", w, t, raw, q0, qa, k0, ka]
            if not self.layout_only and jlo % radix:
                raise ValueError("invalid low CRT row")
            self.bounded(low, fmax, bound)
        return out


def factor_atoms(row):
    """A public upper bound on distinct left forms, without dense expansion."""
    if row[0] == "plain":
        return {(x, n) for c, x, n, y, m in row[1]}
    _, w, t, raw, _, _, _, _ = row
    result = {ONE}
    for x, n in cover(raw, w):
        result.update(_clip_atom((x + i, min(w, n - i)), t) for i in range(0, n, w))
    return result


class PackedFactoredBuilder(FactoredBuilder):
    """Share left factors across mixed-radix packed, bounded integer rows."""

    # Leave room for at least two disjoint ordinary low rows in most bins.
    target_products = 1023

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.pending = []

    def bounded(self, row, fmax, bound):
        if bound >= R:
            raise ValueError("uncertified integral packing bound")
        keys = factor_atoms(row)
        if len(keys) > fmax:
            raise ValueError("invalid factor certificate")
        for i, (parts, prev, forms) in enumerate(self.pending):
            base = prev + 1
            combined = base * (bound + 1) - 1
            if combined >= R:
                continue
            merged = forms | keys
            if len(merged) > MAX_PRODUCTS:
                continue
            parts.append((base, row))
            self.pending[i] = (parts, combined, merged)
            return
        if len(self.pending) >= 24:
            self._flush_one(self.pending.pop(0))
        self.pending.append(([(1, row)], bound, keys))

    def _flush_one(self, bin):
        parts, bound, keys = bin
        row = parts[0][1] if len(parts) == 1 else ["pack", parts]
        self.max_limb_residual = max(self.max_limb_residual, bound)
        self.record(row, len(keys))

    def shape(self):
        for bin in self.pending:
            self._flush_one(bin)
        self.pending.clear()
        return super().shape()


class MinBitsFactoredBuilder(PackedFactoredBuilder):
    """Retain the narrowest digits while folding the bounded low CRT rows."""

    target_products = MAX_PRODUCTS


def _int(v):
    if type(v) is not int:
        raise ValueError("expected an integer in the factored row")
    return v


def _array(v, n):
    if not isinstance(v, (list, tuple)) or len(v) != n:
        raise ValueError("invalid array in the factored row")
    return v


def _atom(a, bits, allow_one=True):
    x, n = map(_int, _array(a, 2))
    if allow_one and (x, n) == ONE:
        return ONE
    if x < 0 or not 1 <= n <= 254 or x + n > bits:
        raise ValueError("invalid or overflowing bit slice")
    return x, n


def inspect_row(row, bits, nested=False):
    """Independently recompute a row's public rank and integer certificates.

    Returns (set of possible left factors, exact integral bound or None).
    Native congruences may not be mixed into a signed bounded-row pack.
    """
    if not isinstance(row, (list, tuple)) or not row:
        raise ValueError("empty or malformed factored row")
    tag = row[0]
    if tag == "pack":
        _array(row, 2)
        if nested or not isinstance(row[1], (list, tuple)) or len(row[1]) < 2:
            raise ValueError("malformed or recursive row pack")
        bound = 0
        forms = set()
        for elem in row[1]:
            m, entry = _array(elem, 2)
            if _int(m) != bound + 1:
                raise ValueError("incorrect mixed-radix multiplier")
            left, sub = inspect_row(entry, bits, True)
            if sub is None:
                raise ValueError("unbounded native row included in an integral pack")
            bound = m * (sub + 1) - 1
            forms.update(left)
            if bound >= R or len(forms) > MAX_PRODUCTS:
                raise ValueError("mixed-radix integer or rank overflow")
        return forms, bound
    if tag == "plain":
        _array(row, 2)
        if not isinstance(row[1], (list, tuple)) or not row[1]:
            raise ValueError("empty plain row")
        forms = set()
        lo = hi = 0
        for term in row[1]:
            c, i, n, j, m = _array(term, 5)
            _int(c)
            x, y = _atom((i, n), bits), _atom((j, m), bits)
            forms.add(x)
            mag = Builder._bound(x) * Builder._bound(y)
            lo += min(c, 0) * mag
            hi += max(c, 0) * mag
        bound = max(-lo, hi)
        if len(forms) > MAX_PRODUCTS or nested and bound >= R:
            raise ValueError("plain row exceeds its certified limits")
        return forms, bound if bound < R else None
    if tag != "digit":
        raise ValueError("unknown factored BQS row tag")
    _, w, t, source, q0, qa, k0, ka = _array(row, 8)
    if not 1 <= _int(w) <= 64 or not 0 <= _int(t) <= 254:
        raise ValueError("invalid digit width or truncated modulus size")
    if not isinstance(source, (list, tuple)) or not source:
        raise ValueError("missing digit row source terms")
    raw = []
    seen = set()
    for term in source:
        c, x, y = _array(term, 3)
        if not -P // 2 < _int(c) <= P // 2 or not c:
            raise ValueError("invalid centered coefficient")
        x, y = _atom(x, bits), _atom(y, bits)
        if x > y or (x, y) in seen:
            raise ValueError("noncanonical or duplicated source product")
        seen.add((x, y))
        raw.append((c, x, y))
    result = plan(raw, w, cover(raw, w))
    if result is None:
        raise ValueError("uncertified digit row")
    off, qw, low, koff, kw, bound, fmax = result
    q = _atom(qa, bits, False) if qa is not None else None
    k = _atom(ka, bits, False) if ka is not None else None
    end = max(a[0] + a[1] for c, x, y in raw for a in (x, y))
    if q and q[0] < end or k and (k[0] < end or q and k[0] != q[0] + q[1]):
        raise ValueError("aliased or misordered quotient and carry slices")
    if _int(q0) != off or (q[1] if q else 0) != qw:
        raise ValueError("incorrect foreign quotient offset or width")
    if (not t and (k is not None or _int(k0) != 0)) or (
        t and (t != low or _int(k0) != koff or (k[1] if k else 0) != kw)
    ):
        raise ValueError("incorrect low residual offset or width")
    forms = factor_atoms(row)
    if len(forms) > fmax:
        raise ValueError("incorrect certified affine-product rank")
    return forms, bound if t else None


def validate_stream(stream, assignment, manifest):
    """Authenticate a full compiled stream before parsing, verify, and decode.

    The caller pins the manifest to a public, proof-independent compilation of
    the intended fixed statement. A digest supplied by a prover cannot by
    itself authenticate that statement.
    """
    if manifest.get("format") != FORMAT or manifest.get("fr") != str(R):
        raise ValueError("wrong factored BQS manifest or scalar field")
    n = _int(manifest["unknowns"])
    nb = _int(manifest["recipe_bytes"])
    rows = _int(manifest["constraints"])
    declared = _int(manifest["max_products"])
    if n <= 0 or nb <= 0 or rows <= 0 or not 1 <= declared <= MAX_PRODUCTS:
        raise ValueError("invalid trusted manifest sizes")
    if len(assignment) != (n + 7) // 8 or n % 8 and assignment[-1] >> (n % 8):
        raise ValueError("invalid Boolean witness length or padding")
    digest = hashlib.sha256(VERSION)
    with tempfile.SpooledTemporaryFile(max_size=1 << 23) as data:
        used = 0
        while block := stream.read(min(65536, nb - used + 1)):
            used += len(block)
            if used > nb:
                raise ValueError("row stream exceeds pinned byte size")
            digest.update(block)
            data.write(block)
        if used != nb or digest.hexdigest() != manifest.get("digest"):
            raise ValueError("row stream differs from the pinned compilation")
        data.seek(0)
        observed = certified = largest = 0
        get = lambda a: bit_value(assignment, a)
        for observed, line in enumerate(data, 1):
            entry = json.loads(line)
            forms, bound = inspect_row(entry, n)
            certified = max(certified, len(forms))
            if bound is not None:
                largest = max(largest, bound.bit_length())
            if evaluate(entry, get) % R:
                raise ValueError(f"unsatisfied factored row {observed}")
        if (
            observed != rows
            or certified > declared
            or largest > _int(manifest["max_limb_residual_bits"])
        ):
            raise ValueError(
                "row count, rank or integral bound exceeds pinned manifest"
            )
    handles = manifest["coordinates"]

    def coordinate(key):
        a = _atom(handles[key], n, False)
        if a[1] != P.bit_length():
            raise ValueError("invalid proof-coordinate width")
        return str(get(a) % P)

    return {
        "a": {"x": coordinate("ax"), "y": coordinate("ay")},
        "b": {
            "x": [coordinate("bx0"), coordinate("bx1")],
            "y": [coordinate("by0"), coordinate("by1")],
        },
        "c": {"x": coordinate("cx"), "y": coordinate("cy")},
    }
