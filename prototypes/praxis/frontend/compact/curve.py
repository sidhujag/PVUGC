"""Fixed-statement reduced Tate pairing relation for a BN254 Groth16 proof.

Fp² coordinates are (real, imaginary) with i²=-1. The sextic twist sends
(x,y) to (xW²,yW³) where W⁶=9+i. The variable proof points, including
infinity in gnark's all-zero affine convention, are checked inside the BQS.
"""

from functools import lru_cache

from .tower import P, R, fp12_mul, fp12_residue, fp12_square

G1 = (1, 2)
G2 = (
    (
        10857046999023057135944570762232829481370756359578518086990519993285655852781,
        11559732032986387107991004021392285783925812861821192530917403151452391805634,
    ),
    (
        8495653923123431417604973247489272438418190587263600148770280649306958101930,
        4082367875863433681332203403145435568316851327593401208105741076214120093531,
    ),
)
ONE12 = (1,) + (0,) * 11


def mod(b, terms=(), linear=(), constant=0):
    if b is None or (
        all(isinstance(x, int) and isinstance(y, int) for _, x, y in terms)
        and all(isinstance(x, int) for _, x in linear)
    ):
        return (
            sum(k * x * y for k, x, y in terms)
            + sum(k * x for k, x in linear)
            + constant
        ) % P
    return b.mod(terms, linear, constant)


def zero(b, terms=(), linear=(), constant=0):
    if b is None or (
        all(isinstance(x, int) and isinstance(y, int) for _, x, y in terms)
        and all(isinstance(x, int) for _, x in linear)
    ):
        if mod(None, terms, linear, constant):
            raise ValueError("false BN254 relation")
    else:
        b.assert_zero(terms, linear, constant)


def value(b, x):
    return x if isinstance(x, int) else b.value(x)


def neg(b, x):
    return mod(b, linear=[(-1, x)])


def mul2(b, a, c):
    return (
        mod(b, [(1, a[0], c[0]), (-1, a[1], c[1])]),
        mod(b, [(1, a[0], c[1]), (1, a[1], c[0])]),
    )


def pow2(a, n):
    y = (1, 0)
    while n:
        if n & 1:
            y = mul2(None, y, a)
        a = mul2(None, a, a)
        n >>= 1
    return y


def subtract2(b, a, c):
    return tuple(mod(b, linear=[(1, x), (-1, y)]) for x, y in zip(a, c))


def inverse_nat2(a):
    norm = (a[0] * a[0] + a[1] * a[1]) % P
    if norm == 0:
        raise ValueError("zero twist denominator")
    inv = pow(norm, -1, P)
    return a[0] * inv % P, -a[1] * inv % P


def slope2(b, p, q, doubling):
    x, y = p
    u, v = q
    if doubling:
        top = mul2(b, x, x)
        numerator = tuple(mod(b, linear=[(3, t)]) for t in top)
        denominator = tuple(mod(b, linear=[(2, t)]) for t in y)
    else:
        numerator = subtract2(b, v, y)
        denominator = subtract2(b, u, x)
    native_den = tuple(value(b, z) for z in denominator)
    native_num = tuple(value(b, z) for z in numerator)
    if all(isinstance(z, int) for z in numerator + denominator):
        return mul2(None, native_num, inverse_nat2(native_den))
    # Slope as an advice pair. Constrain the multiplication and nonzero
    # denominator separately to cover exceptional points outside G2.
    norm = mod(
        b, [(1, denominator[0], denominator[0]), (1, denominator[1], denominator[1])]
    )
    b.inverse(norm)
    native = mul2(None, native_num, inverse_nat2(native_den))
    s = tuple(b.witness(k) for k in native)
    d, e = denominator
    zero(b, [(1, s[0], d), (-1, s[1], e)], [(-1, numerator[0])])
    zero(b, [(1, s[0], e), (1, s[1], d)], [(-1, numerator[1])])
    return s


def step2(b, p, q, doubling):
    return step2_at_slope(b, p, q, slope2(b, p, q, doubling))


def step2_at_slope(b, p, q, slope):
    x, y = p
    u, _ = q
    s, t = slope
    xx = (
        mod(b, [(1, s, s), (-1, t, t)], [(-1, x[0]), (-1, u[0])]),
        mod(b, [(2, s, t)], [(-1, x[1]), (-1, u[1])]),
    )
    dx, dy = subtract2(b, x, xx)
    yy = (
        mod(b, [(1, s, dx), (-1, t, dy)], [(-1, y[0])]),
        mod(b, [(1, s, dy), (1, t, dx)], [(-1, y[1])]),
    )
    return xx, yy


def correct_g1(b, p):
    x, y = p
    square = mod(b, [(1, x, x)])
    zero(b, [(1, y, y), (-1, x, square)], constant=-3)


@lru_cache(maxsize=1)
def twist_constants():
    xi = (9, 1)
    b2 = mul2(None, (3, 0), inverse_nat2(xi))
    return b2, pow2(xi, (P - 1) // 3), pow2(xi, (P - 1) // 2)


def on_twist(b, q):
    x, y = q
    b2, _, _ = twist_constants()
    square = mul2(b, x, x)
    cube = mul2(b, x, square)
    zero(b, [(1, y[0], y[0]), (-1, y[1], y[1])], [(-1, cube[0])], -b2[0])
    zero(b, [(2, y[0], y[1])], [(-1, cube[1])], -b2[1])


def correct_g2(b, q):
    on_twist(b, q)
    x, y = q
    _, fx, fy = twist_constants()
    # p−r is the Frobenius eigenvalue on G2 reduced modulo r. The
    # characteristic polynomial at p−r is exactly r since t=p+1−r.
    # Thus ψ(Q)=[p−r]Q implies [r]Q=0, even for a hostile on-twist input.
    acc = q
    for bit in bin(P - R)[3:]:
        acc = step2(b, acc, acc, True)
        if bit == "1":
            acc = step2(b, acc, q, False)
    conjugate = lambda z: (z[0], neg(b, z[1]))
    eigen = (mul2(b, conjugate(x), fx), mul2(b, conjugate(y), fy))
    for a, c in zip(acc, eigen):
        for v, w in zip(a, c):
            zero(b, linear=[(1, v), (-1, w)])


def step1(b, p, q, doubling):
    x, y = p
    u, v = q
    if doubling:
        numerator, denominator = 3 * value(b, x) ** 2, 2 * value(b, y)
    else:
        numerator, denominator = value(b, v) - value(b, y), value(b, u) - value(b, x)
    if denominator % P == 0:
        raise ValueError("unexpected G1 divisor in finite scalar prefix")
    slope = numerator * pow(denominator, -1, P) % P
    if not all(isinstance(z, int) for z in p + q):
        slope = b.witness(slope)
    if doubling:
        zero(b, [(2, y, slope), (-3, x, x)])
    else:
        zero(b, [(1, u, slope), (-1, x, slope)], [(1, y), (-1, v)])
    newx = mod(b, [(1, slope, slope)], [(-1, x), (-1, u)])
    newy = mod(b, [(1, slope, x), (-1, slope, newx)], [(-1, y)])
    return (newx, newy), slope


def line(b, p, slope, q):
    x, y = p
    (x0, x1), (y0, y1) = q
    # At Qtwist the line is Qy W³ - slope Qx W² + slope*x - y.
    # Replace i by W⁶-9 to get the flat degree-12 power basis.
    values = [0] * 12
    values[0] = mod(b, [(1, slope, x)], linear=[(-1, y)])
    values[2] = mod(b, [(-1, slope, x0), (9, slope, x1)])
    values[8] = mod(b, [(-1, slope, x1)])
    values[3] = mod(b, linear=[(1, y0), (-9, y1)])
    values[9] = y1
    return tuple(values)


def miller(b, pairs):
    # Inputs are finite points in G1 and G2. Every intermediate G1 scalar
    # prefix is strictly between 0 and r. The terminal vertical line and all
    # vertical denominators are nonzero Fp⁶ elements, killed by reduction.
    pairs = tuple(pairs)
    if not pairs:
        return ONE12
    starts = tuple(p for p, _ in pairs)
    states = list(starts)
    out = ONE12
    bits = bin(R)[3:]
    for idx, bit in enumerate(bits):
        out = fp12_square(b, out)
        for j, (_, q) in enumerate(pairs):
            p = states[j]
            states[j], s = step1(b, p, p, True)
            out = fp12_mul(b, out, line(b, p, s, q))
        if bit == "1" and idx != len(bits) - 1:
            for j, (_, q) in enumerate(pairs):
                p = states[j]
                states[j], s = step1(b, p, starts[j], False)
                out = fp12_mul(b, out, line(b, p, s, q))
    return out


def g1(coords):
    return int(coords["x"]), int(coords["y"])


def g2(coords):
    return tuple(map(int, coords["x"])), tuple(map(int, coords["y"]))


def private_point(b, point, generator, check):
    # Canonical decoder maps residues modulo p to coordinates. Byte-level
    # canonicality is checked by the SP1 parser when reading witness bytes.
    is_g2 = isinstance(point[0], tuple)
    flat = tuple(v for pair in point for v in pair) if is_g2 else point
    gen = tuple(v for pair in generator for v in pair) if is_g2 else generator
    if any(v < 0 or v >= P for v in flat):
        raise ValueError("noncanonical proof point coordinate")
    infinity = not any(flat)
    flag = int(infinity) if b is None else b.bit(int(infinity))
    wires = flat if b is None else tuple(b.witness(v) for v in flat)
    safe = []
    for coordinate, replacement in zip(wires, gen):
        zero(b, [(1, flag, coordinate)])
        safe.append(mod(b, linear=[(1, coordinate), (replacement, flag)]))
    safe = (tuple(safe[:2]), tuple(safe[2:])) if is_g2 else tuple(safe)
    check(b, safe)
    return wires, safe, flag


def choose(b, flag, when_set, otherwise):
    return mod(b, [(1, flag, when_set), (-1, flag, otherwise)], linear=[(1, otherwise)])


def opposite(p):
    return p[0], (-p[1]) % P


@lru_cache(maxsize=16)
def constant_miller(p, q):
    if not any(p) or not any(q[0] + q[1]):
        return ONE12
    return miller(None, [(p, q)])


def prepare(b, statement, proof):
    """Emit a deterministic BQS shape for a fixed key and public input.

    Returns handles to the proof's canonical-coordinate residues in A,B,C
    order. All infinity choices are private; no shape specialization on them.
    """
    a, sa, fa = private_point(b, g1(proof["a"]), G1, correct_g1)
    bb, sb, fb = private_point(b, g2(proof["b"]), G2, correct_g2)
    c, sc, fc = private_point(b, g1(proof["c"]), G1, correct_g1)
    disabled = mod(b, [(-1, fa, fb)], linear=[(1, fa), (1, fb)])
    # Force the same known substitute pair even if just A or B is infinity.
    pa = tuple(choose(b, disabled, g, v) for v, g in zip(sa, G1))
    qb = tuple(
        tuple(choose(b, disabled, g, v) for v, g in zip(component, gen))
        for component, gen in zip(sb, G2)
    )
    delta = g2(statement["delta"])
    pairs = [(pa, qb)]
    delta_finite = any(delta[0] + delta[1])  # a fixed-key choice
    if delta_finite:
        pairs.append(((sc[0], neg(b, sc[1])), delta))
    fixed_pairs = [
        (opposite(g1(statement["L"])), g2(statement["gamma"])),
        (opposite(g1(statement["alpha"])), g2(statement["beta"])),
    ]
    disabled_pairs = [(disabled, (opposite(G1), G2))]
    if delta_finite:
        disabled_pairs.append((fc, (G1, delta)))
    return a + bb + c, pairs, fixed_pairs, disabled_pairs


def verify(b, statement, proof):
    """Emit the complete reduced Tate pairing Groth16 verification relation."""
    handles, pairs, fixed_pairs, disabled_pairs = prepare(b, statement, proof)
    out = miller(b, pairs)
    fixed = ONE12
    for p, q in fixed_pairs:
        fixed = fp12_mul(None, fixed, constant_miller(p, q))
    out = fp12_mul(b, out, fixed)
    # Opposite G1 points have inverse reduced Tate values. Multiplying by this
    # precomputed raw correction gives the right residue class, including infinity.
    for flag, (p, q) in disabled_pairs:
        correction = constant_miller(p, q)
        factors = tuple(choose(b, flag, v, one) for v, one in zip(correction, ONE12))
        out = fp12_mul(b, out, factors)
    fp12_residue(b, out)
    return handles
