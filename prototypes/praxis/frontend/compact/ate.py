"""Fixed-key BN254 optimal Ate product, fused with a nonzero residue witness.

The signed-digit loop starts at z rather than 1, accumulating f*z^(6u+2).
Vertical denominators in the Miller calculation belong to Fp6 and disappear
under the final exponent. The affine line formulas below evaluate at G1 on
the sextic twist map (x,y) -> (x*T^2,y*T^3).
"""

from functools import lru_cache

from . import curve
from .tower import (
    ATE,
    LAMBDA,
    ORDER,
    WIDTH,
    P,
    R,
    fp12_frob,
    fp12_mul,
    fp12_one,
    fp12_pow,
    fp12_square,
    fp12_value,
)

ONE = fp12_one()
M = ORDER // R
K = M // 27
PROJECTION = K * pow(K, -1, 27)
HIGH_LIFT = (-pow(LAMBDA, -1, K) * (1 - PROJECTION)) % M


@lru_cache(maxsize=1)
def correction_table():
    # 3+T gives a deterministic generator of the 3-primary subgroup.
    eta = fp12_pow((3, 1) + (0,) * 10, ORDER // 27)
    table = [ONE]
    for _ in range(1, 27):
        table.append(fp12_mul(None, table[-1], eta))
    if len(set(table)) != 27 or fp12_mul(None, table[-1], eta) != ONE:
        raise ArithmeticError("BN254 cubic-coset generator did not have order 27")
    return tuple(table)


def root_and_correction(f):
    """For f in the order-M subgroup return z,e with f*eta^e*z^lambda=1."""
    table = correction_table()
    low = fp12_pow(f, PROJECTION)
    try:
        index = table.index(low)
    except ValueError:
        # An invalid input receives advice of the same shape. The circuit's
        # final equality still decides acceptance.
        return ONE, 0
    e = (-index) % 3
    j = ((-index - e) // 3 * pow(LAMBDA // 3, -1, 9)) % 9
    return fp12_mul(None, fp12_pow(f, HIGH_LIFT), table[j]), e


def _naf(n):
    digits = []
    while n:
        digit = 2 - (n % 4) if n & 1 else 0
        digits.append(digit)
        n = (n - digit) // 2
    return tuple(reversed(digits))


DIGITS = _naf(ATE)


def _neg2(b, value):
    return tuple(curve.neg(b, v) for v in value)


def _negative(b, point):
    return point[0], _neg2(b, point[1])


def _frob_point(b, point):
    _, fx, fy = curve.twist_constants()

    def conjugate(x):
        return x[0], curve.neg(b, x[1])

    x, y = point
    return curve.mul2(b, conjugate(x), fx), curve.mul2(b, conjugate(y), fy)


def _line_step(b, left, right, doubling):
    """The signed BN254 prefix denominator bounds are checked in test_ate.py."""
    x, y = left
    u, v = right
    xv, yv = tuple(curve.value(b, i) for i in x), tuple(curve.value(b, i) for i in y)
    if doubling:
        top = tuple(3 * i % P for i in curve.mul2(None, xv, xv))
        bottom = tuple(2 * i % P for i in yv)
    else:
        top = tuple((curve.value(b, i) - j) % P for i, j in zip(v, yv))
        bottom = tuple((curve.value(b, i) - j) % P for i, j in zip(u, xv))
    advice = curve.mul2(None, top, curve.inverse_nat2(bottom))
    if b is None or all(isinstance(t, int) for t in x + y + u + v):
        slope = advice
    else:
        slope = tuple(b.witness(i) for i in advice)
    s, t = slope
    if doubling:
        curve.zero(b, [(2, s, y[0]), (-2, t, y[1]), (-3, x[0], x[0]), (3, x[1], x[1])])
        curve.zero(b, [(2, s, y[1]), (2, t, y[0]), (-6, x[0], x[1])])
    else:
        curve.zero(
            b,
            [(1, s, u[0]), (-1, s, x[0]), (-1, t, u[1]), (1, t, x[1])],
            [(1, y[0]), (-1, v[0])],
        )
        curve.zero(
            b,
            [(1, s, u[1]), (-1, s, x[1]), (1, t, u[0]), (-1, t, x[0])],
            [(1, y[1]), (-1, v[1])],
        )
    xx = (
        curve.mod(b, [(1, s, s), (-1, t, t)], [(-1, x[0]), (-1, u[0])]),
        curve.mod(b, [(2, s, t)], [(-1, x[1]), (-1, u[1])]),
    )
    intercept = (
        curve.mod(b, [(1, s, x[0]), (-1, t, x[1])], [(-1, y[0])]),
        curve.mod(b, [(1, s, x[1]), (1, t, x[0])], [(-1, y[1])]),
    )
    yy = (
        curve.mod(b, [(-1, s, xx[0]), (1, t, xx[1])], [(1, intercept[0])]),
        curve.mod(b, [(-1, s, xx[1]), (-1, t, xx[0])], [(1, intercept[1])]),
    )
    return (xx, yy), (slope, intercept)


def _evaluate_line(b, g1, coeffs):
    # y_P - slope_Q * x_P * T + (slope_Q*x_Q - y_Q) * T^3
    x, y = g1[:2]
    z = g1[2] if len(g1) == 3 else 1
    (s0, s1), (b0, b1) = coeffs
    values = [0] * WIDTH
    values[0] = y
    values[1] = curve.mod(b, [(-1, s0, x), (9, s1, x)])
    values[7] = curve.mod(b, [(-1, s1, x)])
    values[3] = curve.mod(b, [(1, z, b0), (-9, z, b1)])
    values[9] = curve.mod(b, [(1, z, b1)])
    return tuple(values)


def _steps(b, q):
    acc = q
    neg = _negative(b, q)
    for digit in DIGITS[1:]:
        before = acc
        acc, line = _line_step(b, before, before, True)
        yield line
        if digit:
            before = acc
            acc, line = _line_step(b, before, q if digit == 1 else neg, False)
            yield line
    q1 = _frob_point(b, q)
    q2 = _negative(b, _frob_point(b, q1))
    before = acc
    acc, line = _line_step(b, before, q1, False)
    yield line
    # Check [ATE]q + psi(q) - psi²(q) + psi³(q) = O on the original
    # twist point. This saves a separate subgroup scalar ladder. See
    # compact README for the Frobenius norm and exact twist cofactor.
    last, line = _line_step(b, acc, q2, False)
    target = _frob_point(b, q2)  # q2 carries the minus sign
    for a, bcoord in zip(last, target):
        for v, w in zip(a, bcoord):
            curve.zero(b, linear=[(1, v), (-1, w)])
    yield line


@lru_cache(maxsize=16)
def _fixed_steps(q):
    return tuple(_steps(None, q))


def _miller(b, pairs, seed=ONE, inverse_seed=ONE):
    if not pairs:
        return ONE
    line_traces = [
        iter(_fixed_steps(q))
        if all(isinstance(x, int) for c in q for x in c)
        else _steps(b, q)
        for _, q in pairs
    ]

    def multiply_lines(acc):
        # Fold the two sparse lines before multiplying the dense accumulator.
        line = ONE
        for (g1, _), trace in zip(pairs, line_traces):
            factor = _evaluate_line(b, g1, next(trace))
            line = factor if line is ONE else fp12_mul(b, line, factor)
        return fp12_mul(b, acc, line)

    out = seed
    for digit in DIGITS[1:]:
        out = multiply_lines(fp12_square(b, out))
        if digit:
            out = multiply_lines(out)
            factor = seed if digit == 1 else inverse_seed
            if factor is not ONE:
                out = fp12_mul(b, out, factor)
    return multiply_lines(multiply_lines(out))


@lru_cache(maxsize=16)
def constant_miller(g1, q):
    if not any(g1) or not any(q[0] + q[1]):
        return ONE
    return _miller(None, [(g1, q)])


def _fixed_factors(fixed):
    result = ONE
    for g1, q in fixed:
        result = fp12_mul(None, result, constant_miller(g1, q))
    return result


def _values(b, pairs):
    return tuple(
        (
            tuple(curve.value(b, x) for x in g1),
            tuple(tuple(curve.value(b, x) for x in component) for component in q),
        )
        for g1, q in pairs
    )


def verify(b, statement, proof):
    """Emit BQS constraints or perform the same checks natively (b=None)."""
    # Infinity is represented homogeneously at the place where the line is
    # evaluated. Every line at (0,1,0) is 1. The variable G2 point itself
    # remains in the loop for its subgroup check even if A is infinity.
    a, _, fa = curve.private_point(b, curve.g1(proof["a"]), curve.G1, curve.correct_g1)
    bcoords, qb, fb = curve.private_point(
        b, curve.g2(proof["b"]), curve.G2, curve.on_twist
    )
    c, _, fc = curve.private_point(b, curve.g1(proof["c"]), curve.G1, curve.correct_g1)
    disabled = curve.mod(b, [(-1, fa, fb)], linear=[(1, fa), (1, fb)])
    pa = (
        curve.choose(b, disabled, 0, a[0]),
        curve.choose(b, disabled, 1, a[1]),
        curve.mod(b, linear=[(-1, disabled)], constant=1),
    )
    pairs = [(pa, qb)]
    delta = curve.g2(statement["delta"])
    if any(delta[0] + delta[1]):
        # C's decoded infinity coordinates are both zero by constraint.
        pc = (
            c[0],
            curve.mod(b, linear=[(-1, c[1]), (1, fc)]),
            curve.mod(b, linear=[(-1, fc)], constant=1),
        )
        pairs.append((pc, delta))
    fixed = [
        (curve.opposite(curve.g1(statement["L"])), curve.g2(statement["gamma"])),
        (curve.opposite(curve.g1(statement["alpha"])), curve.g2(statement["beta"])),
    ]
    factors = _fixed_factors(fixed)
    handles = a + bcoords + c
    if b is not None and b.layout_only:
        native_z, selector = ONE, 0
    else:
        raw = _miller(None, _values(b, pairs))
        raw = fp12_mul(None, raw, fp12_value(b, factors))
        native_z, selector = root_and_correction(raw)
    native_inv = fp12_pow(native_z, ORDER - 1)
    if b is None:
        z, inv_z = native_z, native_inv
        correction = correction_table()[selector]
    else:
        z = tuple(b.witness(x) for x in native_z)
        inv_z = tuple(b.witness(x) for x in native_inv)
        for observed, expected in zip(fp12_mul(b, z, inv_z), ONE):
            b.equal(observed, expected)
        sel1, sel2 = b.bit(selector == 1), b.bit(selector == 2)
        b.assert_zero([(1, sel1, sel2)])
        t = correction_table()
        correction = tuple(
            curve.mod(b, linear=[(c1 - c0, sel1), (c2 - c0, sel2)], constant=c0)
            for c0, c1, c2 in zip(ONE, t[1], t[2])
        )
    out = _miller(b, pairs, z, inv_z)
    out = fp12_mul(b, out, factors)
    out = fp12_mul(b, out, correction)
    out = fp12_mul(b, out, fp12_frob(b, z, 1))
    out = fp12_mul(b, out, fp12_frob(b, z, 3))
    rhs = fp12_frob(b, z, 2)
    if b is None:
        if out != rhs:
            raise ValueError("invalid optimal Ate pairing-product or residue")
    else:
        for left, right in zip(out, rhs):
            b.equal(left, right)
    return handles
