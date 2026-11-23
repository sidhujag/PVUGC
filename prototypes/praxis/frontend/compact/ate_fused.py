"""Optimal Ate with two-product equations and a subfield-normalized square.

Each doubling represents its update by new*conj6(line)=old². The advice
changes from the usual update old²*line by the inverse Fp6 norm of line.
Every norm is nonzero and an r-th power, hence membership in (Fp12*)^r is
unchanged. The native lift recomputes exactly this normalized representative.
"""

from functools import lru_cache
from . import ate, curve
from .condensed_curve import steps
from .tower import ORDER, REDUCTION, WIDTH, fp12_mul, fp12_pow, fp12_square, fp12_value

ONE = ate.ONE


@lru_cache(maxsize=16)
def _fixed(q):
    return tuple(steps(None, q))


def _neg2_const(a):
    return tuple((-v) % curve.P for v in a)


def _normalized_position(b, point):
    # Homogeneous point at infinity (0,1,0), or a finite affine point with
    # y != 0, since G1 has odd prime order. Scaling its line by 1/y is free
    # under the reduced pairing. Degree-two verifiable advice never leaks a
    # witness-dependent constant into the public graph.
    x, y = point[:2]
    z = point[2] if len(point) == 3 else 1
    iy = pow(curve.value(b, y), -1, curve.P)
    if all(isinstance(k, int) for k in (x, y, z)):
        return x * iy % curve.P, z * iy % curve.P
    xp = b.witness(curve.value(b, x) * iy % curve.P)
    zp = b.witness(curve.value(b, z) * iy % curve.P)
    curve.zero(b, [(1, xp, y)], [(-1, x)])
    curve.zero(b, [(1, zp, y)], [(-1, z)])
    return xp, zp


def _mixed(b, factors):
    if len(factors) == 1:
        return ()
    (x, z), (other_x, other_z) = factors
    return tuple(
        curve.mod(b, [(1, u, v)])
        for u, v in [(x, other_x), (x, other_z), (z, other_x), (z, other_z)]
    )


def _flat_coefficient(b, terms, constant=0):
    # A term is c * (a0 + i*a1) * r, with fixed c in Fp² and scalar r.
    # Substitute i=T^6-9 directly in the emit; never allocate a separate
    # Fp² product just to apply the linear change of basis.
    real, high = [], []
    for (c0, c1), (a0, a1), r in terms:
        real += [(c0 - 9 * c1, a0, r), (-c1 - 9 * c0, a1, r)]
        high += [(c1, a0, r), (c0, a1, r)]
    return curve.mod(b, real, constant=constant), curve.mod(b, high)


def _line_product(b, positions, mixed, slopes):
    x, z = positions[0]
    s, i = slopes[0]
    vals = [0] * WIDTH
    if len(positions) == 1:
        vals[0] = 1
        vals[1], vals[7] = _flat_coefficient(b, [((-1, 0), s, x)])
        vals[3], vals[9] = _flat_coefficient(b, [((1, 0), i, z)])
        return tuple(vals)
    # Multiply the two sparse normalized lines (1 - sxT + izT³).
    # The second G2 point is fixed, so t,j and all their multiples are public.
    y, w = positions[1]
    t, j = slopes[1]
    xx, xz, zx, zz = mixed
    vals[0], vals[6] = _flat_coefficient(
        b, [(curve.mul2(None, j, (9, 1)), i, zz)], constant=1
    )
    vals[1], vals[7] = _flat_coefficient(b, [((-1, 0), s, x), ((-1, 0), t, y)])
    vals[2], vals[8] = _flat_coefficient(b, [(t, s, xx)])
    vals[3], vals[9] = _flat_coefficient(b, [((1, 0), i, z), ((1, 0), j, w)])
    vals[4], vals[10] = _flat_coefficient(
        b, [(_neg2_const(j), s, xz), (_neg2_const(t), i, zx)]
    )
    return tuple(vals)


def _products_equal(b, left, right, other_left, other_right):
    terms = [[] for _ in range(WIDTH)]
    for a, c, sign in ((left, right, 1), (other_left, other_right, -1)):
        sq = a is c
        for i, xi in enumerate(a):
            if isinstance(xi, int) and xi == 0:
                continue
            for j in range(i if sq else 0, WIDTH):
                yj = c[j]
                if isinstance(yj, int) and yj == 0:
                    continue
                k0 = 2 if sq and j != i else 1
                for dest, k in REDUCTION[i + j]:
                    terms[dest].append((sign * k0 * k, xi, yj))
    for row in terms:
        b.assert_zero(row)


def _conjugate(b, value):
    # T -> -T gives Frobenius⁶. Its norm has multiplicative order dividing p⁶−1.
    return tuple(curve.neg(b, v) if i % 2 else v for i, v in enumerate(value))


def _inverses(elements):
    prefixes = []
    product = ONE
    for a in elements:
        prefixes.append(product)
        product = fp12_mul(None, product, a)
    if not any(product):
        raise ValueError("zero norm of a normalized Miller line")
    inverse = fp12_pow(product, ORDER - 1)
    result = []
    for prefix, a in zip(reversed(prefixes), reversed(elements)):
        result.append(fp12_mul(None, inverse, prefix))
        inverse = fp12_mul(None, inverse, a)
    return tuple(reversed(result))


def _miller(b, pairs, seed=ONE, inverse_seed=ONE):
    positions = [_normalized_position(b, pt) for pt, _ in pairs]
    mixed = _mixed(b, positions)
    traces = [
        iter(_fixed(q))
        if all(isinstance(x, int) for coord in q for x in coord)
        else steps(b, q)
        for _, q in pairs
    ]

    def line():
        return _line_product(b, positions, mixed, [next(t) for t in traces])

    ops = []
    for d in ate.DIGITS[1:]:
        ops.append(("square", _conjugate(b, line())))
        if d:
            ops.append((d, line()))
    ops.extend((("tail", line()), ("tail", line())))
    return _run_ops(b, ops, seed, inverse_seed)


def _run_ops(b, ops, seed, inverse_seed):
    inverse_lines = iter(_inverses([fp12_value(b, x) for d, x in ops if d == "square"]))
    out = seed
    val = fp12_value(b, seed)
    for op, line_wire in ops:
        if op == "square":
            next_native = fp12_mul(None, fp12_square(None, val), next(inverse_lines))
            if b is not None:
                nxt = tuple(b.witness(v) for v in next_native)
                _products_equal(b, nxt, line_wire, out, out)
        else:
            if op == 1:
                factor, opposite = seed, inverse_seed
            elif op == -1:
                factor, opposite = inverse_seed, seed
            else:
                factor = opposite = ONE
            next_native = fp12_mul(None, val, fp12_value(b, line_wire))
            if factor is not ONE:
                next_native = fp12_mul(None, next_native, fp12_value(b, factor))
            if b is not None:
                nxt = tuple(b.witness(v) for v in next_native)
                _products_equal(b, nxt, opposite, out, line_wire)
        out = nxt if b is not None else next_native
        val = next_native
    return out


def verify(b, statement, proof):
    return ate.verify_with_miller(b, statement, proof, _miller)
