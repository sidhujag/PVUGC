"""Batch a Miller tangent and chord, or the final two chords, as one conic.

The vertical divisor of the intermediate point takes its value in Fp6*.
Removing it preserves the reduced pairing. Normalizing the odd conic term
to T makes the fixed delta conic affine in three G1 values and keeps each
of the variable conic's three Fp2 coefficient equations quadratic.
"""

from . import ate, ate_fused, ate_torus, curve, moving_lines, paired_torus, torus
from .condensed_curve import relation
from .tower import fp12_frob, fp12_mul, fp12_pow, fp12_square, fp12_value


def _add(b, a, c):
    return tuple(curve.mod(b, linear=[(1, x), (1, y)]) for x, y in zip(a, c))


def _allocated(b, v):
    return tuple(b.witness(x) for x in v) if b is not None else tuple(v)


def _native(b, a):
    return tuple(curve.value(b, x) for x in a)


def _conic(b, first, second, metric):
    s, i = first
    t, j = second
    sigma = _add(b, s, t)
    intercept_sum = _add(b, i, j)
    inv = curve.inverse_nat2(_native(b, sigma))
    sv, tv, iv, jv = (_native(b, v) for v in (s, t, i, j))
    ij = _native(b, intercept_sum)
    g0 = curve.mul2(None, ((-curve.value(b, metric)) % curve.P, 0), inv)
    g2 = curve.mul2(
        None,
        curve.subtract2(None, curve.mul2(None, g0, ij), curve.mul2(None, sv, tv)),
        inv,
    )
    g4 = curve.mul2(
        None,
        _add(
            None,
            curve.mul2(None, g2, ij),
            _add(None, curve.mul2(None, sv, jv), curve.mul2(None, tv, iv)),
        ),
        inv,
    )
    g0, g2, g4 = tuple(_allocated(b, g) for g in (g0, g2, g4))
    if b is not None:
        relation(b, [(1, sigma, g0)], [(1, (metric, 0))])
        relation(b, [(1, sigma, g2), (-1, g0, intercept_sum), (1, s, t)])
        relation(b, [(1, sigma, g4), (-1, g2, intercept_sum), (-1, s, j), (-1, t, i)])
    return g0, g2, g4


def _even(b, coefficients, factors):
    # Express g0+g2*T²+g4*T⁴ in the real Fp6 basis, using i=T⁶-9.
    low = [
        curve.mod(b, [(1, re, w), (-9, im, w)])
        for (re, im), w in zip(coefficients, factors)
    ]
    high = [curve.mod(b, [(1, im, w)]) for (_, im), w in zip(coefficients, factors)]
    return tuple(low + high)


def _paired_conic(
    b, left, right, factors, selected_factors, monomials, active, second_active
):
    u = _even(b, left, (1, 1, 1))
    v = _even(b, right, factors)
    denominator = torus._sum(b, u, _even(b, right, selected_factors))
    den, un, vn = (torus._native(b, x) for x in (denominator, u, v))
    numerator = torus._combine(
        None, (1, 0, un, vn), (1, 1, torus.ONE, torus._scalar(curve.value(b, active)))
    )
    neutral = not any(den)
    r = (
        torus.ZERO
        if neutral
        else torus._combine(None, (1, 0, numerator, torus._nat_inv(den)))
    )
    cls = torus.finite_witness(b, torus.Class(r, 0))
    if b is None:
        return cls

    # For e=1 enforce R=0, substituting the order-two class of T. The fixed
    # conic has nonzero constant coefficient whenever its G1 input is finite.
    # Thus e=1 and R=0 imply v*(u+v)=0 with v!=0, so den=0. Conversely
    # den=0 forces active=1, since the variable conic has g0!=0.
    e = b.bit(neutral)
    curve.zero(b, [(1, e, active)], [(-1, e)])
    curve.zero(b, [(1, e, second_active)], [(-1, e)])
    atoms = [
        (a.start + j, min(248, a.width - j))
        for a in cls.a
        for j in range(0, a.width, 248)
    ]
    b._row(
        [(1, (e.start, 1), atom) for atom in atoms],
        exact_bound=sum((1 << width) - 1 for _, width in atoms),
    )

    # S-v² is nonzero since S=T² is a nonsquare in Fp6. The six scalar
    # monomials come from a single fixed G1 point and are shared across steps.
    basis = [_even(None, right, tuple(int(i == j) for i in range(3))) for j in range(3)]
    weights = [
        torus._combine(None, (-1 if i == j else -2, 0, basis[i], basis[j]))
        for i in range(3)
        for j in range(i, 3)
    ]
    norm = tuple(
        curve.mod(
            b,
            linear=[(w[j], m) for w, m in zip(weights, monomials)],
            constant=int(j == 1),
        )
        for j in range(6)
    )
    torus._equals_zero(
        b,
        (1, 0, cls.a, denominator),
        (-1, 0, u, v),
        (-1, 1, torus.ONE, torus._scalar(active)),
        (1, 0, torus._scalar(e), norm),
    )
    return cls


def _ops(b, pairs, digits=None, direct_groups=False):
    active, variable = moving_lines.scaled_twist(b, pairs[0], digits, direct_groups)
    x, z = ate_fused._normalized_position(b, pairs[0][0])
    t, h = (curve.mod(b, linear=[(1, a), (-1, active)], constant=1) for a in (x, z))
    t2 = curve.mod(b, [(1, t, t)])
    native_metric = (
        curve.value(b, t) ** 3 * pow(curve.value(b, h), -1, curve.P) % curve.P
    )
    metric = b.witness(native_metric) if b is not None else native_metric
    if b is not None:
        curve.zero(b, [(1, metric, h), (-1, t2, t)])

    def mul(a, c):
        return curve.mod(b, [(1, a, c)])

    if len(pairs) == 2:
        pc, delta = pairs[1]
        second_active = pc[2]
        xc, zc = ate_fused._normalized_position(b, pc)
        ax, az = (mul(active, v) for v in (xc, zc))
        mono = (mul(xc, xc), mul(xc, zc), mul(zc, zc))
        factors = (mul(pc[0], xc), xc, zc)
        selected = tuple(mul(active, v) for v in factors)
        squares = tuple(
            mul(factors[i], factors[j]) for i in range(3) for j in range(i, 3)
        )
    else:
        # All of the right conic's coefficients are zero, which implements
        # the same harmless order-two tag for a disabled public delta term.
        delta = curve.G2
        second_active = xc = zc = ax = az = 0
        mono = factors = selected = (0, 0, 0)
        squares = (0,) * 6
    fixed = (
        iter(ate_fused._fixed(delta))
        if digits is None
        else moving_lines.steps(None, delta, digits=digits)
    )

    def single():
        first, second = next(variable), next(fixed)
        v1 = paired_torus._components(b, 1, 1, first)
        v2 = paired_torus._components(b, xc, zc, second)
        selected_v2 = paired_torus._components(b, ax, az, second)
        coeffs = paired_torus._norm_coefficients(second)
        norm = tuple(
            curve.mod(
                b,
                linear=[(w[j], m) for w, m in zip(coeffs, mono)],
                constant=int(j == 0),
            )
            for j in range(6)
        )
        return paired_torus._paired(b, v1, v2, selected_v2, norm, active, second_active)

    def grouped(direct=False):
        left = (
            next(variable)
            if direct
            else _conic(b, next(variable), next(variable), metric)
        )
        right = _conic(None, next(fixed), next(fixed), 1)
        return _paired_conic(
            b, left, right, factors, selected, squares, active, second_active
        )

    if digits is None:
        for d in ate.DIGITS[1:]:
            yield True, d, grouped(direct_groups) if d else single()
    else:
        # Keep the [2]Q factor allocated once even though it is used in both
        # the odd-digit table and the main ladder.
        previous = None
        for _ in range((max(abs(d) for d in digits) + 1) // 2):
            line = single()
            if previous is None:
                previous = line
            yield False, None, line
        for index, d in enumerate(digits[1:]):
            if index == 0:
                next(variable)
                next(fixed)
                yield True, 0, previous
            else:
                yield True, d, grouped(direct_groups) if d else single()
    yield False, 0, grouped()


def _raw(ops, fixed):
    value = ate.ONE
    for square, _, line in ops:
        if square:
            value = fp12_square(None, value)
        value = fp12_mul(None, value, paired_torus._flat(line))
    return fp12_mul(None, value, fixed)


def _dense(b, ops, root):
    seed = paired_torus._flat(root)
    inv_root = torus.inverse(b, root)
    updates = []
    for square, d, line in ops:
        if d:
            line = torus.finite_multiply(b, line, root if d == 1 else inv_root)
        flat = paired_torus._flat(line)
        updates.append((square, ate_fused._conjugate(b, flat) if square else flat))
    inv = iter(
        ate_fused._inverses([fp12_value(b, x) for square, x in updates if square])
    )
    state, value = seed, fp12_value(b, seed)
    for square, line in updates:
        if square:
            value = fp12_mul(None, fp12_square(None, value), next(inv))
            if b is not None:
                nxt = _allocated(b, value)
                ate_fused._products_equal(b, nxt, line, state, state)
        else:
            value = fp12_mul(None, value, fp12_value(b, line))
            if b is not None:
                nxt = _allocated(b, value)
                ate_fused._products_equal(b, nxt, ate.ONE, state, line)
        state = nxt if b is not None else value
    return state


def verify(b, statement, proof):
    handles, pairs, fixed = ate.prepare(b, statement, proof)
    if b is not None and b.layout_only:
        root = torus.Class(torus.ONE, 0)
    else:
        ops = tuple(_ops(None, ate._values(b, pairs)))
        f = fp12_pow(_raw(ops, fixed), ate_torus.LIFT)
        # Every signed grouped line forbids at most one rotated seed. The
        # seed itself must be finite, so at most 22 of the r choices fail.
        for _ in range(2 + sum(bool(d) for d in ate.DIGITS[1:])):
            try:
                root = torus.finite_witness(None, torus.from_fp12(None, f))
                inverse = torus.inverse(None, root)
                for _, d, line in ops:
                    if d:
                        torus.finite_multiply(None, line, root if d == 1 else inverse)
                break
            except torus.InfiniteChart:
                f = fp12_mul(None, f, ate_torus._generator())
        else:
            raise AssertionError("finite conic-root orbit exhausted")
    root = torus.finite_witness(b, root)
    z = paired_torus._flat(root)
    out = _dense(b, _ops(b, pairs), root)
    _finish(b, out, z, fixed)
    return handles


def _finish(b, out, z, fixed):
    for f in (fixed, fp12_frob(b, z, 1), fp12_frob(b, z, 3)):
        out = fp12_mul(b, out, f)
    c = ate_fused._conjugate(b, fp12_frob(b, z, 2))
    if b is None:
        if any(fp12_mul(None, out, c)[1::2]):
            raise ValueError("invalid projected conic pairing-product")
    else:
        torus._equals_zero(
            b,
            (1, 0, tuple(out[::2]), tuple(c[1::2])),
            (1, 0, tuple(out[1::2]), tuple(c[::2])),
        )
