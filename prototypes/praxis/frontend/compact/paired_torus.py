"""Finite paired Miller lines using the public delta-line norm.

A neutral line product is replaced by the class of T. This changes it by an
r-th power in Fp12*/Fp6*, since T has order two in this quotient and r is odd.
"""

from functools import lru_cache

from . import ate, ate_fused, ate_torus, curve, moving_lines, torus
from .tower import fp12_mul, fp12_pow, fp12_square


def _components(b, x, z, line):
    s, i = line
    a, a3 = ate_fused._flat_coefficient(b, [((-1, 0), s, x)])
    c, c3 = ate_fused._flat_coefficient(b, [((1, 0), i, z)])
    return a, c, 0, a3, c3, 0


@lru_cache(maxsize=256)
def _norm_coefficients(line):
    x = _components(None, 1, 0, line)
    z = _components(None, 0, 1, line)
    return (
        torus._combine(None, (-1, 1, x, x)),
        torus._combine(None, (-2, 1, x, z)),
        torus._combine(None, (-1, 1, z, z)),
    )


def _paired(b, v1, v2, selected_v2, norm, active, second_active=1):
    den = torus._sum(b, v1, selected_v2)
    dn, n1, n2 = (torus._native(b, a) for a in (den, v1, v2))
    num = torus._combine(
        None, (1, 0, torus.ONE, torus._scalar(curve.value(b, active))), (1, 1, n1, n2)
    )
    neutral = int(not any(dn))
    native = (
        torus.ZERO if neutral else torus._combine(None, (1, 0, num, torus._nat_inv(dn)))
    )
    if b is None:
        return torus.Class(native, 0)
    out = torus.Class(tuple(b.witness(v) for v in native), 0)
    e = 0 if isinstance(second_active, int) and not second_active else b.bit(neutral)
    if e != 0:
        curve.zero(b, [(1, e, active)], [(-1, e)])
        curve.zero(b, [(1, e, second_active)], [(-1, e)])
        # Each integer chunk is nonnegative. Thus their sum is zero iff every
        # bit of every selected coefficient is zero. The exact bound is below
        # Fr, so this one row needs no auxiliary signed foreign-field carries.
        chunks = [
            (a.start + i, min(248, a.width - i))
            for a in out.a
            for i in range(0, a.width, 248)
        ]
        b._row(
            [(1, (e.start, 1), atom) for atom in chunks],
            exact_bound=sum((1 << width) - 1 for _, width in chunks),
        )
    # When e=1, both G1 factors are finite, so v2 is nonzero and R=0.
    # The equation then implies S*v2*(v1+v2)=0, hence den=0. Conversely
    # den=0 forces active=1 (the scaled slope and intercept cannot both be 0)
    # and yields (1-e)*norm(1+T*v2)=0. This forces the neutral tag.
    torus._equals_zero(
        b,
        (1, 0, out.a, den),
        (-1, 0, torus.ONE, torus._scalar(active)),
        (-1, 1, v1, v2),
        (1, 0, torus._scalar(e), norm),
    )
    return out


def _lines(b, pairs):
    active, variable = moving_lines.scaled_twist(b, pairs[0])
    if len(pairs) == 1:
        for first in variable:
            v1 = _components(b, 1, 1, first)
            yield _paired(b, v1, torus.ZERO, torus.ZERO, torus.ONE, active, 0)
        return

    point, delta = pairs[1]
    x, z = ate_fused._normalized_position(b, point)
    mono = tuple(curve.mod(b, [(1, u, w)]) for u, w in ((x, x), (x, z), (z, z)))
    ax, az = (curve.mod(b, [(1, active, a)]) for a in (x, z))
    for first, second in zip(variable, ate_fused._fixed(delta), strict=True):
        v1 = _components(b, 1, 1, first)
        v2 = _components(b, x, z, second)
        selected_v2 = _components(b, ax, az, second)
        coef = _norm_coefficients(second)
        norm = tuple(
            curve.mod(
                b, linear=[(c[j], u) for c, u in zip(coef, mono)], constant=int(j == 0)
            )
            for j in range(6)
        )
        yield _paired(b, v1, v2, selected_v2, norm, active, point[2])


def _raw_flat(lines, fixed):
    it = iter(lines)
    acc = ate.ONE
    for d in ate.DIGITS[1:]:
        acc = fp12_mul(None, fp12_square(None, acc), next(it))
        if d:
            acc = fp12_mul(None, acc, next(it))
    for line in (next(it), next(it), fixed):
        acc = fp12_mul(None, acc, line)
    return acc


def _raw(lines, fixed):
    return _raw_flat((_flat(r) for r in lines), fixed)


def _final(b, lines, seed, fixed):
    it = iter(lines)
    out = seed
    iz = torus.inverse(b, seed)
    for digit in ate.DIGITS[1:]:
        out = torus.finite_multiply(b, torus.finite_square(b, out), next(it))
        if digit:
            out = torus.finite_multiply(b, out, next(it))
            out = torus.finite_multiply(b, out, seed if digit == 1 else iz)
    out = torus.finite_multiply(b, torus.finite_multiply(b, out, next(it)), next(it))
    out = torus.finite_mul_line(b, out, fixed)
    out = torus.finite_multiply(b, out, torus.frobenius(b, seed, 1))
    return torus.finite_multiply(b, out, torus.frobenius(b, seed, 3))


def verify(b, statement, proof):
    handles, pairs, fixed = ate.prepare(b, statement, proof)
    if b is not None and b.layout_only:
        native_z = torus.Class(torus.ONE, 0)
    else:
        lines = tuple(_lines(None, ate._values(b, pairs)))
        root = fp12_pow(_raw(lines, fixed), ate_torus.LIFT)
        for _ in range(len(ate_torus._finite_stages()) + 1):
            try:
                native_z = torus.finite_witness(None, torus.from_fp12(None, root))
                _final(None, lines, native_z, fixed)
                break
            except torus.InfiniteChart:
                root = fp12_mul(None, root, ate_torus._generator())
        else:
            raise AssertionError("finite-root orbit exhausted")
    z = torus.finite_witness(b, native_z)
    out = _final(b, _lines(b, pairs), z, fixed)
    torus.assert_equal(b, out, torus.frobenius(b, z, 2))
    return handles


def _flat(r):
    return tuple(c for j, a in enumerate(r.a) for c in (a, int(j == 0)))


def _dense_updates(b, lines, seed):
    """Fused dense rows, with both signed seed factors used projectively."""
    from .tower import ORDER, fp12_value

    conjugate_seed = ate_fused._conjugate(b, seed)
    seed_nat, conjugate_nat = fp12_value(b, seed), fp12_value(b, conjugate_seed)
    inverse_nat = {
        1: fp12_pow(conjugate_nat, ORDER - 1),
        -1: fp12_pow(seed_nat, ORDER - 1),
    }
    ops = []
    it = iter(lines)
    for digit in ate.DIGITS[1:]:
        ops.append(("square", ate_fused._conjugate(b, next(it))))
        if digit:
            ops.append((digit, next(it)))
    ops.extend((("tail", next(it)), ("tail", next(it))))
    inv_lines = iter(
        ate_fused._inverses([fp12_value(b, l) for d, l in ops if d == "square"])
    )
    state, val = seed, seed_nat
    for d, line in ops:
        if d == "square":
            nxt = fp12_mul(None, fp12_square(None, val), next(inv_lines))
            if b is not None:
                wire = tuple(b.witness(y) for y in nxt)
                ate_fused._products_equal(b, wire, line, state, state)
        else:
            nxt = fp12_mul(None, val, fp12_value(b, line))
            if d != "tail":
                nxt = fp12_mul(None, nxt, inverse_nat[d])
            if b is not None:
                wire = tuple(b.witness(y) for y in nxt)
                opposite = conjugate_seed if d == 1 else (seed if d == -1 else ate.ONE)
                ate_fused._products_equal(b, wire, opposite, state, line)
        state, val = (wire if b is not None else nxt), nxt
    return state


def _verify_dense(b, statement, proof, lines_for):
    """Same paired lines and quotient residue with dense two-product updates."""
    from .tower import fp12_frob

    handles, pairs, fixed = ate.prepare(b, statement, proof)
    if b is not None and b.layout_only:
        root_class = torus.Class(torus.ONE, 0)
    else:
        lines = lines_for(None, ate._values(b, pairs))
        root = fp12_pow(_raw_flat(lines, fixed), ate_torus.LIFT)
        root_class = torus.from_fp12(None, root)
        if root_class.inf:
            # The only forbidden root is the identity. All dense states are
            # nonzero, which follows inductively from the two-product updates.
            root_class = torus.from_fp12(
                None, fp12_mul(None, root, ate_torus._generator())
            )
    z = _flat(torus.finite_witness(b, root_class))
    out = _dense_updates(b, lines_for(b, pairs), z)
    # Quotient equality means that all six odd coefficients of lhs/rhs vanish.
    # Each multiplicand is already provably nonzero. Frobenius^6 provides the
    # inverse in the quotient without an Fp12 inverse witness.
    for factor in (fixed, fp12_frob(b, z, 1), fp12_frob(b, z, 3)):
        out = fp12_mul(b, out, factor)
    conj = ate_fused._conjugate(b, fp12_frob(b, z, 2))
    if b is None:
        if any(fp12_mul(None, out, conj)[1::2]):
            raise ValueError("invalid projected BN254 residue")
    else:
        u, v = tuple(out[::2]), tuple(out[1::2])
        c, d = tuple(conj[::2]), tuple(conj[1::2])
        torus._equals_zero(b, (1, 0, u, d), (1, 0, v, c))
    return handles


def _paired_flat(b, pairs):
    return (_flat(r) for r in _lines(b, pairs))


def verify_dense(b, statement, proof):
    return _verify_dense(b, statement, proof, _paired_flat)


def verify_moving_dense(b, statement, proof):
    return _verify_dense(b, statement, proof, moving_lines.products)
