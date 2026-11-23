"""Projective arithmetic for BN254 Fp12*/Fp6* in the basis used by tower.py.

Write S=T², Fp6=Fp[S]/(S⁶−18S³+82). A representative A:T(1-e)
means the class of A+T(1-e), with e a bit. If e=1 any nonzero A represents
the identity. All chart choices on secret operands are constrained advice.
"""

from dataclasses import dataclass
from functools import lru_cache

from .curve import inverse_nat2, mod, mul2, value, zero
from .tower import P, fp12_frob

ZERO = (0,) * 6
ONE = (1,) + (0,) * 5
S = (0, 1) + (0,) * 4


@dataclass(frozen=True)
class Class:
    a: tuple
    inf: object


IDENTITY = Class(ONE, 1)


@lru_cache(maxsize=12)
def reduction(degree):
    if degree < 6:
        return ((degree, 1),)
    out = {}
    for shift, k in ((3, 18), (6, -82)):
        for pos, factor in reduction(degree - shift):
            out[pos] = out.get(pos, 0) + k * factor
    return tuple(out.items())


def _zero(v):
    return isinstance(v, int) and v == 0


def _rows(groups):
    """Expand sums of c*S^shift*left*right directly into six quadratic rows."""
    rows = [[] for _ in range(6)]
    for c, shift, left, right in groups:
        same = left is right
        for i, x in enumerate(left):
            if _zero(x):
                continue
            for j in range(i if same else 0, 6):
                y = right[j]
                if _zero(y):
                    continue
                scale = 2 * c if same and i != j else c
                for k, d in reduction(i + j + shift):
                    rows[k].append((d * scale, x, y))
    return rows


def _combine(b, *groups):
    return tuple(mod(b, row) for row in _rows(groups))


def _equals_zero(b, *groups):
    for row in _rows(groups):
        zero(b, row)


def _native(b, x):
    return tuple(value(b, a) % P for a in x)


def _scalar(a):
    return (a,) + (0,) * 5


def _sum(b, a, c):
    return tuple(mod(b, linear=[(1, x), (1, y)]) for x, y in zip(a, c))


def _nat_inv(a):
    """Invert in the cubic tower over Fp[i], with S³=9+i."""
    tower = tuple(((a[i] + 9 * a[i + 3]) % P, a[i + 3]) for i in range(3))
    x, y, z = tower

    def m(l, r):
        return mul2(None, l, r)

    def sub(l, r):
        return tuple((v - w) % P for v, w in zip(l, r))

    def add(l, r):
        return tuple((v + w) % P for v, w in zip(l, r))

    k = (9, 1)
    b0 = sub(m(x, x), m(k, m(y, z)))
    b1 = sub(m(k, m(z, z)), m(x, y))
    b2 = sub(m(y, y), m(x, z))
    norm = inverse_nat2(add(m(x, b0), m(k, add(m(y, b2), m(z, b1)))))
    coeff = tuple(m(v, norm) for v in (b0, b1, b2))
    return tuple((re - 9 * im) % P for re, im in coeff) + tuple(im for _, im in coeff)


def _project(native_n, native_d):
    if not any(native_d):
        if not any(native_n):
            raise ValueError("zero Fp12 has no projective class")
        return Class(native_n, 1)
    return Class(_combine(None, (1, 0, native_n, _nat_inv(native_d))), 0)


def _public(x):
    return isinstance(x.inf, int) and all(isinstance(a, int) for a in x.a)


def _validate(b, x):
    # A finite point A+T is always nonzero. For infinity select a single
    # nonzero coefficient of A; sum(bits)=inf controls the whole selection.
    if isinstance(x.inf, int) and x.inf == 0:
        return
    if _public(x):
        if x.inf not in (0, 1) or (x.inf and not any(a % P for a in x.a)):
            raise ValueError("invalid torus representative")
        return
    e = value(b, x.inf)
    native = _native(b, x.a)
    i = next((j for j, u in enumerate(native) if u), None) if e else None
    flags = tuple(b.bit(j == i) for j in range(6))
    zero(b, linear=[(1, v) for v in flags] + [(-1, x.inf)])
    selected = mod(b, [(1, f, a) for f, a in zip(flags, x.a)])
    inv = b.witness(pow(native[i], -1, P) if i is not None else 0)
    zero(b, [(1, selected, inv)], [(-1, x.inf)])


def _allocate(b, x):
    return Class(tuple(b.witness(a) for a in x.a), b.bit(x.inf))


def witness(b, x):
    """Allocate and validate an independently supplied projective class."""
    if len(x.a) != 6 or x.inf not in (0, 1):
        raise ValueError("invalid native torus chart")
    out = x if b is None else _allocate(b, x)
    _validate(b, out)
    return out


def _native_project(b, n, d):
    if b is not None and b.layout_only and not (any(n) or any(d)):
        return IDENTITY
    return _project(n, d)


def _force_chart(b, e, d):
    # If d!=0, then e=0. If d=0, nonzero n and A*(d+e)=n imply e=1.
    for v in d:
        zero(b, [(1, e, v)])


def from_fp12(b, f):
    if len(f) != 12:
        raise ValueError("Fp12 requires twelve coefficients")
    u, v = tuple(f[::2]), tuple(f[1::2])
    if b is None or all(isinstance(x, int) for x in f):
        return _project(_native(b, u), _native(b, v))
    a = _native_project(b, _native(b, u), _native(b, v))
    out = _allocate(b, a)
    _force_chart(b, out.inf, v)
    _equals_zero(b, (1, 0, out.a, _sum(b, v, _scalar(out.inf))), (-1, 0, ONE, u))
    # If (u,v)=(0,0) and e=0 then the finite equation is vacuous. Require
    # that the source is nonzero independently of the normalization.
    if not any(isinstance(c, int) and c % P for c in f):
        n = _native(b, f)
        i = next((j for j, a in enumerate(n) if a), None)
        flags = tuple(b.bit(j == i) for j in range(12))
        zero(b, linear=[(1, c) for c in flags], constant=-1)
        selected = mod(b, [(1, flag, c) for flag, c in zip(flags, f)])
        b.inverse(selected)
    return out


def square(b, x):
    """One Fp6 advice value and one chart bit, including both exceptional charts."""
    a, e = x.a, x.inf
    v, en = _native(b, a), value(b, e)
    n = _combine(None, (1, 0, v, v), (1 - en, 0, ONE, S))
    e2 = int(en or not any(v))
    d = tuple((2 * x0 + (e2 - en if j == 0 else 0)) % P for j, x0 in enumerate(v))
    if not any(d) and b is not None and b.layout_only:
        native = IDENTITY
    else:
        native = Class(_combine(None, (1, 0, n, _nat_inv(d))), e2)
    if b is None or _public(x):
        return native
    out = _allocate(b, native)
    delta = mod(b, linear=[(1, out.inf), (-1, e)])
    for aj in a:
        zero(b, [(1, aj, delta)])
    _equals_zero(
        b,
        (2, 0, out.a, a),
        (1, 0, out.a, _scalar(delta)),
        (-1, 0, a, a),
        (-1, 1, ONE, _scalar(mod(b, linear=[(-1, e)], constant=1))),
    )
    return out


def _mul_projective(b, x, u, v):
    """Multiply a valid class x by the known-nonzero Fp12 element u+Tv."""
    a, e = x.a, x.inf
    y = _scalar(mod(b, linear=[(-1, e)], constant=1))
    d = _combine(b, (1, 0, a, v), (1, 0, y, u))
    an, un, vn, yn = (_native(b, z) for z in (a, u, v, y))
    n = _combine(None, (1, 0, an, un), (1, 1, yn, vn))
    native = _native_project(b, n, _native(b, d))
    if b is None or (_public(x) and all(isinstance(c, int) for c in u + v)):
        return native
    out = _allocate(b, native)
    _force_chart(b, out.inf, d)
    _equals_zero(
        b, (1, 0, out.a, _sum(b, d, _scalar(out.inf))), (-1, 0, a, u), (-1, 1, y, v)
    )
    return out


def multiply(b, x, y):
    return _mul_projective(b, x, y.a, _scalar(mod(b, linear=[(-1, y.inf)], constant=1)))


def mul_line(b, x, line):
    """Fuse multiplication by a Miller line already proved nonzero by the caller."""
    if len(line) != 12:
        raise ValueError("Fp12 requires twelve coefficients")
    return _mul_projective(b, x, tuple(line[::2]), tuple(line[1::2]))


def inverse(b, x):
    return Class(tuple(mod(b, linear=[(-1, a)]) for a in x.a), x.inf)


@lru_cache(maxsize=12)
def _frob_matrix(power):
    # (A+T)^(p^i) has chart Frob(A)/(Frob(T)/T); that same invertible
    # linear map may scale any infinity representative.
    denom = fp12_frob(None, (0, 1) + (0,) * 10, power)[1::2]
    di = _nat_inv(denom)
    cols = []
    for j in range(6):
        basis = tuple(int(k == 2 * j) for k in range(12))
        image = fp12_frob(None, basis, power)[::2]
        cols.append(_combine(None, (1, 0, image, di)))
    return tuple(cols)


def frobenius(b, x, power):
    cols = _frob_matrix(power % 12)
    a = tuple(
        mod(b, linear=[(col[j], v) for col, v in zip(cols, x.a) if col[j]])
        for j in range(6)
    )
    return Class(a, x.inf)


def assert_equal(b, x, y):
    zero(b, linear=[(1, x.inf), (-1, y.inf)])
    finite = mod(b, linear=[(-1, x.inf)], constant=1)
    for a, c in zip(x.a, y.a):
        zero(b, [(1, finite, a), (-1, finite, c)])


class InfiniteChart(ValueError):
    """A finite-only update requires a different root advice lift."""


def _finite_quotient(b, numerator, denominator):
    n, d = _native(b, numerator), _native(b, denominator)
    if not any(d):
        if b is not None and b.layout_only:
            return ONE
        raise InfiniteChart("torus result is not finite in the selected root chart")
    return _combine(None, (1, 0, n, _nat_inv(d)))


def finite_witness(b, x):
    """A+T is nonzero for every A in Fp6. Root selection covers infinity."""
    if x.inf:
        raise InfiniteChart("initial torus root is at infinity")
    return x if b is None else Class(tuple(b.witness(a) for a in x.a), 0)


def _finite_advice(b, vals):
    return Class(tuple(b.witness(v) for v in vals), 0)


def finite_square(b, x):
    if x.inf != 0:
        raise InfiniteChart("finite square requires a finite input")
    a = x.a
    v = _native(b, a)
    numerator = _combine(None, (1, 0, v, v), (1, 0, ONE, S))
    d = tuple(2 * k % P for k in v)
    next_a = _finite_quotient(b, numerator, d)
    if b is None or _public(x):
        return Class(next_a, 0)
    out = _finite_advice(b, next_a)
    _equals_zero(b, (2, 0, out.a, a), (-1, 0, a, a), (-1, 0, ONE, S))
    return out


def finite_multiply(b, x, y):
    if x.inf != 0 or y.inf != 0:
        raise InfiniteChart("finite multiplication requires finite inputs")
    a, c = x.a, y.a
    av, cv = _native(b, a), _native(b, c)
    v = _combine(None, (1, 0, av, cv), (1, 0, ONE, S))
    d = _sum(b, a, c)
    next_a = _finite_quotient(b, v, d)
    if b is None or (_public(x) and _public(y)):
        return Class(next_a, 0)
    out = _finite_advice(b, next_a)
    _equals_zero(b, (1, 0, out.a, d), (-1, 0, a, c), (-1, 0, ONE, S))
    return out


def finite_mul_line(b, x, line):
    if x.inf != 0 or len(line) != 12:
        raise ValueError(
            "finite Miller update requires a finite class and an Fp12 line"
        )
    u, v = tuple(line[::2]), tuple(line[1::2])
    if all(_zero(z) for z in v) and any(isinstance(z, int) and z % P for z in u):
        return x
    av, uv, vv = (_native(b, z) for z in (x.a, u, v))
    n = _combine(None, (1, 0, av, uv), (1, 1, ONE, vv))
    d = _combine(b, (1, 0, x.a, v), (1, 0, ONE, u))
    next_a = _finite_quotient(b, n, d)
    if b is None or (_public(x) and all(isinstance(c, int) for c in line)):
        return Class(next_a, 0)
    out = _finite_advice(b, next_a)
    _equals_zero(b, (1, 0, out.a, d), (-1, 0, x.a, u), (-1, 1, ONE, v))
    return out
