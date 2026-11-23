"""Check a tangent and a chord in one degree-two Vieta certificate.

For a monic conic X²+L*X+C=A*Y on Y²=X³/k+H, its norm quartic has
third coefficient 2L-A²/k and second coefficient L²+2C. Incidence puts
the distinct old abscissae p,v among its roots. The two coefficient
equations make its remaining roots have sum p+w and product p*w, so
they are p and w with multiplicities. A is nonzero and the old point
is not 2-torsion. Thus the double root is tangency at the old point.
The final conic incidence fixes the reflected ordinate of the output.
"""

from functools import lru_cache
from math import gcd

from . import curve
from .condensed_curve import relation


@lru_cache(maxsize=8)
def certify(digits):
    # The two known roots of the norm quartic must be distinct on *every*
    # possible input twist subgroup, even before final G2 validation.
    order = curve.R * (2 * curve.P - curve.R)
    prefix = digits[0]
    for digit in digits[1:]:
        if digit and any(gcd(prefix + i, order) != 1 for i in (-digit, digit)):
            raise ValueError("direct conic requires distinct signed source points")
        prefix = 2 * prefix + digit


def grouped(b, old_x, old_y, other, metric):
    """Return (output point, normalized conic) on Y²=U³/k+constant."""

    def native(v):
        return tuple(curve.value(b, x) for x in v)

    def add(*terms):
        return tuple(sum(values) % curve.P for values in zip(*terms))

    def mul(l, r):
        return curve.mul2(None, l, r)

    def neg(l):
        return tuple(-v % curve.P for v in l)

    def div(l, r):
        return mul(l, curve.inverse_nat2(r))

    def advice(v):
        return tuple(b.witness(x) for x in v) if b is not None else v

    other_x, other_y = other
    p, y, v, h, k = map(native, (old_x, old_y, other_x, other_y, metric))
    s = div(mul((3, 0), mul(p, p)), mul((2, 0), y))
    j = add(div(mul(s, p), k), neg(y))
    middle = add(div(mul(s, s), k), neg(p), neg(p))
    middle_y = add(j, neg(div(mul(s, middle), k)))
    t = div(mul(k, add(h, neg(middle_y))), add(v, neg(middle)))
    i = add(div(mul(t, v), k), neg(h))
    a = add(s, t)
    ell = add(middle, div(mul(s, t), k))
    constant = add(mul(middle, ell), neg(mul(s, i)), neg(mul(t, j)))
    w = add(div(mul(t, t), k), neg(middle), neg(v))
    wy = add(i, neg(div(mul(t, w), k)))
    g0, g2, g4 = (div(neg(n), a) for n in (mul(k, k), mul(k, ell), constant))
    A, L, G0, G2, G4, W, WY = map(advice, (a, ell, g0, g2, g4, w, wy))
    if b is not None:
        # G0*A=-k² also enforces A!=0. The conic's monic coefficients
        # are L and -A*G4; G2*A=-k*L prepares its evaluated form.
        relation(b, [(1, A, G0), (1, metric, metric)])
        relation(b, [(1, A, G2), (1, metric, L)])
        for x, ordinate, sign in (
            (old_x, old_y, 1),
            (other_x, other_y, 1),
            (W, WY, -1),
        ):
            relation(b, [(1, x, x), (1, L, x), (-1, A, G4), (-sign, A, ordinate)])
        relation(
            b,
            [
                (1, metric, W),
                (2, metric, old_x),
                (1, metric, other_x),
                (2, metric, L),
                (-1, A, A),
            ],
        )
        relation(
            b,
            [
                (1, L, L),
                (-2, A, G4),
                (-1, old_x, old_x),
                (-2, old_x, other_x),
                (-2, old_x, W),
                (-1, other_x, W),
            ],
        )
    return (W, WY), (G0, G2, G4)
