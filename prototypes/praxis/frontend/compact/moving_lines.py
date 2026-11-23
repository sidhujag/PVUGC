"""Scale the variable G2 trace to expose its evaluated Miller-line coefficients.

For the finite G1 point P=(a,b), put t=a/b and z=1/b. Take d²=t*z in
Fp² and k=t²/d. The mapped twist coordinates U=d*x, Y=z*y have incidence
S*U=k*(J+Y), for S=t*s and J=z*I. These are the coefficients of the
evaluated line 1−S*T+J*T³. Squaring the coordinate scale makes the tangent
equation 2*S*J=U²+2*U*U' quadratic, even when t and z are private.
"""

from . import ate, ate_fused, curve
from .condensed_curve import relation, steps
from .tower import WIDTH


def scaled_twist(b, pair, digits=None, direct_groups=False):
    point, q = pair
    active = point[2] if len(point) == 3 else 1
    t0, z0 = ate_fused._normalized_position(b, point)
    # When the pairing is disabled, use t=z=1. Its line is then T times
    # a nonzero Fp6 element. Such a factor disappears under final reduction
    # because its square is in Fp6* and r is odd.
    t, z = (curve.mod(b, linear=[(1, v), (-1, active)], constant=1) for v in (t0, z0))
    tv, zv = (curve.value(b, v) for v in (t, z))
    # A finite BN254 G1 point cannot have x=0 (3 is a nonsquare), or y=0
    # (there is no 2-torsion). Both denominators remain nonzero at infinity.
    # p=3 mod 4. A nonsquare of Fp has a purely imaginary square root in Fp².
    product = tv * zv % curve.P
    root = pow(product, (curve.P + 1) // 4, curve.P)
    imaginary = int(root * root % curve.P != product)
    private = b is not None and not all(isinstance(v, int) for v in (t, z))
    d = (0, root) if imaginary else (root, 0)
    k = curve.mul2(None, (tv * tv % curve.P, 0), curve.inverse_nat2(d))
    if private:
        d, k = tuple(b.witness(a) for a in d), tuple(b.witness(a) for a in k)
        relation(b, [(1, d, d), (-1, (t, 0), (z, 0))])
        relation(b, [(1, k, d), (-1, (t, 0), (t, 0))])

    def transform(point):
        return curve.mul2(b, d, point[0]), tuple(
            curve.mod(b, [(1, z, v)]) for v in point[1]
        )

    # d need not lie in Fp. Apply Frobenius before the change of coordinate.
    q1 = ate._frob_point(b, q)
    q2 = ate._negative(b, ate._frob_point(b, q1))
    tail = tuple(transform(point) for point in (q1, q2, ate._frob_point(b, q2)))
    return active, steps(b, transform(q), k, tail, digits, direct_groups)


def products(b, pairs):
    active, var = scaled_twist(b, pairs[0])
    if len(pairs) == 1:
        for s, j in var:
            vals = [0] * WIDTH
            vals[0] = active
            vals[1], vals[7] = ate_fused._flat_coefficient(b, [((-1, 0), s, 1)])
            vals[3], vals[9] = ate_fused._flat_coefficient(b, [((1, 0), j, 1)])
            yield tuple(vals)
        return
    p, q = pairs[1]
    x, z = ate_fused._normalized_position(b, p)
    ax, az = (curve.mod(b, [(1, active, v)]) for v in (x, z))
    for (s, j), (f, k) in zip(var, ate_fused._fixed(q), strict=True):
        vals = [0] * WIDTH
        low, vals[6] = ate_fused._flat_coefficient(
            b, [(curve.mul2(None, k, (9, 1)), j, z)]
        )
        vals[0] = curve.mod(b, linear=[(1, active), (1, low)])
        vals[1], vals[7] = ate_fused._flat_coefficient(
            b, [((-1, 0), s, 1), ((-1, 0), f, ax)]
        )
        vals[2], vals[8] = ate_fused._flat_coefficient(b, [(f, s, x)])
        vals[3], vals[9] = ate_fused._flat_coefficient(
            b, [((1, 0), j, 1), ((1, 0), k, az)]
        )
        vals[4], vals[10] = ate_fused._flat_coefficient(
            b, [(ate_fused._neg2_const(k), s, z), (ate_fused._neg2_const(f), j, x)]
        )
        yield tuple(vals)


def miller(b, pairs, seed=ate.ONE, inverse_seed=ate.ONE):
    lines = products(b, pairs)
    ops = []
    for d in ate.DIGITS[1:]:
        ops.append(("square", ate_fused._conjugate(b, next(lines))))
        if d:
            ops.append((d, next(lines)))
    ops.extend((("tail", next(lines)), ("tail", next(lines))))
    return ate_fused._run_ops(b, ops, seed, inverse_seed)


def verify(b, statement, proof):
    return ate.verify_with_miller(b, statement, proof, miller)
