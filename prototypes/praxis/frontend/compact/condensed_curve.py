"""Emit G2 Miller-line equations using x coordinates and incident lines.

For the previous output point, y = I_old - s_old*x. The new line
y = s*x - I therefore gives (s + s_old)*x = I + I_old. On a doubling
step, substituting x' = s² - 2x into the tangent equation gives
2sI = x² + 2xx'. Both identities are quadratic in the *stored* values.
"""

from . import ate, curve


def relation(b, products, linear=()):
    """Assert a quadratic Fp² equation directly in two base-field rows."""
    real = []
    imag = []
    for k, (x, y), (u, v) in products:
        real.extend(((k, x, u), (-k, y, v)))
        imag.extend(((k, x, v), (k, y, u)))
    curve.zero(b, real, [(k, a[0]) for k, a in linear])
    curve.zero(b, imag, [(k, a[1]) for k, a in linear])


def _value2(b, a):
    return tuple(curve.value(b, x) for x in a)


def _advice(b, v, variable):
    return tuple(b.witness(x) for x in v) if variable else v


def steps(b, q, metric=(1, 0), tail=None, digits=None, direct_groups=False):
    # The circuit shape depends only on BN254's public signed Miller digits.
    variable = b is not None and (
        any(not isinstance(x, int) for x in metric)
        or any(not isinstance(x, int) for part in q for x in part)
    )
    native_metric = _value2(b, metric)
    inv_metric = curve.inverse_nat2(native_metric)
    unscaled = metric == (1, 0)
    x, ordinate = q
    last = None

    def advance(other=None):
        nonlocal x, last
        old_x = _value2(b, x)
        if last is None:
            old_y = _value2(b, ordinate)
        else:
            last_s, last_i = (_value2(b, a) for a in last)
            old_y = curve.subtract2(
                None,
                last_i,
                curve.mul2(None, inv_metric, curve.mul2(None, last_s, old_x)),
            )

        if other is None:
            numerator = tuple(3 * v % curve.P for v in curve.mul2(None, old_x, old_x))
            denominator = tuple(2 * v % curve.P for v in old_y)
            other_x = x
        else:
            other_x, other_y = other
            numerator = curve.subtract2(None, _value2(b, other_y), old_y)
            numerator = curve.mul2(None, native_metric, numerator)
            denominator = curve.subtract2(None, _value2(b, other_x), old_x)

        native_s = curve.mul2(None, numerator, curve.inverse_nat2(denominator))
        native_i = curve.subtract2(
            None, curve.mul2(None, inv_metric, curve.mul2(None, native_s, old_x)), old_y
        )
        slope = _advice(b, native_s, variable)
        intercept = _advice(b, native_i, variable)
        s, t = slope

        if last is None:
            relation(
                b, [(1, slope, x), (-1, metric, intercept), (-1, metric, ordinate)]
            )
        else:
            relation(
                b,
                [
                    (1, slope, x),
                    (1, last[0], x),
                    (-1, metric, intercept),
                    (-1, metric, last[1]),
                ],
            )

        if unscaled:
            xx = (
                curve.mod(b, [(1, s, s), (-1, t, t)], [(-1, x[0]), (-1, other_x[0])]),
                curve.mod(b, [(2, s, t)], [(-1, x[1]), (-1, other_x[1])]),
            )
        else:
            # metric*(x' + x + u) = s² also holds for a chord.
            nn = curve.mul2(None, inv_metric, curve.mul2(None, native_s, native_s))
            old_other = _value2(b, other_x)
            xx = _advice(
                b,
                tuple((n - v - w) % curve.P for n, v, w in zip(nn, old_x, old_other)),
                variable,
            )
            relation(
                b,
                [
                    (1, metric, xx),
                    (1, metric, x),
                    (1, metric, other_x),
                    (-1, slope, slope),
                ],
            )
        if other is None:
            relation(b, [(2, slope, intercept), (-1, x, x), (-2, x, xx)])
        else:
            relation(
                b, [(1, slope, other_x), (-1, metric, intercept), (-1, metric, other_y)]
            )

        x = xx
        last = slope, intercept
        return last

    def snapshot():
        if last is None:
            return x, ordinate
        s, i = last
        product = curve.mul2(None, _value2(b, s), _value2(b, x))
        v = curve.subtract2(None, _value2(b, i), curve.mul2(None, inv_metric, product))
        y = _advice(b, v, variable)
        relation(b, [(1, metric, y), (1, s, x), (-1, metric, i)])
        return x, y

    def composite(point):
        nonlocal x, ordinate, last
        p, y = snapshot()
        (x, ordinate), coeffs = direct_conic.grouped(b, p, y, point, metric)
        last = None
        return coeffs

    if direct_groups:
        from . import direct_conic

        direct_conic.certify(tuple(ate.DIGITS if digits is None else digits))

    if digits is None:
        negative_q = ate._negative(b, q)
        for digit in ate.DIGITS[1:]:
            if direct_groups and digit:
                yield composite(q if digit == 1 else negative_q)
                continue
            yield advance()
            if digit:
                yield advance(q if digit == 1 else negative_q)
    else:
        # Emit the fixed window table, then the live line sequence. The main
        # ladder's first doubling is exactly the precomputed [2]Q, so its
        # point and line are shared without duplicate constraints.
        maximum = max(abs(d) for d in digits)
        twice_line = advance()
        twice = snapshot()
        odd = {1: q}
        yield twice_line
        for j in range(3, maximum + 1, 2):
            line = advance(q if j == 3 else twice)
            odd[j] = snapshot()
            yield line
        if digits[0] != 1 or digits[1] != 0:
            raise ValueError("this window requires leading digits one and zero")
        x, last = twice[0], twice_line
        for index, digit in enumerate(digits[1:]):
            if direct_groups and digit:
                point = odd[abs(digit)]
                yield composite(point if digit > 0 else ate._negative(b, point))
                continue
            yield twice_line if index == 0 else advance()
            if digit:
                point = odd[abs(digit)]
                yield advance(point if digit > 0 else ate._negative(b, point))
    if tail is None:
        q1 = ate._frob_point(b, q)
        q2 = ate._negative(b, ate._frob_point(b, q1))
        target = ate._frob_point(b, q2)
    else:
        q1, q2, target = tail
    yield advance(q1)
    final_line = advance(q2)
    target_x, target_y = target
    for v, w in zip(x, target_x):
        curve.zero(b, linear=[(1, v), (-1, w)])
    slope, intercept = final_line
    relation(b, [(-1, slope, x), (1, metric, intercept), (-1, metric, target_y)])
    yield final_line
