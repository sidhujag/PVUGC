"""BN254 Fp12 arithmetic and a deterministic pairing-product residue certificate.

The coefficient order is 1, T, ..., T^11, with i=T^6-9 and i^2=-1.
Pass b=None for native arithmetic. With a builder each output coefficient is a
single foreign-field sum-of-products; squaring folds symmetric terms. Constant
sparsity, unlike the values of witness wires, may change the emitted shape.
"""

from functools import lru_cache

U = 4965661367192848881
P = 36 * U**4 + 36 * U**3 + 24 * U**2 + 6 * U + 1
R = P - 6 * U**2
ORDER = P**12 - 1
ATE = 6 * U + 2
LAMBDA = ATE + P - P**2 + P**3
# gcd(LAMBDA, ORDER)=3R and gcd(R, ORDER/R)=1 for these exact BN254 parameters.
LIFT_EXPONENT = pow(LAMBDA // 3, -1, ORDER // (3 * R))
WIDTH = 12


def fp12_one():
    return (1,) + (0,) * (WIDTH - 1)


def _coefficient_map(degree):
    if degree < WIDTH:
        return ((degree, 1),)
    reduced = {}
    for offset, multiplier in ((6, 18), (12, -82)):
        for index, value in _coefficient_map(degree - offset):
            reduced[index] = reduced.get(index, 0) + multiplier * value
    return tuple(reduced.items())


REDUCTION = tuple(_coefficient_map(i) for i in range(2 * WIDTH - 1))


def _constant_zero(v):
    return isinstance(v, int) and v == 0


def _product(b, left, right, square):
    if len(left) != WIDTH or len(right) != WIDTH:
        raise ValueError("Fp12 requires twelve coefficients")
    if b is None:
        values = [0] * (2 * WIDTH - 1)
        for i, x in enumerate(left):
            if x:
                for j in range(i if square else 0, WIDTH):
                    factor = 2 if square and j != i else 1
                    values[i + j] += factor * x * right[j]
        for i in range(2 * WIDTH - 2, WIDTH - 1, -1):
            values[i - 6] += 18 * values[i]
            values[i - 12] -= 82 * values[i]
        return tuple(v % P for v in values[:WIDTH])

    terms = [[] for _ in range(WIDTH)]
    for i, x in enumerate(left):
        if _constant_zero(x):
            continue
        for j in range(i if square else 0, WIDTH):
            y = right[j]
            if _constant_zero(y):
                continue
            factor = 2 if square and i != j else 1
            for dest, coefficient in REDUCTION[i + j]:
                terms[dest].append((factor * coefficient, x, y))
    return tuple(b.mod(products) for products in terms)


def fp12_mul(b, left, right):
    return _product(b, left, right, False)


def fp12_square(b, value):
    return _product(b, value, value, True)


def fp12_pow(value, exponent):
    """Native exponentiation used to lift a public group computation."""
    if exponent < 0:
        raise ValueError("negative exponent")
    out = fp12_one()
    for bit in bin(exponent)[2:]:
        out = fp12_square(None, out)
        if bit == "1":
            out = fp12_mul(None, out, value)
    return out


@lru_cache(maxsize=12)
def _frobenius_columns(power):
    t = (0, 1) + (0,) * 10
    image = fp12_pow(t, P**power)
    col = fp12_one()
    columns = [col]
    for _ in range(1, WIDTH):
        col = fp12_mul(None, col, image)
        columns.append(col)
    return tuple(columns)


def fp12_frob(b, value, power):
    if len(value) != WIDTH:
        raise ValueError("Fp12 requires twelve coefficients")
    power %= WIDTH
    if not power:
        return tuple(value)
    columns = _frobenius_columns(power)
    result = []
    for k in range(WIDTH):
        terms = [
            (1, col[k], x)
            for col, x in zip(columns, value)
            if col[k] and not _constant_zero(x)
        ]
        if b is None:
            result.append(sum(c * x for _, c, x in terms) % P)
        else:
            result.append(b.mod(terms))
    return tuple(result)


def fp12_value(b, value):
    return tuple(value) if b is None else tuple(b.value(x) for x in value)


def _ate_power(b, value):
    # A fixed width-three sliding window uses only odd powers 1,3,5,7.
    even = fp12_square(b, value)
    odd = {1: value}
    for j in (3, 5, 7):
        odd[j] = fp12_mul(b, odd[j - 2], even)
    bits = bin(ATE)[2:]
    out = None
    while bits:
        if bits[0] == "0":
            out = fp12_square(b, out)
            bits = bits[1:]
            continue
        end = min(3, len(bits))
        while bits[end - 1] == "0":
            end -= 1
        factor = odd[int(bits[:end], 2)]
        if out is None:
            out = factor
        else:
            for _ in range(end):
                out = fp12_square(b, out)
            out = fp12_mul(b, out, factor)
        bits = bits[end:]
    return out


def _assert_nonzero(b, value, native):
    # Existence of twelve coefficients with dot product one tests nonzero with
    # a single base-field equation and makes the shape independent of the pivot.
    pivot = next((j for j, x in enumerate(native) if x), None)
    inverse = pow(native[pivot], -1, P) if pivot is not None else 0
    coeff = [b.witness(inverse if j == pivot else 0) for j in range(WIDTH)]
    b.equal(b.mod([(1, x, y) for x, y in zip(value, coeff)]), 1)


def fp12_residue(b, f):
    """Constrain f to a nonzero R-th power, equivalently f^(ORDER/R)=1.

    In the cyclic multiplicative group, writing f=g^v, h^LAMBDA=f^3 has a
    solution iff gcd(LAMBDA,ORDER)=3R divides 3v, i.e. R divides v. For an
    accepted f the explicit lift h=f^a works, since LAMBDA*a=3 mod ORDER/R.
    Nonzero h is crucial in the cross-multiplied circuit equation.
    """
    values = fp12_value(b, f)
    h_native = (
        fp12_one()
        if b is not None and b.layout_only
        else fp12_pow(values, LIFT_EXPONENT)
    )
    if b is None:
        if not any(h_native):
            raise ValueError("zero target-group residue certificate")
        h = h_native
    else:
        h = tuple(b.witness(x) for x in h_native)
        _assert_nonzero(b, h, h_native)
    lhs = fp12_mul(b, _ate_power(b, h), fp12_frob(b, h, 1))
    lhs = fp12_mul(b, lhs, fp12_frob(b, h, 3))
    rhs = fp12_mul(b, fp12_square(b, f), f)
    rhs = fp12_mul(b, rhs, fp12_frob(b, h, 2))
    if b is None:
        if lhs != rhs:
            raise ValueError("Fp12 element fails the pairing-product test")
    else:
        for left, right in zip(lhs, rhs):
            b.equal(left, right)
