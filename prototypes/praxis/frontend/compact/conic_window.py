"""Fixed signed-digit Miller ladder with a shared table of true odd Miller factors."""

from itertools import islice

from . import ate, ate_fused, ate_torus, conic, paired_torus, torus
from .tower import ATE, fp12_mul, fp12_pow, fp12_square


def _digits(n, width):
    rev = []
    while n:
        digit = n % (1 << width) if n & 1 else 0
        if digit >= 1 << (width - 1):
            digit -= 1 << width
        rev.append(digit)
        n = (n - digit) // 2
    return tuple(reversed(rev))


def schedule(width):
    if width not in (3, 4, 5, 6):
        raise ValueError("unsupported signed width")
    digits = _digits(ATE, width)
    # A leading 13 or 3 can be recoded in ordinary nonadjacent binary. This
    # retains leading 1 and lets the source and root start at Q and z.
    return _digits(digits[0], 2) + digits[1:]


def _ops(b, pairs, digits, direct_groups=False):
    updates = conic._ops(b, pairs, digits, direct_groups)
    table = tuple(
        line for _, _, line in islice(updates, (max(abs(d) for d in digits) + 1) // 2)
    )
    return table, updates


def _raw(table, updates, fixed, initial=1):
    # F_j is the product of the two Miller functions at scalar j. Vertical
    # divisors, including f_{-j}f_j, lie in the discarded subfield Fp6*.
    base = {1: ate.ONE, 2: paired_torus._flat(table[0])}
    for j, line in zip(range(3, 2 * len(table), 2), table[1:]):
        earlier = base[2] if j == 3 else fp12_mul(None, base[2], base[j - 2])
        base[j] = fp12_mul(None, earlier, paired_torus._flat(line))
    value = base[initial]
    for square, d, line in updates:
        if square:
            value = fp12_square(None, value)
        value = fp12_mul(None, value, paired_torus._flat(line))
        if abs(d) > 1:
            factor = base[d] if d > 0 else ate_fused._conjugate(None, base[-d])
            value = fp12_mul(None, value, factor)
    return fp12_mul(None, value, fixed)


def _powers(b, table, root):
    # D_j = F_j*z^j. The static curve table supplies the actual line through
    # [j-2]Q and [2]Q, except j=3, whose inputs are [2]Q and Q.
    mul = torus.finite_multiply
    powers = {1: root, 2: mul(b, torus.finite_square(b, root), table[0])}
    for j, line in zip(range(3, 2 * len(table), 2), table[1:]):
        earlier = mul(b, powers[2], powers[1 if j == 3 else j - 2])
        powers[j] = mul(b, earlier, line)
    return powers


def _fold(b, table, updates, root, powers=None):
    if powers is None:
        powers = _powers(b, table, root)
    mul = torus.finite_multiply
    for square, d, line in updates:
        if d:
            factor = powers[abs(d)]
            line = mul(b, line, factor if d > 0 else torus.inverse(b, factor))
        yield square, 0, line


def verify_width(b, statement, proof, width, direct_groups=False):
    return _verify_schedule(b, statement, proof, schedule(width), direct_groups)


def _verify_schedule(
    b, statement, proof, digits, direct_groups, projective_finish=False
):
    handles, pairs, fixed = ate.prepare(b, statement, proof)
    if b is not None and b.layout_only:
        root = torus.Class(torus.ONE, 0)
    else:
        table, iterator = _ops(None, ate._values(b, pairs), digits, direct_groups)
        ops = tuple(iterator)
        f = fp12_pow(_raw(table, ops, fixed, digits[0]), ate_torus.LIFT)
        # The seed itself, z², D_2, both intermediate powers for each odd
        # digit, and every signed main-loop factor must be finite. Each is
        # a nonzero power of z modulo r times a seed-independent line.
        forbidden = (
            3
            + 2 * (len(table) - 1)
            + sum(bool(d) for d in digits[1:])
            + 2 * projective_finish
        )
        for _ in range(forbidden + 1):
            try:
                root = torus.finite_witness(None, torus.from_fp12(None, f))
                tuple(_fold(None, table, ops, root))
                if projective_finish:
                    _rhs(None, root)
                break
            except torus.InfiniteChart:
                f = fp12_mul(None, f, ate_torus._generator())
        else:
            raise AssertionError("window root chart exhausted")
    root = torus.finite_witness(b, root)
    table, ops = _ops(b, pairs, digits, direct_groups)
    if digits[0] == 1:
        out = conic._dense(b, _fold(b, table, ops, root), root)
    else:
        powers = _powers(b, table, root)
        out = conic._dense(b, _fold(b, table, ops, root, powers), powers[digits[0]])
    if projective_finish:
        rhs = _rhs(b, root)
        lhs = fp12_mul(b, out, fixed)
        torus._equals_zero(
            b, (1, 0, rhs.a, tuple(lhs[1::2])), (-1, 0, torus.ONE, tuple(lhs[::2]))
        )
    else:
        conic._finish(b, out, paired_torus._flat(root), fixed)
    return handles


def verify(b, statement, proof):
    return verify_width(b, statement, proof, 4)


def _rhs(b, root):
    f2 = torus.frobenius(b, root, 2)
    f3 = torus.inverse(b, torus.frobenius(b, root, 3))
    f1 = torus.inverse(b, torus.frobenius(b, root, 1))
    return torus.finite_multiply(b, torus.finite_multiply(b, f2, f3), f1)


def optimized_schedule():
    # Signed expansion with 62 doublings and 11 additions using the same
    # odd table. Initialize at [3]Q and F_3*z³ from that table.
    nonzero = {
        62: 3,
        61: 7,
        55: -5,
        48: -7,
        44: 7,
        35: 7,
        30: 7,
        23: -3,
        17: -5,
        11: 7,
        7: 7,
        3: 5,
    }
    return tuple(nonzero.get(j, 0) for j in range(62, -1, -1))


def verify_optimized(b, statement, proof):
    return _verify_schedule(b, statement, proof, optimized_schedule(), True, True)
