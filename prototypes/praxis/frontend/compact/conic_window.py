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


def _raw(table, updates, fixed):
    # F_j is the product of the two Miller functions at scalar j. Vertical
    # divisors, including f_{-j}f_j, lie in the discarded subfield Fp6*.
    base = {1: ate.ONE, 2: paired_torus._flat(table[0])}
    for j, line in zip(range(3, 2 * len(table), 2), table[1:]):
        earlier = base[2] if j == 3 else fp12_mul(None, base[2], base[j - 2])
        base[j] = fp12_mul(None, earlier, paired_torus._flat(line))
    value = ate.ONE
    for square, d, line in updates:
        if square:
            value = fp12_square(None, value)
        value = fp12_mul(None, value, paired_torus._flat(line))
        if abs(d) > 1:
            factor = base[d] if d > 0 else ate_fused._conjugate(None, base[-d])
            value = fp12_mul(None, value, factor)
    return fp12_mul(None, value, fixed)


def _fold(b, table, updates, root):
    # D_j = F_j*z^j. The static curve table supplies the actual line through
    # [j-2]Q and [2]Q, except j=3, whose inputs are [2]Q and Q.
    mul = torus.finite_multiply
    powers = {1: root, 2: mul(b, torus.finite_square(b, root), table[0])}
    for j, line in zip(range(3, 2 * len(table), 2), table[1:]):
        earlier = mul(b, powers[2], powers[1 if j == 3 else j - 2])
        powers[j] = mul(b, earlier, line)
    for square, d, line in updates:
        if d:
            factor = powers[abs(d)]
            line = mul(b, line, factor if d > 0 else torus.inverse(b, factor))
        yield square, 0, line


def verify_width(b, statement, proof, width, direct_groups=False):
    digits = schedule(width)
    handles, pairs, fixed = ate.prepare(b, statement, proof)
    if b is not None and b.layout_only:
        root = torus.Class(torus.ONE, 0)
    else:
        table, iterator = _ops(None, ate._values(b, pairs), digits, direct_groups)
        ops = tuple(iterator)
        f = fp12_pow(_raw(table, ops, fixed), ate_torus.LIFT)
        # The seed itself, z², D_2, both intermediate powers for each odd
        # digit, and every signed main-loop factor must be finite. Each is
        # a nonzero power of z modulo r times a seed-independent line.
        forbidden = 3 + 2 * (len(table) - 1) + sum(bool(d) for d in digits[1:])
        for _ in range(forbidden + 1):
            try:
                root = torus.finite_witness(None, torus.from_fp12(None, f))
                tuple(_fold(None, table, ops, root))
                break
            except torus.InfiniteChart:
                f = fp12_mul(None, f, ate_torus._generator())
        else:
            raise AssertionError("window root chart exhausted")
    root = torus.finite_witness(b, root)
    table, ops = _ops(b, pairs, digits, direct_groups)
    out = conic._dense(b, _fold(b, table, ops, root), root)
    conic._finish(b, out, paired_torus._flat(root), fixed)
    return handles


def verify(b, statement, proof):
    return verify_width(b, statement, proof, 4)
