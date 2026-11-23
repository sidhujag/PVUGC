"""Exact optimal Ate verification in Fp12*/Fp6*, using six coordinates per state.

The quotient by Fp6* preserves the reduced pairing because r divides p^6+1
and gcd(r,p^6-1)=1. Here gcd(lambda,p^6+1)=r: there is no cubic-coset
correction. Frobenius and line evaluation commute with the projection.
"""

from functools import lru_cache
from math import gcd
from . import ate, ate_fused, curve, torus
from .tower import LAMBDA, ORDER, P, R, fp12_mul, fp12_pow

QUOTIENT_ORDER = P**6 + 1
RESIDUE_ORDER = QUOTIENT_ORDER // R
if gcd(LAMBDA, QUOTIENT_ORDER) != R or gcd(LAMBDA, RESIDUE_ORDER) != 1:
    raise ValueError("incorrect BN254 quotient subgroup or root exponent")
LIFT = -pow(LAMBDA, -1, RESIDUE_ORDER) % RESIDUE_ORDER


def _miller(b, pairs, seed, finite=False):
    square = torus.finite_square if finite else torus.square
    mul = torus.finite_multiply if finite else torus.multiply
    mul_line = torus.finite_mul_line if finite else torus.mul_line
    positions = [ate_fused._normalized_position(b, point) for point, _ in pairs]
    mixed = ate_fused._mixed(b, positions)
    lines = [
        iter(ate_fused._fixed(q))
        if all(isinstance(x, int) for coord in q for x in coord)
        else ate_fused.steps(b, q)
        for _, q in pairs
    ]

    def apply_line(acc):
        whole = ate_fused._line_product(b, positions, mixed, [next(t) for t in lines])
        return mul_line(b, acc, whole)

    acc = seed
    z_inverse = torus.inverse(b, seed)
    for digit in ate.DIGITS[1:]:
        acc = apply_line(square(b, acc))
        if digit:
            acc = apply_line(acc)
            acc = mul(b, acc, seed if digit == 1 else z_inverse)
    return apply_line(apply_line(acc))


def _final(b, pairs, seed, fixed, finite):
    mul = torus.finite_multiply if finite else torus.multiply
    mul_line = torus.finite_mul_line if finite else torus.mul_line
    acc = _miller(b, pairs, seed, finite)
    acc = mul_line(b, acc, fixed)
    acc = mul(b, acc, torus.frobenius(b, seed, 1))
    return mul(b, acc, torus.frobenius(b, seed, 3))


@lru_cache(maxsize=1)
def _generator():
    # A nontrivial element of the prime-order group remains nontrivial modulo
    # Fp6*, whose order is coprime to r. This uses public fixed points.
    base = ate.constant_miller(curve.G1, curve.G2)
    gen = fp12_pow(base, ORDER // R)
    if gen == ate.ONE or fp12_pow(gen, R) != ate.ONE:
        raise ValueError("invalid order-r BN254 chart rotation")
    return gen


def _finite_stages():
    # Every independently guarded step has x_i = c_i*z^s_i, with all c_i
    # independent of z. Among rotated roots z*g^j, at most one j can send
    # such a stage to the identity, since r is prime and r does not divide s_i.
    power = 1
    stages = [power]
    for digit in ate.DIGITS[1:]:
        power *= 2
        stages.extend((power, power))  # doubling and multiplication by its line
        if digit:
            stages.append(power)
            power += digit
            stages.append(power)
    stages.extend((power, power, power, power + P, power + P + P**3))
    if any(s % R == 0 for s in stages) or len(stages) >= R:
        raise ValueError("chart-completeness exponent certificate failed")
    return tuple(stages)


def _rotate(pairs, fixed, root):
    g = _generator()
    for _ in range(len(_finite_stages()) + 1):
        seed = torus.from_fp12(None, root)
        try:
            torus.finite_witness(None, seed)
            _final(None, pairs, seed, fixed, True)
            return seed
        except torus.InfiniteChart:
            root = fp12_mul(None, root, g)
    raise AssertionError("order-r rotation exceeded its finite completeness bound")


def _verify(b, statement, proof, finite):
    handles, pairs, fixed = ate.prepare(b, statement, proof)
    if b is not None and b.layout_only:
        native_z = torus.Class(torus.ONE, 0) if finite else torus.IDENTITY
    else:
        native_pairs = ate._values(b, pairs)
        # Raw and normalized lines differ by Fp6* factors. The quotient class
        # is exactly identical, including when either G1 input is infinity.
        raw = fp12_mul(None, ate._miller(None, native_pairs), fixed)
        root = fp12_pow(raw, LIFT)
        native_z = (
            _rotate(native_pairs, fixed, root)
            if finite
            else torus.from_fp12(None, root)
        )
    allocate = torus.finite_witness if finite else torus.witness
    seed = allocate(b, native_z)
    acc = _final(b, pairs, seed, fixed, finite)
    torus.assert_equal(b, acc, torus.frobenius(b, seed, 2))
    return handles


def verify(b, statement, proof):
    """Exact projective verifier supporting infinity as an intermediate state."""
    return _verify(b, statement, proof, False)


def verify_finite(b, statement, proof):
    """Exact finite-chart variant; valid witnesses always admit a finite root."""
    return _verify(b, statement, proof, True)
