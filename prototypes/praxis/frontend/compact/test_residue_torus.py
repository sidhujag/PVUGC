import io
import json
import random
import unittest

from . import torus
from .bqs import ONE, P, R, bit_value, check_row
from .residue_bqs import MAX_PRODUCTS, PackedResidueBuilder, ResidueBuilder
from .tower import fp12_frob, fp12_mul, fp12_square


def satisfied(rows, assignment):
    return [
        check_row(json.loads(row), lambda atom: bit_value(assignment, atom))
        for row in rows.splitlines()
    ]


class ResidueTests(unittest.TestCase):
    def test_packed_signed_residuals(self):
        stream = io.BytesIO()
        b = PackedResidueBuilder(stream)
        x, y = b.bit(0), b.bit(0)
        b._row([(1, (x.start, x.width), ONE)], exact_bound=1)
        b._row([(-1, (y.start, y.width), ONE)], exact_bound=1)
        self.assertEqual(b.shape()["constraints"], 1)
        self.assertEqual(b.shape()["constraints"], 1)
        for mask in range(4):
            self.assertEqual(satisfied(stream.getvalue(), bytes([mask])), [mask == 0])

    def test_foreign_modulus_alias(self):
        stream = io.BytesIO()
        b = ResidueBuilder(stream, layout_only=True)
        x = b.witness(R)
        b.assert_zero([], [(1, x)])
        self.assertEqual(satisfied(stream.getvalue(), b.assignment), [True, False])

    def test_dense_coefficients_with_fallback(self):
        rng = random.Random(6407)
        b = ResidueBuilder()
        operands = [b.witness(rng.randrange(P)) for _ in range(180)]
        for n in (1, 4, 16, 35, 90):
            terms = [
                (rng.randrange(P), operands[2 * i], operands[2 * i + 1])
                for i in range(n)
            ]
            raw = sum(c * b.value(x) * b.value(y) for c, x, y in terms)
            self.assertEqual(b.value(b.mod(terms)), raw % P)
        self.assertLessEqual(b.max_products, MAX_PRODUCTS)
        self.assertLess(b.max_limb_residual, R)


class TorusTests(unittest.TestCase):
    def setUp(self):
        rng = random.Random(89354)
        self.raw = tuple(rng.randrange(P) for _ in range(12))
        self.real = self.raw[::2]
        self.base = torus.from_fp12(None, self.raw)
        self.imag = torus.from_fp12(None, (0, 1) + (0,) * 10)
        self.identity = torus.Class(self.real, 1)

    def test_native_reference_and_exceptional_charts(self):
        for mask in (self.raw, (0, 1) + (0,) * 10, (1,) + (0,) * 11):
            x = torus.from_fp12(None, mask)
            for y in (self.raw, fp12_frob(None, mask, 6)):
                expected = torus.from_fp12(None, fp12_mul(None, mask, y))
                torus.assert_equal(
                    None, torus.multiply(None, x, torus.from_fp12(None, y)), expected
                )
                torus.assert_equal(None, torus.mul_line(None, x, y), expected)
            expected = torus.from_fp12(None, fp12_square(None, mask))
            torus.assert_equal(None, torus.square(None, x), expected)
            for n in (0, 1, 2, 3, 6):
                torus.assert_equal(
                    None,
                    torus.frobenius(None, x, n),
                    torus.from_fp12(None, fp12_frob(None, mask, n)),
                )

    def test_all_charts_use_the_same_rows(self):
        layouts = set()
        for x, y in [
            (self.base, self.base),
            (self.base, torus.inverse(None, self.base)),
            (self.identity, self.imag),
            (self.imag, self.imag),
            (self.identity, self.identity),
        ]:
            b = ResidueBuilder()
            u, v = torus.witness(b, x), torus.witness(b, y)
            square, prod = torus.square(b, u), torus.multiply(b, u, v)
            expected = torus.witness(b, torus.square(None, x))
            compared = torus.witness(b, torus.multiply(None, x, y))
            torus.assert_equal(b, square, expected)
            torus.assert_equal(b, prod, compared)
            layouts.add((b.bits, b.rows, b.digest.hexdigest()))
        self.assertEqual(len(layouts), 1)

    def test_finite_rows_and_zero_source(self):
        stream = io.BytesIO()
        b = ResidueBuilder(stream)
        x = torus.finite_witness(b, self.base)
        z = torus.finite_square(b, x)
        z2 = torus.finite_multiply(b, x, x)
        torus.assert_equal(b, z, z2)
        line = tuple(b.witness(c) for c in self.raw)
        torus.assert_equal(b, torus.finite_mul_line(b, x, line), z)
        self.assertTrue(all(satisfied(stream.getvalue(), b.assignment)))
        with self.assertRaises(torus.InfiniteChart):
            torus.finite_multiply(None, self.base, torus.inverse(None, self.base))
        stream = io.BytesIO()
        b = ResidueBuilder(stream, layout_only=True)
        torus.from_fp12(b, [b.witness(0) for _ in range(12)])
        self.assertFalse(all(satisfied(stream.getvalue(), b.assignment)))
