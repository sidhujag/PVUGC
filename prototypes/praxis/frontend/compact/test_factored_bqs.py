import copy
import io
import json
import random
import unittest

from .bqs import P, R, bit_value
from .factored_bqs import (
    FORMAT,
    MAX_PRODUCTS,
    FactoredBuilder,
    PackedFactoredBuilder,
    affine_products,
    evaluate,
    inspect_row,
    instantiated_factors,
    praxis_forms,
    validate_stream,
)


def expanded(row, get):
    factors = list(affine_products(row))
    assert len(factors) <= MAX_PRODUCTS
    explicit = [
        (a, get(a) % R, sum(c * get(b) for c, b in right) % R) for a, right in factors
    ]
    assert explicit == list(instantiated_factors(row, get))
    return sum(get(a) * sum(c * get(b) for c, b in right) for a, right in factors)


class FactoredTests(unittest.TestCase):
    def test_praxis_export_indexes_original_boolean_witness_only(self):
        sink = io.BytesIO()
        b = PackedFactoredBuilder(sink)
        x = b.unsigned(31, 9)
        y = b.unsigned(255, 11)
        b.assert_zero([(3, x, y)], [(13, y)], constant=-(3 * 31 * 255 + 13 * 255))
        b.shape()
        for row in map(json.loads, sink.getvalue().splitlines()):
            forms = list(praxis_forms(row, b.bits))
            self.assertTrue(forms)
            for data in [b.assignment, bytes([0x7D]) * len(b.assignment)]:

                def read(f, data=data):
                    const, terms = f
                    self.assertTrue(
                        all(0 <= i < b.bits and 0 < c < R for i, c in terms)
                    )
                    return (
                        const + sum(c * bit_value(data, (i, 1)) for i, c in terms)
                    ) % R

                self.assertEqual(
                    sum(read(l) * read(r) for l, r in forms) % R,
                    evaluate(row, lambda a, data=data: bit_value(data, a)) % R,
                )

    def test_expanded_forms_agree_even_on_arbitrary_assignments(self):
        sink = io.BytesIO()
        b = PackedFactoredBuilder(sink)
        rng = random.Random(62711)
        x = b.witness(rng.randrange(P))
        y = b.witness(rng.randrange(P))
        term = [(rng.randrange(P), x, y), (-13, x, x)]
        z = b.mod(term, [(73, y)], constant=64)
        b.assert_zero(term, [(73, y), (-1, z)], constant=64)
        # An explicit raw direct bit/product row has the same semantics.
        flag = b.bit(0)
        b._row([(1, (flag.start, 1), (x.start, 9))], exact_bound=511)
        shape = b.shape()
        rows = list(map(json.loads, sink.getvalue().splitlines()))
        self.assertEqual(len(rows), shape["constraints"])
        for row in rows:
            forms, _ = inspect_row(row, b.bits)
            self.assertLessEqual(len(forms), shape["max_products"])
            for data in (b.assignment, rng.randbytes(len(b.assignment))):
                get = lambda a, data=data: bit_value(data, a)
                self.assertEqual(expanded(row, get) % R, evaluate(row, get) % R)
            self.assertEqual(evaluate(row, lambda a: bit_value(b.assignment, a)) % R, 0)

    def test_native_modulus_alias_requires_low_row(self):
        sink = io.BytesIO()
        b = FactoredBuilder(sink, layout_only=True)
        x = b.witness(R)
        b.assert_zero([], [(1, x)])
        rows = list(map(json.loads, sink.getvalue().splitlines()))
        self.assertEqual(
            [
                evaluate(row, lambda a: bit_value(b.assignment, a)) % R == 0
                for row in rows
            ],
            [True, False],
        )

    def test_rejects_malformed_recipes_and_untrusted_stream(self):
        sink = io.BytesIO()
        b = FactoredBuilder(sink)
        z = b.witness(37)
        v = b.mod([(1, z, z)])
        b.assert_zero([], [(1, v)], constant=-(37**2))
        shape = b.shape()
        rows = list(map(json.loads, sink.getvalue().splitlines()))
        source, low = rows[0], rows[1]
        coord = {
            n: [z.start, z.width]
            for n in ("ax", "ay", "bx0", "bx1", "by0", "by1", "cx", "cy")
        }
        meta = dict(format=FORMAT, fr=str(R), coordinates=coord, **shape)
        sink.seek(0)
        self.assertEqual(validate_stream(sink, b.assignment, meta)["a"]["x"], "37")
        for i, value in [(1, 0), (1, 255), (2, 999), (4, True), (5, [0, 999])]:
            bad = copy.deepcopy(source)
            bad[i] = value
            with self.assertRaises(ValueError):
                inspect_row(bad, b.bits)
        bad = copy.deepcopy(source)
        bad[3][0][1] = [-1, 1]
        with self.assertRaises(ValueError):
            inspect_row(bad, b.bits)
        bad = copy.deepcopy(source)
        bad[5][0] = 0
        with self.assertRaisesRegex(ValueError, "aliased"):
            inspect_row(bad, b.bits)
        bad = copy.deepcopy(low)
        bad[2] += 1
        with self.assertRaises(ValueError):
            inspect_row(bad, b.bits)
        bad = ["pack", [[1, low], [1, low]]]
        with self.assertRaises(ValueError):
            inspect_row(bad, b.bits)
        bad = ["pack", [[1, source], [1, low]]]
        with self.assertRaises(ValueError):
            inspect_row(bad, b.bits)
        tampered = sink.getvalue().replace(b"digit", b"digits", 1)
        with self.assertRaisesRegex(ValueError, "pinned"):
            validate_stream(io.BytesIO(tampered), b.assignment, meta)
        data = bytearray(b.assignment)
        data[0] ^= 1
        with self.assertRaisesRegex(ValueError, "unsatisfied"):
            validate_stream(io.BytesIO(sink.getvalue()), data, meta)
