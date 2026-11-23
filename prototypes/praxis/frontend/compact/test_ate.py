"""Regression checks for the optimized BN254 fixed-statement encoder."""

import json
import unittest
from math import gcd

from . import ate, curve
from .bqs import Builder
from .test_curve import FIXTURE
from .tower import ATE, LAMBDA, ORDER, P, R, fp12_frob, fp12_mul, fp12_one, fp12_pow


class OptimalAte(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(FIXTURE.read_text())

    def test_frobenius_and_residue_constants(self):
        self.assertEqual(gcd(LAMBDA, ORDER), 3 * R)
        self.assertEqual(gcd(R, ORDER // R), 1)
        self.assertEqual(gcd(27, ate.K), 1)
        table = ate.correction_table()
        self.assertEqual(len(set(table)), 27)
        arbitrary = (2, 1, 7) + (0,) * 9
        self.assertEqual(fp12_frob(None, arbitrary, 1), fp12_pow(arbitrary, P))
        self.assertEqual(
            fp12_frob(None, fp12_frob(None, arbitrary, 1), 2),
            fp12_frob(None, arbitrary, 3),
        )
        # Exercise all cubic cosets explicitly; every correction is a 27th root.
        for expected in (0, 1, 2):
            f = fp12_mul(None, fp12_pow(arbitrary, R), table[expected])
            z, e = ate.root_and_correction(f)
            self.assertIn(e, (0, 1, 2))
            self.assertEqual(
                fp12_mul(None, fp12_mul(None, f, table[e]), fp12_pow(z, LAMBDA)),
                fp12_one(),
            )

    def test_twist_order_and_naf_exception_certificate(self):
        n = R * (2 * P - R)
        self.assertEqual(n % 2, 1)
        prefix = 1
        for digit in ate.DIGITS[1:]:
            self.assertEqual(gcd(prefix, n), 1)
            prefix *= 2
            self.assertEqual(gcd(prefix, n), 1)
            if digit:
                for sign in (-1, 1):
                    self.assertEqual(gcd(prefix + sign * digit, n), 1)
            prefix += digit
            self.assertEqual(gcd(prefix, n), 1)
        self.assertEqual(prefix, ATE)
        trace = P + 1 - R
        norm = lambda a, b: a * a + trace * a * b + P * b * b
        for a, b in ((ATE, -1), (ATE, 1), (ATE - P, 1 + trace), (ATE + P, 1 - trace)):
            self.assertEqual(gcd(norm(a, b), n), 1)
        self.assertEqual(
            gcd(norm(ATE + P - P * trace, 1 - trace + trace * trace - P), n), R
        )

    def test_native_fixtures_and_mixed_identity(self):
        for proof in self.data["witnesses"]:
            ate.verify(None, self.data["statement"], proof)
        gen = ate.constant_miller(curve.G1, curve.G2)
        self.assertNotEqual(fp12_pow(gen, ORDER // R), fp12_one())
        changed = dict(proof)
        changed["c"] = proof["a"]
        with self.assertRaises(ValueError):
            ate.verify(None, self.data["statement"], changed)
        zero1 = {"x": "0", "y": "0"}
        zero2 = {"x": ["0", "0"], "y": ["0", "0"]}
        neutral = dict(self.data["statement"], L=zero1, alpha=zero1)
        for a, b in ((zero1, proof["b"]), (proof["a"], zero2), (zero1, zero2)):
            ate.verify(None, neutral, {"a": a, "b": b, "c": zero1})
        # Subgroup checking must still bind the supplied B when A is infinity.
        outside = {
            "x": ["2", "1"],
            "y": [
                "7292567877523311580221095596750716176434782432868683424513645834767876293070",
                "19659275751359636165940301690575149581329631496732780143538578556285923319774",
            ],
        }
        for engine in (None, Builder()):
            with self.assertRaises(ValueError):
                ate.verify(engine, neutral, {"a": zero1, "b": outside, "c": zero1})
