"""Conic batching geometry, exceptional slopes and original verifier agreement."""

import json
import unittest

from . import ate, conic
from .test_curve import FIXTURE
from .tower import ATE, ORDER, P, R, fp12_mul, fp12_pow


class ConicMiller(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(FIXTURE.read_text())
        cls.zero1 = {"x": "0", "y": "0"}
        cls.zero2 = {"x": ["0", "0"], "y": ["0", "0"]}

    def test_slope_sum_exception_certificate(self):
        # A reflected chord through aQ,bQ meets the curve at -aQ,-bQ,(a+b)Q.
        # Sigma zero would make the next chord this very same line.
        old = 1
        for digit in ate.DIGITS[1:]:
            if digit:
                self.assertTrue(all((digit - x) % R for x in (-old, 2 * old)))
            old = 2 * old + digit
        self.assertEqual(old, ATE)
        self.assertTrue(all((-(P**2) - x) % R for x in (-ATE, -P, ATE + P)))

    def test_unreduced_representatives_and_mixed_identities(self):
        statement = self.data["statement"]
        first, second = self.data["witnesses"]
        cases = (
            first,
            second,
            dict(first, c=first["a"]),
            dict(first, a=self.zero1),
            dict(first, b=self.zero2),
            dict(first, c=self.zero1),
        )
        reduced = []
        for proof in cases:
            _, pairs, fixed = ate.prepare(None, statement, proof)
            old = fp12_mul(None, ate._miller(None, pairs), fixed)
            new = conic._raw(tuple(conic._ops(None, pairs)), fixed)
            expected = fp12_pow(old, ORDER // R)
            reduced.append(expected)
            self.assertEqual(fp12_pow(new, ORDER // R), expected)
        self.assertTrue(any(x != ate.ONE for x in reduced))

    def test_verifier_and_hostile_g2(self):
        statement = self.data["statement"]
        for proof in self.data["witnesses"]:
            conic.verify(None, statement, proof)
        with self.assertRaises(ValueError):
            conic.verify(None, dict(statement, L={"x": "1", "y": "2"}), proof)
        neutral = dict(statement, alpha=self.zero1, L=self.zero1)
        for delta in (statement["delta"], self.zero2):
            for a, b in (
                (self.zero1, self.zero2),
                (self.zero1, proof["b"]),
                (proof["a"], self.zero2),
            ):
                conic.verify(
                    None, dict(neutral, delta=delta), {"a": a, "b": b, "c": self.zero1}
                )
        outside = {
            "x": ["2", "1"],
            "y": [
                "7292567877523311580221095596750716176434782432868683424513645834767876293070",
                "19659275751359636165940301690575149581329631496732780143538578556285923319774",
            ],
        }
        with self.assertRaises(ValueError):
            conic.verify(
                None, neutral, {"a": self.zero1, "b": outside, "c": self.zero1}
            )
