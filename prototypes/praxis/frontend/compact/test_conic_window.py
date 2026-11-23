"""Verify signed window curves, subgroup exceptional cases and reduced Miller values."""

import json
import unittest
from math import gcd

from . import ate, conic_window
from .test_curve import FIXTURE
from .tower import ATE, ORDER, P, R, fp12_mul, fp12_pow


class SignedWindow(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(FIXTURE.read_text())

    def test_window_domain_certificate(self):
        twist_order = R * (2 * P - R)
        for width in range(3, 7):
            digits = conic_window.schedule(width)
            self.assertEqual(digits[:2], (1, 0))
            maximum = max(abs(d) for d in digits)
            for j in range(1, maximum + 3):
                self.assertEqual(gcd(j, twist_order), 1)
            # Precomputation [2]Q+Q, followed by [j-2]Q+[2]Q.
            for j in range(3, maximum + 1, 2):
                a, b = (2, 1) if j == 3 else (j - 2, 2)
                for n in (a, b, a + b, a - b):
                    self.assertEqual(gcd(n, twist_order), 1)
            prefix = 1
            for d in digits[1:]:
                self.assertEqual(gcd(prefix, twist_order), 1)
                doubled = 2 * prefix
                if d:
                    self.assertEqual(gcd(doubled - d, twist_order), 1)
                    self.assertEqual(gcd(doubled + d, twist_order), 1)
                    self.assertNotIn(d % R, ((-prefix) % R, doubled % R))
                prefix = doubled + d
            self.assertEqual(prefix, ATE)
            self.assertTrue(all((-(P**2) - v) % R for v in (-ATE, -P, ATE + P)))

    def test_optimized_schedule_and_final_chart(self):
        from . import direct_conic

        digits = conic_window.optimized_schedule()
        self.assertEqual(digits[0], 3)
        self.assertEqual(sum(d << j for j, d in enumerate(reversed(digits))), ATE)
        self.assertEqual(len(digits) - 1, 62)
        self.assertEqual(sum(bool(d) for d in digits[1:]), 11)
        direct_conic.certify(digits)
        order = R * (2 * P - R)
        prefix = digits[0]
        for digit in digits[1:]:
            self.assertEqual(gcd(prefix, order), 1)
            if digit:
                self.assertEqual(gcd(2 * prefix - digit, order), 1)
                self.assertEqual(gcd(2 * prefix + digit, order), 1)
                self.assertNotIn(digit % R, ((-prefix) % R, 2 * prefix % R))
            prefix = 2 * prefix + digit
        self.assertEqual(prefix, ATE)
        self.assertNotEqual((P**2 - P**3) % R, 0)
        self.assertEqual((P**2 - P**3 - P) % R, ATE % R)
        self.assertNotEqual(ATE % R, 0)
        s = self.data["statement"]
        first, second = self.data["witnesses"]
        zero1 = {"x": "0", "y": "0"}
        zero2 = {"x": ["0", "0"], "y": ["0", "0"]}
        for proof in (
            first,
            second,
            dict(first, c=first["a"]),
            dict(first, a=zero1),
            dict(first, b=zero2),
            dict(first, c=zero1),
        ):
            _, pairs, fixed = ate.prepare(None, s, proof)
            table, ops = conic_window._ops(None, pairs, digits, True)
            self.assertEqual(
                fp12_pow(conic_window._raw(table, ops, fixed, digits[0]), ORDER // R),
                fp12_pow(fp12_mul(None, ate._miller(None, pairs), fixed), ORDER // R),
            )
        for proof in (first, second):
            conic_window.verify_optimized(None, s, proof)
        with self.assertRaises(ValueError):
            conic_window.verify_optimized(None, dict(s, L={"x": "1", "y": "2"}), first)
        for delta in (s["delta"], zero2):
            for a, b in ((zero1, zero2), (first["a"], zero2), (zero1, first["b"])):
                conic_window.verify_optimized(
                    None,
                    dict(s, L=zero1, alpha=zero1, delta=delta),
                    {"a": a, "b": b, "c": zero1},
                )

    def test_quotient_equivalence_and_correct_input(self):
        s = self.data["statement"]
        first, second = self.data["witnesses"]
        zero1 = {"x": "0", "y": "0"}
        zero2 = {"x": ["0", "0"], "y": ["0", "0"]}
        for proof in (
            first,
            second,
            dict(first, c=first["a"]),
            dict(first, a=zero1),
            dict(first, b=zero2),
            dict(first, c=zero1),
        ):
            _, pairs, fixed = ate.prepare(None, s, proof)
            old = fp12_pow(fp12_mul(None, ate._miller(None, pairs), fixed), ORDER // R)
            table, ops = conic_window._ops(None, pairs, conic_window.schedule(4))
            self.assertEqual(
                fp12_pow(conic_window._raw(table, ops, fixed), ORDER // R), old
            )
        for width in range(3, 7):
            for proof in (first, second):
                conic_window.verify_width(None, s, proof, width)
        with self.assertRaises(ValueError):
            conic_window.verify(None, dict(s, L={"x": "1", "y": "2"}), first)
        outside = {
            "x": ["2", "1"],
            "y": [
                "7292567877523311580221095596750716176434782432868683424513645834767876293070",
                "19659275751359636165940301690575149581329631496732780143538578556285923319774",
            ],
        }
        for verify in (conic_window.verify, conic_window.verify_optimized):
            with self.assertRaises(ValueError):
                verify(
                    None,
                    dict(s, L=zero1, alpha=zero1),
                    {"a": zero1, "b": outside, "c": zero1},
                )
        for delta in (s["delta"], zero2):
            for a, b in ((zero1, zero2), (first["a"], zero2), (zero1, first["b"])):
                conic_window.verify(
                    None,
                    dict(s, L=zero1, alpha=zero1, delta=delta),
                    {"a": a, "b": b, "c": zero1},
                )
