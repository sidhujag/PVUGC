"""Regression checks for scoped Miller normalization and root chart completeness."""

import json
import unittest
from math import gcd

from . import ate, ate_fused, ate_torus, curve, moving_lines
from .test_curve import FIXTURE
from .tower import ORDER, P, R, fp12_pow


class FusedMiller(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads(FIXTURE.read_text())

    def test_norm_changes_only_a_subfield_factor(self):
        statement, proof = self.data["statement"], self.data["witnesses"][0]
        _, pairs, _ = ate.prepare(None, statement, proof)
        old = ate._miller(None, pairs)
        normalized = ate_fused._miller(None, pairs)
        self.assertEqual(gcd(R, P**6 - 1), 1)
        self.assertNotEqual(normalized, old)
        self.assertEqual(fp12_pow(old, ORDER // R), fp12_pow(normalized, ORDER // R))

    def test_complete_finite_chart_rotation(self):
        stages = ate_torus._finite_stages()
        self.assertEqual(len(stages), 178)
        self.assertTrue(all(x % R for x in stages))
        self.assertEqual(gcd(ate_torus.LAMBDA, ate_torus.QUOTIENT_ORDER), R)
        # All lines are neutral, so the naive initial lift 1 is at infinity.
        # Rotation to another r-th root must still make this valid proof lift.
        g1 = {"x": "0", "y": "0"}
        g2 = {"x": ["0", "0"], "y": ["0", "0"]}
        stmt = dict(self.data["statement"], L=g1, alpha=g1)
        proof = {"a": g1, "b": g2, "c": g1}
        ate_torus.verify_finite(None, stmt, proof)

    def test_moving_coordinate_lines_with_finite_and_infinite_points(self):
        stmt = self.data["statement"]
        finite = self.data["witnesses"][0]
        _, pairs, _ = ate.prepare(None, stmt, finite)
        self.assertEqual(
            moving_lines.miller(None, pairs), ate_fused._miller(None, pairs)
        )
        self.assertEqual(pow(3, (P - 1) // 2, P), P - 1)
        g1 = {"x": "0", "y": "0"}
        g2 = {"x": ["0", "0"], "y": ["0", "0"]}
        neutral = dict(stmt, L=g1, alpha=g1)
        gen1 = {"x": "1", "y": "2"}
        gen2 = {"x": list(map(str, curve.G2[0])), "y": list(map(str, curve.G2[1]))}
        moving_lines.verify(
            None, dict(neutral, delta=gen2), {"a": gen1, "b": gen2, "c": gen1}
        )
        for a, b in ((g1, finite["b"]), (finite["a"], g2), (g1, g2)):
            proof = {"a": a, "b": b, "c": g1}
            _, pairs, _ = ate.prepare(None, neutral, proof)
            for line in moving_lines.products(None, pairs):
                self.assertTrue(any(line[1::2]))
                self.assertFalse(any(line[::2]))
            moving_lines.verify(None, neutral, proof)
        outside = {
            "x": ["2", "1"],
            "y": [
                "7292567877523311580221095596750716176434782432868683424513645834767876293070",
                "19659275751359636165940301690575149581329631496732780143538578556285923319774",
            ],
        }
        with self.assertRaises(ValueError):
            moving_lines.verify(None, neutral, {"a": g1, "b": outside, "c": g1})

    def test_proofs_and_altered_fixed_statement(self):
        funcs = (
            ate_fused.verify,
            ate_torus.verify,
            ate_torus.verify_finite,
            moving_lines.verify,
        )
        for verify in funcs:
            stmt = self.data["statement"]
            for proof in self.data["witnesses"]:
                verify(None, stmt, proof)
            # Changing an already-specialized public input changes L. It
            # leaves a valid point and destroys the original pairing relation.
            altered = dict(stmt, L={"x": str(curve.G1[0]), "y": str(curve.G1[1])})
            with self.assertRaises(ValueError):
                verify(None, altered, self.data["witnesses"][0])
