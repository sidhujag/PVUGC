"""Regression checks for affine, subgroup and identity handling."""

import json
import unittest
from pathlib import Path

from . import ate, curve
from .tower import P, R, fp12_pow

FIXTURE = Path(__file__).resolve().parent.parent / "testdata/sp1-v6.1.0-pairing.json"


class PairingCoordinates(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(FIXTURE.read_text())

    def test_non_degenerate_pairing_on_generators(self):
        # On these two cyclic prime-order groups, nondegeneracy makes the
        # product predicate invariant under changing pairing conventions.
        generator = curve.constant_miller(curve.G1, curve.G2)
        self.assertNotEqual(fp12_pow(generator, (P**12 - 1) // R), curve.ONE12)

    def test_both_native_proofs_and_altered_pair(self):
        statement = self.fixture["statement"]
        for proof in self.fixture["witnesses"]:
            curve.verify(None, statement, proof)
        changed = dict(self.fixture["witnesses"][0])
        changed["c"] = changed["a"]
        with self.assertRaisesRegex(ValueError, "pairing-product"):
            curve.verify(None, statement, changed)

    def test_mixed_infinity_terms_are_neutral(self):
        statement = dict(self.fixture["statement"])
        zero_g1 = {"x": "0", "y": "0"}
        zero_g2 = {"x": ["0", "0"], "y": ["0", "0"]}
        statement["L"] = statement["alpha"] = zero_g1
        proof = self.fixture["witnesses"][0]
        for a, b in ((zero_g1, proof["b"]), (proof["a"], zero_g2), (zero_g1, zero_g2)):
            for verify in (curve.verify, ate.verify):
                verify(None, statement, {"a": a, "b": b, "c": zero_g1})

    def test_on_twist_outside_prime_subgroup(self):
        x = (2, 1)
        y = (
            7292567877523311580221095596750716176434782432868683424513645834767876293070,
            19659275751359636165940301690575149581329631496732780143538578556285923319774,
        )
        x3 = curve.mul2(None, x, curve.mul2(None, x, x))
        b2, _, _ = curve.twist_constants()
        self.assertEqual(
            curve.mul2(None, y, y), tuple((a + b) % P for a, b in zip(x3, b2))
        )
        curve.correct_g2(None, curve.G2)
        with self.assertRaises(ValueError):
            curve.correct_g2(None, (x, y))
        # A neutral pairing equation must still reject this non-subgroup G2.
        identity = {"x": "0", "y": "0"}
        neutral = dict(self.fixture["statement"], L=identity, alpha=identity)
        proof = {
            "a": identity,
            "c": identity,
            "b": {"x": list(map(str, x)), "y": list(map(str, y))},
        }
        with self.assertRaises(ValueError):
            ate.verify(None, neutral, proof)
