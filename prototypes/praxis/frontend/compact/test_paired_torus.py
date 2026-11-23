"""Checks for projective finite Miller lines, including the neutral-line tag."""

import json
import unittest

from . import ate, curve, paired_torus, torus
from .test_curve import FIXTURE
from .tower import ORDER, P, R, fp12_pow


class PairedTorus(unittest.TestCase):
    def test_neutral_pair_is_represented_by_a_residue(self):
        v = (2, 3, 0, 17, 7, 0)
        opposite = tuple(-x % P for x in v)
        norm = torus._combine(None, (1, 0, torus.ONE, torus.ONE), (-1, 1, v, v))
        self.assertTrue(any(norm))
        encoded = paired_torus._paired(None, opposite, v, v, norm, 1)
        self.assertEqual(encoded, torus.Class(torus.ZERO, 0))
        self.assertEqual(fp12_pow(paired_torus._flat(encoded), ORDER // R), ate.ONE)

    def test_native_equivalence_and_fixed_statement_change(self):
        data = json.loads(FIXTURE.read_text())
        s = data["statement"]
        for mode in (
            paired_torus.verify,
            paired_torus.verify_dense,
            paired_torus.verify_moving_dense,
        ):
            for w in data["witnesses"]:
                mode(None, s, w)
            changed = dict(s, L={"x": str(curve.G1[0]), "y": str(curve.G1[1])})
            with self.assertRaises(ValueError):
                mode(None, changed, data["witnesses"][0])
            z1 = {"x": "0", "y": "0"}
            z2 = {"x": ["0", "0"], "y": ["0", "0"]}
            for delta in (s["delta"], z2):
                mode(
                    None,
                    dict(s, L=z1, alpha=z1, delta=delta),
                    {"a": z1, "b": z2, "c": z1},
                )
