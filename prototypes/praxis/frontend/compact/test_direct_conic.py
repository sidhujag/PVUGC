"""Differential checks for the tangent-free quartic certificate."""

import json
import unittest

from . import ate, conic_window, direct_conic
from .test_curve import FIXTURE
from .tower import ORDER, R, fp12_mul, fp12_pow


class DirectConic(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(FIXTURE.read_text())

    def test_raw_conics_and_reduced_pairing(self):
        st = self.fixture["statement"]
        a, b = self.fixture["witnesses"]
        zero = {"x": "0", "y": "0"}
        zero2 = {"x": ["0", "0"], "y": ["0", "0"]}
        schedule = conic_window.schedule(4)
        direct_conic.certify(schedule)
        for proof in (
            a,
            b,
            dict(a, c=a["a"]),
            dict(a, a=zero),
            dict(a, b=zero2),
            dict(a, c=zero),
        ):
            _, pairs, fixed = ate.prepare(None, st, proof)
            table, reference = conic_window._ops(None, pairs, schedule)
            new_table, trace = conic_window._ops(None, pairs, schedule, True)
            trace = tuple(trace)
            self.assertEqual(table, new_table)
            self.assertEqual(tuple(reference), trace)
            raw = conic_window._raw(new_table, trace, fixed)
            ordinary = fp12_mul(None, ate._miller(None, pairs), fixed)
            self.assertEqual(fp12_pow(raw, ORDER // R), fp12_pow(ordinary, ORDER // R))

    def test_hostile_subgroup_and_altered_statement(self):
        st = self.fixture["statement"]
        first = self.fixture["witnesses"][0]
        with self.assertRaises(ValueError):
            conic_window.verify_width(
                None, dict(st, L={"x": "1", "y": "2"}), first, 4, True
            )
        zero = {"x": "0", "y": "0"}
        outside = {
            "x": ["2", "1"],
            "y": [
                "7292567877523311580221095596750716176434782432868683424513645834767876293070",
                "19659275751359636165940301690575149581329631496732780143538578556285923319774",
            ],
        }
        with self.assertRaises(ValueError):
            conic_window.verify_width(
                None,
                dict(st, alpha=zero, L=zero),
                {"a": zero, "b": outside, "c": zero},
                4,
                True,
            )
