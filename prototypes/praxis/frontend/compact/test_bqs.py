import io
import json
import random
import unittest

from .bqs import Builder, P, R, bit_value, check_row


class ForeignFieldTests(unittest.TestCase):
    def test_signed_sums_at_the_canonical_boundary(self):
        rng = random.Random(23)
        for x in (0, 1, P - 1, R, rng.randrange(P)):
            y = rng.randrange(P)
            b = Builder()
            a, c = b.witness(x), b.witness(y)
            small_sum = b.mod(linear=[(18, a), (-82, c)], constant=-6)
            expected = (18 * x - 82 * y - 6) % P
            got = b.mod(
                [(1, small_sum, small_sum), (-82, a, c)], [(P - 19, c)], -P // 3
            )
            self.assertEqual(
                b.value(got), (expected**2 - 82 * x * y + (P - 19) * y + (-P // 3)) % P
            )

    def test_native_alias_fails_a_carry_row(self):
        sink = io.BytesIO()
        b = Builder(sink)
        x = b.witness(7)
        out = b.mod([(1, x, x)])
        rows = [json.loads(line) for line in sink.getvalue().splitlines()]
        mutated = bytearray(b.assignment)
        for i in range(out.width):
            offset = out.start + i
            bit = 1 << (offset % 8)
            if ((49 + R) >> i) & 1:
                mutated[offset // 8] |= bit
            else:
                mutated[offset // 8] &= ~bit
        get = lambda atom: bit_value(mutated, atom)
        self.assertTrue(check_row(rows[0], get))
        self.assertTrue(any(not check_row(row, get) for row in rows[1:]))

    def test_same_public_shape_with_distinct_secret_values(self):
        shapes = []
        for v in [0, 1, P - 1]:
            builder = Builder()
            x = builder.witness(v)
            y = builder.mod([(1, x, x)], [(7, x)], -1)
            self.assertEqual(builder.value(y), (v * v + 7 * v - 1) % P)
            shapes.append(builder.shape())
        self.assertEqual(shapes[0], shapes[1])
        self.assertEqual(shapes[1], shapes[2])
