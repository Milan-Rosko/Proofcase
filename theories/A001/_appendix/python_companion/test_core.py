from __future__ import annotations

import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from core import fib, pair, stable, unpair, zeckendorf_decompose
from plotting import available_pairing_names, get_pairing


class CoreTests(unittest.TestCase):
    def test_zeckendorf_decomposition_reconstructs_inputs(self) -> None:
        for n in range(0, 201):
            support = zeckendorf_decompose(n)
            self.assertEqual(sum(fib(index) for index in support), n)
            for left, right in zip(support, support[1:]):
                self.assertGreaterEqual(left - right, 2)

    def test_pair_unpair_roundtrip_on_small_grid(self) -> None:
        for x in range(0, 26):
            for y in range(0, 26):
                encoded = pair(x, y)
                self.assertEqual(unpair(encoded), (x, y))

    def test_known_pairing_value(self) -> None:
        self.assertEqual(pair(1, 1), 37)
        self.assertEqual(unpair(37), (1, 1))

    def test_plot_pairing_registry(self) -> None:
        self.assertIn("carryless", set(available_pairing_names()))
        self.assertEqual(get_pairing("carryless")(1, 1), 37)
        with self.assertRaises(ValueError):
            get_pairing("unknown")


if __name__ == "__main__":
    unittest.main()
