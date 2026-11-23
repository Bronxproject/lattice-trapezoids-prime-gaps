"""Fast deterministic checks for the prime-gap reproduction scripts.

These tests are not a substitute for the full 2e8 or 3e10 computations.
"""

import math
import unittest

import numpy as np

import prime_gap_stats as stats
from reproduce_tables import odd_sieve


class PrimeSourceTests(unittest.TestCase):
    def test_small_sieve(self):
        np.testing.assert_array_equal(
            odd_sieve(30), np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29])
        )

    def test_segmented_source_on_boundaries(self):
        _, source = stats.make_prime_source(60)
        segments = [source(lo, hi) for lo, hi in ((0, 20), (20, 40), (40, 60))]
        np.testing.assert_array_equal(
            np.concatenate(segments),
            np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59]),
        )

    def test_first_trapezoid_invariants(self):
        primes = odd_sieve(30)
        g1, g2 = np.diff(primes)[:-1], np.diff(primes)[1:]
        two_area = g1 * (g1 + g2)
        boundary = 2 * g1 + g2 + np.gcd(g1, g2)
        twice_interior = two_area - boundary + 2
        np.testing.assert_array_equal(two_area[:4], [3, 8, 12, 24])
        np.testing.assert_array_equal(boundary[:4], [5, 8, 10, 12])
        np.testing.assert_array_equal(twice_interior[:4], [0, 2, 4, 14])


class NullModelTests(unittest.TestCase):
    def test_null_distribution_matches_direct_enumeration(self):
        histogram = np.zeros(stats.GMAX + 1, dtype=np.int64)
        histogram[2] = 2
        histogram[4] = 1
        gcd_dist, sign_dist = stats.null_dist(histogram)
        expected_gcd = np.zeros_like(gcd_dist)
        expected_sign = np.zeros(3)
        for a, pa in ((2, 2 / 3), (4, 1 / 3)):
            for b, pb in ((2, 2 / 3), (4, 1 / 3)):
                expected_gcd[math.gcd(a, b)] += pa * pb
                for c, pc in ((2, 2 / 3), (4, 1 / 3)):
                    expected_sign[int(np.sign(a * c - b * b)) + 1] += pa * pb * pc
        np.testing.assert_allclose(gcd_dist, expected_gcd, atol=1e-14)
        np.testing.assert_allclose(sign_dist, expected_sign, atol=1e-14)
        self.assertAlmostEqual(sum(gcd_dist), 1)
        self.assertAlmostEqual(sum(sign_dist), 1)

    def test_known_adjacent_gap_signs(self):
        state = stats.fresh_state((100, 1.1))
        stats.process(np.array([3, 5, 7, 11, 13], dtype=np.int64), state, math.log(1.1))
        self.assertEqual(sum(int(c['s'].sum()) for c in state['G'].values()), 2)
        observed_signs = sum((c['s'] for c in state['G'].values()))
        np.testing.assert_array_equal(observed_signs, [1, 0, 1])
        self.assertEqual(sum(int(c['g'][2]) for c in state['G'].values()), 2)

    def test_one_parameter_fit_recovers_coefficient(self):
        lnx = np.array([10.0, 12.0, 15.0, 20.0])
        y = 3.0 / lnx
        sigma = np.full(4, 0.1)
        fit = stats.fit_1param(lnx, y, sigma)['c/lnx']
        self.assertAlmostEqual(fit['c'], 3.0, places=12)
        self.assertAlmostEqual(fit['chi2'], 0.0, places=12)
        self.assertEqual(fit['dof'], 3)


if __name__ == '__main__':
    unittest.main()
