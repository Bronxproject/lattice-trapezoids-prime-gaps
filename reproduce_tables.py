#!/usr/bin/env python3
"""
reproduce_tables.py -- Reproduce Tables 1 and 2 for:
  "Lattice Trapezoids of Prime Gaps: Minimal Interior Counts and Empirical Statistics"

Computes exact lattice invariants (Delta A_n, B_n, gcd(g_n, g_{n+1}), I_n)
in 64-bit integer arithmetic for all primes up to 2 x 10^8.

Usage:
    pip install numpy
    python reproduce_tables.py
"""
import math
import time
import numpy as np

LIMIT = 200_000_000  # 11,078,937 primes


def odd_sieve(limit: int) -> np.ndarray:
    """Odd-only Sieve of Eratosthenes returning all primes <= limit."""
    if limit < 2:
        return np.array([], dtype=np.int64)
    size = (limit - 1) // 2
    is_prime = np.ones(size, dtype=bool)
    max_i = int(math.isqrt(limit))
    for i in range(3, max_i + 1, 2):
        if is_prime[(i - 3) // 2]:
            start = (i * i - 3) // 2
            is_prime[start::i] = False
    odds = np.nonzero(is_prime)[0].astype(np.int64) * 2 + 3
    return np.concatenate(([2], odds))


def main():
    t0 = time.perf_counter()
    primes = odd_sieve(LIMIT)
    print(f"Sieved {len(primes):,} primes up to {LIMIT:,} in {time.perf_counter() - t0:.2f}s")

    gaps = np.diff(primes)
    g1 = gaps[:-1]
    g2 = gaps[1:]

    # Exact integer arithmetic: 2*Delta A_n, B_n, and 2*I_n
    gcds = np.gcd(g1, g2)
    two_dA = g1 * (g1 + g2)
    B = 2 * g1 + g2 + gcds
    two_I = two_dA - B + 2

    # --- Table 1: First ten prime trapezoids ---
    print("\n=== Table 1: First ten prime trapezoids ===")
    print(f"{'n':>2} | {'p_n':>3} | {'(g_n, g_{n+1})':>14} | {'Delta A_n':>9} | {'B_n':>3} | {'gcd':>3} | {'I_n':>3}")
    for i in range(10):
        pair = f"({g1[i]}, {g2[i]})"
        print(f"{i+1:>2} | {primes[i]:>3} | {pair:>14} | {two_dA[i]/2:>9.1f} | {B[i]:>3} | {gcds[i]:>3} | {two_I[i]//2:>3}")

    # --- Table 2: Interior density convergence ---
    print("\n=== Table 2: Interior density checkpoints ===")
    print(f"{'x':>12} | {'N':>10} | {'sum I_n / sum dA_n':>18} | {'sum (B_n/2) / sum dA_n':>22}")
    checkpoints = [10**4, 10**5, 10**6, 10**7, 10**8, LIMIT]
    for x in checkpoints:
        idx = min(int(np.searchsorted(primes, x, side="right")), len(g1))
        sum_two_A = int(np.sum(two_dA[:idx], dtype=np.int64))
        sum_two_I = int(np.sum(two_I[:idx], dtype=np.int64))
        sum_B = int(np.sum(B[:idx], dtype=np.int64))
        print(f"{x:>12,} | {idx:>10,} | {sum_two_I / sum_two_A:>18.6f} | {sum_B / sum_two_A:>22.6f}")

    print(f"\nTotal runtime: {time.perf_counter() - t0:.2f}s")


if __name__ == "__main__":
    main()