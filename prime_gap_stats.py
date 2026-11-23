#!/usr/bin/env python3
"""
prime_gap_stats.py -- Streaming adjacency statistics for consecutive prime gaps.

Reproduces Tables 3--6, the full-range convexity counts, and all 1- and 2-parameter
weighted least-squares fits for:
  "Lattice Trapezoids of Prime Gaps: Minimal Interior Counts and Empirical Statistics"

Computes, for primes p_n < LIMIT (anchor p_n >= 3, using triples (g_n, g_{n+1}, g_{n+2})):
  - gcd(g_n, g_{n+1}) distribution vs. windowed empirical-marginal null and reduced-residue limit
  - sign of K_n = (g_n * g_{n+2} - g_{n+1}^2) / 2 vs. windowed empirical-marginal null
  - block-bootstrap standard errors on six disjoint intervals (null recomputed per resample)
  - 1-parameter WLS fits (c/ln x, c*ln(ln x)/ln x) and 2-parameter fits (c/(ln x)^a, c/ln x + d/(ln x)^2)

Usage:
    pip install numpy scipy          # optionally also `primesieve` for speed
    python prime_gap_stats.py        # runs default LIMIT = 3e10, RATIO = 1.1
    python prime_gap_stats.py --limit 200000000 --ratio 1.1
    python prime_gap_stats.py --ratio 1.05 --ckpt ckpt_105.pkl
"""
import argparse
import json
import math
import os
import pickle
import time

import numpy as np

try:
    from scipy.optimize import curve_fit
    from scipy.stats import chi2
except ImportError:
    curve_fit = None
    chi2 = None

# ----------------------------- defaults -----------------------------
DEFAULT_LIMIT = 3 * 10**10   # process primes below this (must be even)
SEG = 2 * 10**7              # numbers per segment (even)
DEFAULT_RATIO = 1.1          # multiplicative window width for the null
GMAX = 1024                  # largest gap tracked in histograms
MOBIUS_TRUNC = 5000          # truncation for reduced-residue limit d_{2k}
NBLOCKS = 200                # contiguous blocks (equal width in x) per interval
NBOOT = 1000                 # bootstrap resamples
SEED = 12345
CKPT_EVERY = 10              # segments between checkpoints

ALL_INTERVALS = [
    (10**5, 3 * 10**5),
    (10**6, 3 * 10**6),
    (10**7, 3 * 10**7),
    (10**8, 2 * 10**8),
    (10**9, 3 * 10**9),
    (10**10, 2 * 10**10),
]
KNOWN_PI = {
    10**6: 78498,
    10**7: 664579,
    10**8: 5761455,
    2 * 10**8: 11078937,
    10**9: 50847534,
    10**10: 455052511,
    3 * 10**10: 1300005926,
}


# ------------------------------ prime source ------------------------------
def simple_primes(n: int) -> np.ndarray:
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for i in range(2, math.isqrt(n) + 1):
        if s[i]:
            s[i * i :: i] = False
    return np.flatnonzero(s)


def make_prime_source(limit: int):
    try:
        import primesieve

        def get_primes(lo: int, hi: int) -> np.ndarray:
            return np.asarray(primesieve.primes(lo, hi - 1), dtype=np.int64)

        return "primesieve", get_primes
    except ImportError:
        base = [int(q) for q in simple_primes(math.isqrt(limit) + 1) if q > 2]

        def get_primes(lo: int, hi: int) -> np.ndarray:
            cnt = (hi - lo) // 2
            flags = np.ones(cnt, dtype=bool)
            if lo == 0:
                flags[0] = False
            for q in base:
                if q * q >= hi:
                    break
                start = max(q * q, -(-(lo + 1) // q) * q)
                if start % 2 == 0:
                    start += q
                flags[(start - (lo + 1)) // 2 :: q] = False
            pr = lo + 1 + 2 * np.flatnonzero(flags).astype(np.int64)
            return np.concatenate(([2], pr)) if lo == 0 else pr

        return "numpy", get_primes


# ------------------------- reduced-residue limit -------------------------
def reduced_residue_limits(max_even: int = 12, trunc: int = MOBIUS_TRUNC) -> dict:
    """Compute d_{2k} = sum_{j=1}^{trunc} mu(j) / phi(2*k*j)^2."""
    n_max = max_even * trunc
    mu = np.ones(n_max + 1, dtype=np.int64)
    phi = np.arange(n_max + 1, dtype=np.int64)
    is_prime = np.ones(n_max + 1, dtype=bool)
    is_prime[:2] = False
    for p in range(2, n_max + 1):
        if is_prime[p]:
            if p * p <= n_max:
                is_prime[p * p :: p] = False
            phi[p::p] -= phi[p::p] // p
            mu[p::p] = -mu[p::p]
            if p * p <= n_max:
                mu[p * p :: p * p] = 0
    mu[0] = 0

    j = np.arange(1, trunc + 1)
    nz = mu[j] != 0
    j_nz = j[nz]
    mu_nz = mu[j_nz]
    return {
        m: float(np.sum(mu_nz / (phi[m * j_nz].astype(np.float64) ** 2)))
        for m in range(2, max_even + 1, 2)
    }


# ------------------------- accumulation of statistics -------------------------
def new_cell():
    return {
        "h": np.zeros(GMAX + 1, np.int64),  # single-gap histogram (g_n)
        "g": np.zeros(GMAX + 1, np.int64),  # gcd(g_n, g_{n+1}) counts
        "s": np.zeros(3, np.int64),         # K<0, K=0, K>0 counts
    }


def accumulate(store, keys, g1, gc, sg):
    """keys must be non-decreasing; adds each run of equal keys to its cell."""
    if len(keys) == 0:
        return
    cuts = np.flatnonzero(np.diff(keys)) + 1
    starts = np.concatenate(([0], cuts))
    ends = np.concatenate((cuts, [len(keys)]))
    for s, e in zip(starts, ends):
        k = int(keys[s])
        c = store.get(k)
        if c is None:
            c = store[k] = new_cell()
        c["h"] += np.bincount(g1[s:e], minlength=GMAX + 1)
        c["g"] += np.bincount(gc[s:e], minlength=GMAX + 1)
        c["s"] += np.bincount(sg[s:e], minlength=3)


def process(P, state, log_ratio: float):
    g = np.diff(P)
    state["max_gap"] = max(state["max_gap"], int(g.max()))
    g1, g2, g3 = g[:-2], g[1:-1], g[2:]
    p = P[:-3]  # anchor primes p_n
    keep = p >= 3
    p, g1, g2, g3 = p[keep], g1[keep], g2[keep], g3[keep]
    if len(p) == 0:
        return
    sg = (np.sign(g1 * g3 - g2 * g2) + 1).astype(np.int64)  # 0:K<0, 1:K=0, 2:K>0
    gc = np.gcd(g1, g2)
    state["clipped"] += int((g1 > GMAX).sum())
    g1c, gcc = np.minimum(g1, GMAX), np.minimum(gc, GMAX)
    w = np.where(
        p < 1000,
        0,
        1 + np.floor(np.log(np.maximum(p, 1000) / 1000.0) / log_ratio),
    ).astype(np.int64)
    accumulate(state["G"], w, g1c, gcc, sg)
    for k, (L, U) in enumerate(ALL_INTERVALS):
        sel = (p >= L) & (p < U)
        if not sel.any():
            continue
        b = ((p[sel] - L) * NBLOCKS) // (U - L)
        accumulate(state["I"][k], b * 1000 + w[sel], g1c[sel], gcc[sel], sg[sel])
        state["sumlog"][k] += float(np.log(p[sel]).sum())
        state["cnt"][k] += int(sel.sum())


# ------------------------------ null model ------------------------------
def null_dist(h):
    """Independent draws from histogram h: returns gcd distribution and P(K<0,=0,>0)."""
    sup = np.flatnonzero(h)
    p = h[sup] / h[sup].sum()
    pr = (p[:, None] * p[None, :]).ravel()
    gn = np.bincount(
        np.gcd(sup[:, None], sup[None, :]).ravel(),
        weights=pr,
        minlength=GMAX + 1,
    )
    prod = (sup[:, None] * sup[None, :]).ravel()
    sq = sup * sup
    M = int(max(prod.max(), sq.max())) + 2
    pz = np.bincount(prod, weights=pr, minlength=M)
    cdf = np.cumsum(pz)
    lt = float((p * cdf[sq - 1]).sum())
    eq = float((p * pz[sq]).sum())
    gt = float((p * (1.0 - cdf[sq])).sum())
    return gn, np.array([lt, eq, gt])


# ------------------------------ reporting ------------------------------
def report_global(state):
    G = state["G"]
    N = sum(int(c["h"].sum()) for c in G.values())
    gemp = sum(c["g"] for c in G.values()).astype(float) / N
    semp = sum(c["s"] for c in G.values()).astype(float) / N
    gnull, snull = np.zeros(GMAX + 1), np.zeros(3)
    for c in G.values():
        n = c["h"].sum()
        gn, sn = null_dist(c["h"])
        gnull += n * gn
        snull += n * sn
    gnull /= N
    snull /= N
    red_res = reduced_residue_limits(max_even=12, trunc=MOBIUS_TRUNC)

    print(f"\n=== Table 3: Full range ({N:,} anchors, p_n >= 3) ===")
    print(f"mean gcd = {(np.arange(GMAX + 1) * gemp).sum():.5f}")
    print(f"{'gcd':>6} {'count':>14} {'empirical':>10} {'win_null':>10} {'red_res':>9} {'shift(pp)':>10}")
    for d in (2, 4, 6, 8, 10, 12):
        print(
            f"{d:>6} {int(round(gemp[d] * N)):>14,} {100 * gemp[d]:>9.3f}% "
            f"{100 * gnull[d]:>9.3f}% {100 * red_res[d]:>8.2f}% "
            f"{100 * (gemp[d] - gnull[d]):>+10.3f}"
        )
    for m in (3, 4):
        e, n_ = gemp[m::m].sum(), gnull[m::m].sum()
        print(f"P({m} | gcd): empirical {e:.5f}   windowed null {n_:.5f}   limit 0.25000")

    print(f"\n{'K sign':>10} {'count':>14} {'empirical':>10} {'win_null':>10} {'shift(pp)':>10}")
    for i, name in ((2, "K>0"), (1, "K=0"), (0, "K<0")):
        print(
            f"{name:>10} {int(round(semp[i] * N)):>14,} {100 * semp[i]:>9.3f}% "
            f"{100 * snull[i]:>9.3f}% {100 * (semp[i] - snull[i]):>+10.3f}"
        )


def build_interval(store):
    keys = list(store)
    wins = sorted({k % 1000 for k in keys})
    widx = {w: i for i, w in enumerate(wins)}
    Hbw = np.zeros((NBLOCKS, len(wins), GMAX + 1), np.int64)
    Gb = np.zeros((NBLOCKS, GMAX + 1), np.int64)
    Sb = np.zeros((NBLOCKS, 3), np.int64)
    for k, c in store.items():
        b, w = divmod(k, 1000)
        Hbw[b, widx[w]] += c["h"]
        Gb[b] += c["g"]
        Sb[b] += c["s"]
    return Hbw, Gb, Sb


def shifts(m, Hbw, Gb, Sb):
    """Shifts (empirical - null) in pp: [gcd=2, K>0, K=0, K<0], and sample size."""
    Hw = np.tensordot(m, Hbw, axes=(0, 0))
    G, S = m @ Gb, m @ Sb
    N = S.sum()
    gnull, snull = np.zeros(GMAX + 1), np.zeros(3)
    for h in Hw:
        n = h.sum()
        if n > 0:
            gn, sn = null_dist(h)
            gnull += n * gn
            snull += n * sn
    gnull /= N
    snull /= N
    gemp, semp = G / N, S / N
    out = 100.0 * np.array([
        gemp[2] - gnull[2],
        semp[2] - snull[2],
        semp[1] - snull[1],
        semp[0] - snull[0],
    ])
    return out, int(N)


def fit_1param(L, y, se):
    res = {}
    for name, f in (("c/lnx", 1.0 / L), ("c*lnlnx/lnx", np.log(L) / L)):
        w = 1.0 / se**2
        c = (w * y * f).sum() / (w * f * f).sum()
        cse = (w * f * f).sum() ** -0.5
        chi = float((w * (y - c * f) ** 2).sum())
        dof = len(y) - 1
        pval = float(chi2.sf(chi, dof)) if chi2 is not None else float("nan")
        res[name] = dict(c=float(c), se=float(cse), chi2=chi, dof=dof, p=pval)
    return res


def fit_2param(L, y, se):
    if curve_fit is None:
        return {}
    models = {
        "c/(lnx)^a": (lambda x, c, a: c / x**a, lambda c0: [c0, 1.0]),
        "c/lnx + d/ln^2 x": (lambda x, c, d: c / x + d / x**2, lambda c0: [c0, 0.0]),
    }
    res = {}
    for nm, (f, p0_fn) in models.items():
        params, _ = curve_fit(f, L, y, p0=p0_fn(y[-1] * L[-1]), sigma=se, absolute_sigma=True)
        chi = float((((y - f(L, *params)) / se) ** 2).sum())
        dof = len(y) - 2
        pval = float(chi2.sf(chi, dof)) if chi2 is not None else float("nan")
        res[nm] = dict(params=[float(v) for v in params], chi2=chi, dof=dof, p=pval)
    return res


def report_intervals(state):
    rng = np.random.default_rng(SEED)
    names = ["gcd=2", "K>0", "K=0", "K<0"]
    rows = []

    print("\n=== Table 4: Disjoint intervals (shift in pp, block-bootstrap SE) ===")
    print(f"{'interval':>24} {'N':>12} " + " ".join(f"{n:>18}" for n in names))
    for k, (L, U) in enumerate(ALL_INTERVALS):
        if U > state["next_lo"] or not state["I"][k]:
            continue
        Hbw, Gb, Sb = build_interval(state["I"][k])
        pt, N = shifts(np.ones(NBLOCKS), Hbw, Gb, Sb)
        boot = np.empty((NBOOT, 4))
        for r in range(NBOOT):
            m = np.bincount(rng.integers(0, NBLOCKS, NBLOCKS), minlength=NBLOCKS).astype(float)
            boot[r], _ = shifts(m, Hbw, Gb, Sb)
        se = boot.std(axis=0, ddof=1)
        lnx = state["sumlog"][k] / state["cnt"][k]
        rows.append(dict(interval=[L, U], N=N, lnx=lnx, shift=pt.tolist(), se=se.tolist()))
        print(
            f"{f'[{L:.0e}, {U:.0e}]':>24} {N:>12,} "
            + " ".join(f"{pt[j]:>+9.3f} +/- {se[j]:<6.3f}" for j in range(4))
        )

    fits1, fits2 = {}, {}
    if len(rows) >= 3:
        Lx = np.array([r["lnx"] for r in rows])
        print("\n=== Table 5: One-parameter WLS fits (inverse-variance weights) ===")
        for j, nm in enumerate(names):
            y = np.array([r["shift"][j] for r in rows])
            s = np.array([r["se"][j] for r in rows])
            fits1[nm] = fit_1param(Lx, y, s)
            for form, v in fits1[nm].items():
                print(
                    f"{nm:>6} {form:>12}: c = {v['c']:+.3f} +/- {v['se']:.3f} pp, "
                    f"chi2 = {v['chi2']:.2f} (dof {v['dof']}), p = {v['p']:.3g}"
                )

    if len(rows) >= 4 and curve_fit is not None:
        Lx = np.array([r["lnx"] for r in rows])
        print("\n=== Table 6: Two-parameter fits ===")
        for j, nm in enumerate(names):
            y = np.array([r["shift"][j] for r in rows])
            s = np.array([r["se"][j] for r in rows])
            fits2[nm] = fit_2param(Lx, y, s)
            for form, v in fits2[nm].items():
                p_str = ", ".join(f"{val:.3f}" for val in v["params"])
                print(
                    f"{nm:>6} {form:>18}: params = ({p_str}), "
                    f"chi2 = {v['chi2']:.2f} (dof {v['dof']}), p = {v['p']:.3g}"
                )

    return rows, fits1, fits2


# --------------------------------- main ---------------------------------
def fresh_state(params):
    n = len(ALL_INTERVALS)
    return dict(
        params=params,
        next_lo=0,
        carry=np.empty(0, np.int64),
        n_primes=0,
        max_gap=0,
        clipped=0,
        G={},
        I=[{} for _ in range(n)],
        sumlog=[0.0] * n,
        cnt=[0] * n,
    )


def save(state, ckpt_path: str):
    tmp = ckpt_path + ".tmp"
    with open(tmp, "wb") as f:
        pickle.dump(state, f)
    os.replace(tmp, ckpt_path)


def main():
    parser = argparse.ArgumentParser(description="Streaming prime-gap adjacency statistics.")
    parser.add_argument("--limit", type=int, default=DEFAULT_LIMIT, help="Upper prime limit (even).")
    parser.add_argument("--ratio", type=float, default=DEFAULT_RATIO, help="Multiplicative window ratio.")
    parser.add_argument("--ckpt", type=str, default="prime_gap_stats_ckpt.pkl", help="Checkpoint file path.")
    parser.add_argument("--out", type=str, default="prime_gap_stats_results.json", help="Output JSON path.")
    args = parser.parse_args()

    limit = args.limit
    ratio = args.ratio
    assert limit % 2 == 0 and SEG % 2 == 0
    log_ratio = math.log(ratio)
    params = (limit, ratio, SEG, GMAX, NBLOCKS, tuple(ALL_INTERVALS))

    backend, get_primes = make_prime_source(limit)
    state = fresh_state(params)
    if os.path.exists(args.ckpt):
        with open(args.ckpt, "rb") as f:
            old = pickle.load(f)
        if old.get("params") == params:
            state = old
            print(f"Resuming from {state['next_lo']:,} ({args.ckpt})")
        else:
            print("Checkpoint parameters differ: starting fresh.")

    print(f"backend = {backend}, LIMIT = {limit:,}, SEG = {SEG:,}, RATIO = {ratio}")
    t0, nseg = time.time(), 0
    start = state["next_lo"]
    for lo in range(start, limit, SEG):
        hi = min(lo + SEG, limit)
        new = get_primes(lo, hi)
        state["n_primes"] += len(new)
        P = np.concatenate((state["carry"], new)) if len(state["carry"]) else new
        if len(P) >= 4:
            process(P, state, log_ratio)
        state["carry"] = P[-3:].copy()
        state["next_lo"] = hi
        nseg += 1
        if nseg % 5 == 0 or hi == limit:
            el = time.time() - t0
            done = hi - start
            eta = el * (limit - hi) / max(done, 1)
            print(
                f"  {hi:>16,} / {limit:,}   elapsed {el / 60:6.1f} min   ETA {eta / 60:6.1f} min",
                flush=True,
            )
        if nseg % CKPT_EVERY == 0:
            save(state, args.ckpt)
    save(state, args.ckpt)

    print(f"\nprimes below {limit:,}: {state['n_primes']:,}   largest gap seen: {state['max_gap']}")
    if limit in KNOWN_PI:
        ok = "OK" if state["n_primes"] == KNOWN_PI[limit] else "MISMATCH -- check the sieve!"
        print(f"pi({limit:,}) should be {KNOWN_PI[limit]:,}: {ok}")
    if state["clipped"]:
        print(f"WARNING: {state['clipped']} gaps exceeded GMAX={GMAX}; raise GMAX.")

    report_global(state)
    rows, fits1, fits2 = report_intervals(state)

    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(
            {
                "limit": limit,
                "ratio": ratio,
                "backend": backend,
                "segment_width": SEG,
                "prime_count": state["n_primes"],
                "anchor_count": sum(int(c["h"].sum()) for c in state["G"].values()),
                "max_gap": state["max_gap"],
                "histogram_gmax": GMAX,
                "bootstrap_blocks": NBLOCKS,
                "bootstrap_resamples": NBOOT,
                "bootstrap_seed": SEED,
                "intervals": rows,
                "fits": fits1,
                "fits_two_parameter": fits2,
            },
            f,
            indent=2,
        )
    print(f"Wrote results to {args.out}")


if __name__ == "__main__":
    main()
