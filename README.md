# Lattice Trapezoids of Prime Gaps

[![Zenodo DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24451767.svg)](https://doi.org/10.5281/zenodo.24451767)

**Companion source archive for:** Rafael A. Gonzalez Castillo, *Lattice Trapezoids of Prime Gaps: Minimal Interior Counts and Empirical Statistics* (November 2026 manuscript).

This repository contains a Lean 4 / Mathlib formalization of finite algebraic and lattice-point statements, together with Python programs for reproducing the manuscript's numerical experiments. It is an archive of the code, not a claim to have formally proved the paper's asymptotic estimates or its empirical observations.

## Contents

| File | Purpose |
| --- | --- |
| `PrimeGaps.lean` | Prime gaps, trapezoid area identity, positivity, and finite area bounds |
| `PrimeGaps/Verification.lean` | Concrete examples, boundary cases, and general-sequence checks |
| `PrimeGapsTheorem3.lean` | Finite area / squared-gap bounds and transfer principle |
| `PrimeTrapezoidPick.lean` | Minimal interior-point counts, telescoping boundary count, and direct interior-point enumeration |
| `PrimeGaps/TrapezoidAxiomChecks.lean` | Selected `#print axioms` checks and concrete lattice examples |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Pinned Lean / Mathlib build configuration |
| `reproduce_tables.py` | Numerical Tables 1 and 2, prime limit 200,000,000 |
| `prime_gap_stats.py` | Numerical Tables 3–6, convexity frequencies, bootstrap uncertainty, 1- and 2-parameter weighted fits; default prime limit 30,000,000,000 |

The paper's LaTeX source is being revised separately and is not included in this code archive.

## Lean 4 verification

Install [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get
lake build PrimeGaps
lake build PrimeGaps.Verification
lake build PrimeGapsTheorem3
lake build PrimeTrapezoidPick
lake build PrimeGaps.TrapezoidAxiomChecks
```

**For a reproducible build, do not run `lake update`**, since that may alter pinned dependencies; use the committed `lake-manifest.json` as provided. In particular, `lean-toolchain` selects Lean `v4.36.0`, and Mathlib is pinned to the matching revision. The axiom-audit file prints the axiom dependencies of selected proofs. The formalization covers finite statements. The paper's asymptotic interior-density conclusion and numerical results are not Lean theorems.

## Python reproduction

Use Python 3.10+ and install:

```sh
python -m pip install -r requirements.txt
```

**Tables 1 and 2** (all primes through 200,000,000):

```sh
python reproduce_tables.py
```

**Tables 3–6** (up to primes below 30,000,000,000):

```sh
python prime_gap_stats.py --limit 30000000000 --ratio 1.1
```

The large run uses a segmented NumPy sieve by default and may require substantial computing time. Installing optional Python `primesieve` bindings can accelerate prime generation. For an inexpensive smoke test, use a smaller prime limit and separate output/checkpoint paths:

```sh
python prime_gap_stats.py --limit 100000 --ratio 1.1 --ckpt smoke_ckpt.pkl --out smoke_results.json
```

For the manuscript's sensitivity checks, use `--ratio 1.05` or `--ratio 1.2`, each with a distinct `--ckpt` and `--out` path. The defaults are 200 bootstrap blocks, 1,000 resamples, and seed 12345. A run saves a pickle checkpoint so it can resume; **only load checkpoints you created yourself**, since Python pickle files can execute code when loaded. Checkpoints (`*.pkl`) and the default generated results file are intentionally excluded from version control. The JSON output includes its prime limit, window ratio, bootstrap settings, interval shifts, and both fit families when sufficiently many intervals are available.

The Python scripts are checked with fast deterministic tests in `tests/` and GitHub Actions. The program for Tables 1–2 has also been checked against the manuscript values. The full 30-billion-limit numerical run and the Lean build should be rerun in an appropriate environment before describing the complete computation as independently reproduced.

## Automated verification

GitHub Actions runs Python unit tests and a small end-to-end statistics check, and attempts to build every included Lean module against the pinned Mathlib version. A passing small test is **not** a substitute for executing the full numerical experiments. See the [verification workflow](.github/workflows/verify.yml) for the exact commands.

## Citation and license

The software release **v1.0.0** is permanently archived at [Zenodo DOI: 10.5281/zenodo.24451767](https://doi.org/10.5281/zenodo.24451767). Please cite that DOI when referencing the archived release. Later commits on `main` improve documentation and checks but **do not modify** the already-archived `v1.0.0` snapshot.

See [`CITATION.cff`](CITATION.cff) for citation metadata. Software is distributed under the [MIT License](LICENSE), copyright 2026 Rafael A. Gonzalez Castillo. When the manuscript has an arXiv identifier, update the manuscript citation separately.
