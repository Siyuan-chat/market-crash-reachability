# When Can Markets Crash Without News?

**Siyuan Ye · V12 Final · reproducibility companion (1.0.0rc1)**

In an idealized multi-asset market with fixed fundamentals and dollar-balanced
trading, which systemic drawdowns are reachable without adverse fundamental
news? This paper studies structural feasibility and execution constraints,
rather than empirical crash prediction.

The mathematical approach uses **response-adapted generalized price coordinates**
to express nonlinear price impact in the normal form

```math
dy = B\,dz - \rho R(y)\,dt.
```

The results identify global elasticity barriers, an A/B/C reachability
classification, execution-resource lower bounds, a finite-rate quadratic law,
and a rigorously feasible two-session consecutive-limit-down construction.
The computer-assisted existence certificate concerns one specified ten-asset
path; analytical theorems rely on the proofs in the manuscript.

- [Manuscript PDF](paper/manuscript.pdf) · [LaTeX](paper/main.tex)
- [Supplement PDF](supplementary/supplementary.pdf) · [LaTeX](supplementary/supplementary.tex)
- [Mathematical results and code](docs/MATHEMATICAL_RESULTS.md)
- [Verification scope](docs/VERIFICATION_SCOPE.md)

## Quick start

Python 3.11 is the primary CI environment. From the repository root:

```bash
python -m venv .venv
# Linux/macOS: source .venv/bin/activate
# Windows PowerShell: .venv/Scripts/Activate.ps1
python -m pip install .
python scripts/run_checks.py quick
```

## Full reproduction

```bash
python scripts/run_checks.py full
python scripts/reproduce_figures.py
python scripts/build_papers.py
python scripts/check_hashes.py
```

The full suite regenerates the 80,000-step outward-rounded certificate and
requires byte identity with the supplied final certificate. It also runs exact
rational checks and an independent floating-point ODE comparison. See
[reproduction instructions](docs/REPRODUCIBILITY.md) for requirements and outputs.

## Citation and rights

Cite Siyuan Ye, *When Can Markets Crash Without News?*, V12 Final (2026),
and identify the software version and commit used. Machine-readable metadata
is in [CITATION.cff](CITATION.cff). The public repository is
[Siyuan-chat/market-crash-reachability](https://github.com/Siyuan-chat/market-crash-reachability).
No arXiv identifier, DOI, ORCID or acceptance information is asserted.

The code is licensed under [MIT](LICENSE). The paper, figures and research
outputs have separate rights; no CC BY license has been applied. See
[NOTICE.md](NOTICE.md) for the license scope and the
[release checklist](docs/RELEASE_CHECKLIST.md).

The model uses idealized execution and hypothetical normalized assets.
Feasibility under its assumptions is neither a claim about general financial
markets nor a trading or forecasting result. Earlier exploratory displays in
the supplement are numerical illustrations, not additional interval proofs.

