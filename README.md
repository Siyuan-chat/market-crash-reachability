# When Can Markets Crash Without News?

**Siyuan Ye · V12 Final · reproducibility companion (1.0.0rc1)**

**Research areas:** endogenous (news-free) market crashes, systemic risk, nonlinear price impact, resilient market microstructure, and mathematical reachability.


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

- **Zenodo preprint and supplement:** [Published record](https://zenodo.org/records/23427880) · [DOI: 10.5281/zenodo.23427880](https://doi.org/10.5281/zenodo.23427880)
- **Archived code and reproducibility package:** [Zenodo software record](https://zenodo.org/records/23428183) · [DOI: 10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183), version `1.0.0rc1+git.d6e2606`, fixed at [commit d6e2606](https://github.com/Siyuan-chat/market-crash-reachability/tree/d6e2606590f955a6287c6945488a080e5acab004). Includes the source ZIP, provenance and SHA-256 checksum; later README DOI updates are outside this immutable snapshot.
- **SSRN preprint:** [Abstract ID 7622079](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079) — submitted; platform screening pending as of 2026-10-17.
- **SIFIN submission edition:** [Manuscript PDF](submission/siam/manuscript.pdf) · [LaTeX](submission/siam/main.tex)
- **SIFIN supplementary material:** [Supplement PDF](submission/siam/supplementary.pdf) · [LaTeX](submission/siam/supplementary.tex)
- [SIFIN build instructions and author items pending](submission/siam/README.md)
- [Mathematical results and code](docs/MATHEMATICAL_RESULTS.md)
- [Verification scope](docs/VERIFICATION_SCOPE.md)
- [Research overview and FAQ](docs/RESEARCH_OVERVIEW.md)

## Main findings at a glance

- **When are systemic drawdowns excluded?** Under the paper's paired-dollar, resilient model, response elasticity at least 2 excludes positive systemic drawdowns; elasticity at least 1 excludes a simultaneous decline of all assets.
- **When can large losses be reached?** The A/B/C regimes differ across price-impact response functions. Partial-coverage severity is conditional on the impact law, execution horizon and permission for pulses.
- **What do trading constraints change?** Dollar turnover, share inventory, bounded execution rates and daily price limits restrict feasible paths.
- **What is rigorously constructed?** One specified ten-asset, two-session path with nine repeated lower-limit closes and a computer-certified systemic log-loss measure above 0.020.

These results are theoretical and **do not predict real market crashes**. For exact hypotheses, the crisis definition and proof boundaries, read the [research overview and FAQ](docs/RESEARCH_OVERVIEW.md) and [theorem-to-code map](docs/MATHEMATICAL_RESULTS.md).

## Research editions and Lean foundations

- **V12 Final 原始研究版 (original research edition):** [Manuscript PDF](paper/manuscript.pdf) · [LaTeX](paper/main.tex) · [Supplement PDF](supplementary/supplementary.pdf) · [Supplement LaTeX](supplementary/supplementary.tex). This remains the canonical mathematical baseline; the main links above open the SIFIN submission edition.
- **简体中文:** [complete manuscript and supplement sources, build and review status](translations/zh-CN/README.md).
- **日本語:** [complete manuscript and supplement sources, build and review status](translations/ja/README.md).
- [Trilingual glossary](translations/GLOSSARY.md) and [translation consistency and build instructions](translations/README.md).
- [Lean formalization](formal/README.md): 76 kernel-checked declarations, including regular physical price-space execution paths and their no-crash barriers with Lean 4.19.0 and pinned Mathlib. **No complete numbered paper theorem is Lean-verified.** See the [theorem map](formal/THEOREM_MAP.md) and [whole-paper verification tracker](https://github.com/Siyuan-chat/market-crash-reachability/issues/5).

The complete translation editions are publicly distributed with the author’s
permission; their copyright statements remain unchanged. English remains the authoritative mathematical
source. The Lean project proves coordinate, conservation and selected
response-family foundations; it does not formalize the complete paper or the
interval certificate. Phase 2 CI runs on pull requests; consult the PR checks for current results.
Generated translation PDFs are review/build artifacts rather than duplicated
committed binaries. Paper and translation copyrights are separate from software MIT.

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
The paper is available on [Zenodo](https://doi.org/10.5281/zenodo.23427880)
and submitted to [SSRN](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079).
These are preprint records; no journal acceptance is asserted. The
[CITATION.cff](CITATION.cff) metadata describes the reproducibility software.
For the archived software snapshot, cite [DOI: 10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183)
and commit `d6e2606590f955a6287c6945488a080e5acab004`; the paper DOI above identifies
the manuscript and supplement, not the software archive. The archive preserves
the mixed license scope in [NOTICE.md](NOTICE.md).

The code is licensed under [MIT](LICENSE). The paper, figures and research
outputs have separate rights; no CC BY license has been applied. See
[NOTICE.md](NOTICE.md) for the license scope and the
[release checklist](docs/RELEASE_CHECKLIST.md).

The model uses idealized execution and hypothetical normalized assets.
Feasibility under its assumptions is neither a claim about general financial
markets nor a trading or forecasting result. Earlier exploratory displays in
the supplement are numerical illustrations, not additional interval proofs.
