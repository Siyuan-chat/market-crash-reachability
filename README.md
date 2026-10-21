# When Can Markets Crash Without News?

**Siyuan Ye** · Mathematical finance · Deterministic systemic-drawdown reachability

[![V14 manuscript CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/v14.yml/badge.svg)](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/v14.yml)
[![Reproducibility](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/tests.yml/badge.svg)](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/tests.yml)

**Latest GitHub manuscript: V14-R1 (working edition).**

**[Read the manuscript (PDF)](submission/v14-turnover-dissipation/manuscript.pdf)** · [LaTeX source](submission/v14-turnover-dissipation/main.tex) · [Build provenance](submission/v14-turnover-dissipation/manuscript-build.json) · [Reproduce the results](REPRODUCE.md) · [Results and evidence](docs/RESULTS_AND_EVIDENCE.md)

The PDF above is the current GitHub working manuscript. Its `manuscript-build.json` records the **exact source commit, PDF SHA-256 and successful build run**; a later PDF-only publication commit on `main` does not change that source identity. This working edition **is not** the fixed [V14 Zenodo deposit](https://doi.org/10.5281/zenodo.23478787), which predates the twin ten-asset examples and subsequent proof/editorial revisions. [Version and citation details](docs/VERSIONS.md).

## Research question

Equal-dollar purchases and sales need not leave prices unchanged, even when every asset's cumulative executed-dollar ledger returns to zero. We study which **terminal systemic drawdowns** can be reached in a multi-asset market with fixed fundamental benchmarks, state-dependent price impact, and price-level resilience.

For positive response `g(S)`, the trade-adapted coordinate and terminal crisis statistic are

$$
\Phi(S)=\int_F^S\frac{u}{g(u)}\,du,\qquad
\mathcal C_\alpha(T)=\min\left\{\frac{1}{N}\sum_{i=1}^N\log\frac{F}{S_i(T)},\ Q_\alpha(T)\right\},
$$

where `Q_\alpha` is the `k`-th largest log loss and `k=\lceil\alpha N\rceil`. Paired-dollar trades preserve `\sum_i\Phi(S_i)`, while resilience can move prices between its level sets. The research concerns **deterministic reachability**, not an estimated probability of a crash, an equilibrium strategy, or a historical-event attribution.

## Main results

- **Structural barriers:** under the stated common-impact and price-level-recovery assumptions, elasticity `e(S)\ge1` prevents all assets falling together; `e(S)\ge2` excludes positive losses under the systemic crisis criterion.
- **Partial versus full coverage:** for each fixed power exponent `0\le p<1`, sufficiently severe **partial-coverage** log losses admit a constructive path with bounded turnover and initial share inventory; **full coverage** has a sharp, unattained horizon-dependent ceiling under constant impact.
- **Execution resources:** necessary turnover/inventory inequalities, a constant-impact turnover–dissipation bound, and small-rate bounds distinguish mathematical reachability from bounded-rate or rolling-band feasibility.
- **Constrained paths:** prescribed ten-asset schedules meet positive-price, paired-dollar, terminal assetwise closure, and finite execution constraints, with specified internally interval-checked certificates.

### Four ten-asset benchmarks

| Benchmark | Achieved terminal outcome | Execution and evidence |
|---|---|---|
| **A1 · all ten** | Every price finishes at **50%** of its fundamental benchmark | Constant impact, idealized flow-completed pulses, reconstructed paired turnover `M ≈ 34.37`; analytical construction + double-precision regression |
| **A2 · nine targets** | Severity series `L=3,5,10,20` illustrates unbounded partial-coverage log losses | Constructive uniform-resource theorem + double-precision reconstruction |
| **B1 · seven targets** | Seven ordinary price falls **>20.2%**; geometric-index fall **>6%** | Rolling ±25% bands, gross-rate cap <0.285, per-asset sales <2, **`M<5`**; internally interval-checked |
| **B2 · all ten** | Every ordinary price fall **>2%** | Same band/rate/inventory class but a **different control** and **`M<7`** budget; internally interval-checked |

A1/A2 numerical reconstructions and B1/B2 interval certificates provide **different evidence types**. See the [twin-benchmark explanation](docs/TWIN_TEN_ASSET_REVISION_V1.md), [verification archive](verification/loss_breadth/README.md) and [full evidence matrix](docs/RESULTS_AND_EVIDENCE.md).

## Reproduce

Python **3.11** is the acceptance environment; the primary dependencies are pinned in [`pyproject.toml`](pyproject.toml). From the repository root:

```bash
python -m venv .venv
# Activate .venv for your shell, then:
python -m pip install .
python scripts/check_revision_hashes.py
python scripts/check_v14_resource_bound.py
python verification/twin_ten_asset_benchmarks.py --check
python verification/loss_breadth/verify_all.py
python scripts/run_checks.py quick
```

The checks serve different purposes: manuscript consistency; analytical-primitives numerical regression; internally outward-rounded rational controls; and baseline numerical checks. To **build the V14-R1 PDF**, install the pdfLaTeX/BibTeX dependencies and run `python scripts/build_v14_resource_bound.py`. Outputs go under the ignored `build/` directory. For the original 80,000-step certificate, Lean build and exact command scopes, use [REPRODUCE.md](REPRODUCE.md) and [the technical guide](docs/REPRODUCIBILITY.md).

## Repository guide

| Location | Role |
|---|---|
| [`submission/v14-turnover-dissipation/`](submission/v14-turnover-dissipation/README.md) | **Current working English manuscript:** source, PDF, build metadata, bibliography and TikZ figure |
| [`submission/`](submission/README.md), [`paper/`](paper/main.tex), [`supplementary/`](supplementary/supplementary.tex) | Preserved English editions, original research baseline and supplement |
| [`verification/`](verification/loss_breadth/README.md) and [`data/`](data/twin_ten_asset_benchmarks.json) | Numerical checks, exact rational controls, interval certificates and fixtures |
| [`formal/`](formal/README.md) | Lean 4 formalization of the **original sixteen result families**, with recorded scope qualifications |
| [`scripts/`](scripts/run_checks.py) and [`.github/workflows/`](.github/workflows/v14.yml) | Reproducibility, manuscript build, integrity checks and CI |
| [`docs/`](docs/REPOSITORY_STRUCTURE.md), [`release/`](release/SHA256SUMS) | Reader guides, provenance, preserved SHA-256 manifests and historical validation |
| [`translations/`](translations/README.md), [`third_party/`](third_party/siam/README.md) | Baseline translations and third-party SIAM templates |

**[Full repository structure and file policy →](docs/REPOSITORY_STRUCTURE.md)**

The original frozen release and its input certificates are **not reorganized or overwritten**. The current GitHub working revision has a separate allowed-file checksum overlay, [`release/SHA256SUMS_V14_R1`](release/SHA256SUMS_V14_R1).

## Evidence, citation and license

The manuscript contains analytic proofs; a later one-sided bounded-variation (BV) lemma completes a step in the current working proof exposition. Historical Lean acceptance covers the **original sixteen result families**; the five added V14 results and the later analytical BV lemma are **not Lean-formalized**. The constrained witness verifiers are internal reproducibility evidence, not external peer review.

- **Current working V14-R1:** cite the specific Git source revision recorded in [`manuscript-build.json`](submission/v14-turnover-dissipation/manuscript-build.json); there is **no separately assigned archival DOI** for this revision.
- **Frozen manuscript V14:** [Zenodo 10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787), deposited 20 October 2026; **does not contain V14-R1**.
- **Earlier V13:** [Zenodo 10.5281/zenodo.23444647](https://doi.org/10.5281/zenodo.23444647). **Fixed original software:** [10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183). The software-specific [CITATION.cff](CITATION.cff) intentionally retains those frozen identities.
- **SSRN:** [record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079), whose PDF has **not** been established as identical to the current GitHub revision.

Source-code licensing is [MIT](LICENSE); the manuscript, figures, research data and other artifacts have **separate rights** under [NOTICE.md](NOTICE.md). [Contribution and issue guidance](CONTRIBUTING.md).

