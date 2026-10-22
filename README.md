# When Can Markets Crash Without News?

**Siyuan Ye** · Mathematical finance · Deterministic systemic-drawdown reachability

[![V16 manuscript CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/v16.yml/badge.svg)](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/v16.yml)
[![V14 historical CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/v14.yml/badge.svg)](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/v14.yml)
[![Reproducibility](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/tests.yml/badge.svg)](https://github.com/Siyuan-chat/market-crash-reachability/actions/workflows/tests.yml)

**Latest English working manuscript: V16 — three constructive ten-asset results (22 October 2026).**

**[Read V16 PDF (successful CI build artifact; ZIP download)](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39739415539/artifacts/12409050841)** · [V16 LaTeX source](submission/v16-three-certified-constructions/main.tex) · [V16 numerical proof and independent audit](docs/TWO_DAY_25PCT_FIVE_TARGET_CERTIFICATE.md) · [V16 build workflow](.github/workflows/v16.yml) · [Older V14-R1 PDF](submission/v14-turnover-dissipation/manuscript.pdf)

V16 contains a new internally interval-certified two-session witness under uniform ±25% rolling price bands, with five assets closing at both lower limits. The V16 PDF is distributed as a CI artifact rather than a separately committed PDF file; its mathematical/computational results have not undergone external peer review or an external certificate-code audit. The earlier V14-R1 and [frozen V14 Zenodo deposit](https://doi.org/10.5281/zenodo.23478787) retain their original provenance and must not be cited as containing the newer V16 construction. [Version and citation details](docs/VERSIONS.md).

## Research question

Equal-dollar purchases and sales need not leave prices unchanged, even when every asset's cumulative executed-dollar ledger returns to zero. We study which **terminal systemic drawdowns** can be reached in a multi-asset market with fixed fundamental benchmarks, state-dependent price impact, and price-level resilience.

For positive response $g(S)$, the trade-adapted price coordinate is

$$
\Phi(S)=\int_F^S\frac{u}{g(u)}\,du.
$$

The terminal systemic-drawdown statistic is

$$
A(T)=\frac{1}{N}\sum_{i=1}^{N}\log\frac{F}{S_i(T)},
\qquad
\mathcal{C}_{\alpha}(T)=\min(A(T),Q_{\alpha}(T)).
$$

Here $Q_{\alpha}(T)$ is the $k$-th largest log loss, where $k=\lceil\alpha N\rceil$. Paired-dollar trades preserve $\sum_i\Phi(S_i)$, while resilience can move prices between its level sets. The research concerns **deterministic reachability**, not an estimated probability of a crash, an equilibrium strategy, or a historical-event attribution.

## Main results

- **Structural barriers:** under the stated common-impact and price-level-recovery assumptions, elasticity `e(S)\ge1` prevents all assets falling together; `e(S)\ge2` excludes positive losses under the systemic crisis criterion.
- **Partial versus full coverage:** for each fixed power exponent `0\le p<1`, sufficiently severe **partial-coverage** log losses admit a constructive path with bounded turnover and initial share inventory; **full coverage** has a sharp, unattained horizon-dependent ceiling under constant impact.
- **Execution resources:** necessary turnover/inventory inequalities, a constant-impact turnover–dissipation bound, and small-rate bounds distinguish mathematical reachability from bounded-rate or rolling-band feasibility.
- **Constrained paths:** prescribed ten-asset schedules meet positive-price, paired-dollar, terminal assetwise closure, and finite execution constraints, with specified internally interval-checked certificates.

### Three core ten-asset constructions

| Construction | Certified or analytically proved terminal outcome | Execution and evidence |
|---|---|---|
| **I · all ten decline** | All ten prices end at **50%** of the initial fundamental benchmark | Constant impact; idealized flow-completed pulses; explicit analytical path and numerical reconstruction, paired turnover approximately 34.37 |
| **II · nine severe losses** | Nine targets can incur arbitrarily severe terminal log losses while one asset compensates | Analytic uniform finite resource bound independent of target severity, with reconstruction checks |
| **III · two consecutive lower-limit closes** | Five of ten assets close at **−25%** on both sessions (cumulative individual loss **−43.75%**); equal-weight geometric price index falls **more than 16%** | Uniform ±25% rolling bands for all ten; absolutely continuous paired-dollar controls; internally outward-rounded interval certificate, sales <2 per asset, gross rate <0.285 and turnover M<14 |

The third construction **proves reachability for five assets**, not that five is optimal. A separate necessary bound establishes that eight or more assets cannot meet both consecutive lower closes under the specified parameters; attainability of six or seven remains open. Historical V14 A1/A2/B1/B2 numerical research assets are preserved but are not presented as extra main-paper examples. See the [third proof and evidence note](docs/TWO_DAY_25PCT_FIVE_TARGET_CERTIFICATE.md).

## Reproduce

For the latest V16 construction and manuscript, use `python verification/two_day_25pct_five_assets.py`, `python verification/audit_two_day_25pct.py`, `python scripts/check_v16_three_constructions.py`, and (with LaTeX/BibTeX available) `python scripts/build_v16_three_constructions.py`. The checked V16 PDF build also validates reference numbering by first citation order.

The following commands reproduce the preserved V14-R1 and broader historical verification suite:

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

The checks serve different purposes: manuscript consistency; analytical-primitives numerical regression; internally outward-rounded rational controls; and baseline numerical checks. To **build the preserved V14-R1 PDF**, install the pdfLaTeX/BibTeX dependencies and run `python scripts/build_v14_resource_bound.py`. Outputs go under the ignored `build/` directory. For the original 80,000-step certificate, Lean build and exact command scopes, use [REPRODUCE.md](REPRODUCE.md) and [the technical guide](docs/REPRODUCIBILITY.md).

## Repository guide

| Location | Role |
|---|---|
| [`submission/v14-turnover-dissipation/`](submission/v14-turnover-dissipation/README.md) | Preserved earlier English working manuscript: source, PDF, build metadata, bibliography and TikZ figure |
| [`submission/`](submission/README.md), [`paper/`](paper/main.tex), [`supplementary/`](supplementary/supplementary.tex) | Preserved English editions, original research baseline and supplement |
| [`verification/`](verification/loss_breadth/README.md) and [`data/`](data/twin_ten_asset_benchmarks.json) | Numerical checks, exact rational controls, interval certificates and fixtures |
| [`formal/`](formal/README.md) | Lean 4 formalization of the **original sixteen result families**, with recorded scope qualifications |
| [`scripts/`](scripts/run_checks.py) and [`.github/workflows/`](.github/workflows/v14.yml) | Reproducibility, manuscript build, integrity checks and CI |
| [`docs/`](docs/REPOSITORY_STRUCTURE.md), [`release/`](release/SHA256SUMS) | Reader guides, provenance, preserved SHA-256 manifests and historical validation |
| [`translations/`](translations/README.md), [`third_party/`](third_party/siam/README.md) | Baseline translations and third-party SIAM templates |

**[Full repository structure and file policy →](docs/REPOSITORY_STRUCTURE.md)**

The original frozen release and its input certificates are **not reorganized or overwritten**. The preserved V14-R1 revision has a separate allowed-file checksum overlay, [`release/SHA256SUMS_V14_R1`](release/SHA256SUMS_V14_R1).

## Evidence, citation and license

The manuscript contains analytic proofs; a later one-sided bounded-variation (BV) lemma completes a step in the current working proof exposition. Historical Lean acceptance covers the **original sixteen result families**; the five added V14 results and the later analytical BV lemma are **not Lean-formalized**. The constrained witness verifiers are internal reproducibility evidence, not external peer review.

- **Preserved V14-R1:** cite the specific Git source revision recorded in [`manuscript-build.json`](submission/v14-turnover-dissipation/manuscript-build.json); there is **no separately assigned archival DOI** for this revision.
- **Frozen manuscript V14:** [Zenodo 10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787), deposited 20 October 2026; **does not contain V14-R1**.
- **Earlier V13:** [Zenodo 10.5281/zenodo.23444647](https://doi.org/10.5281/zenodo.23444647). **Fixed original software:** [10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183). The software-specific [CITATION.cff](CITATION.cff) intentionally retains those frozen identities.
- **SSRN:** [record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079), whose PDF has **not** been established as identical to the current GitHub revision.

Source-code licensing is [MIT](LICENSE); the manuscript, figures, research data and other artifacts have **separate rights** under [NOTICE.md](NOTICE.md). [Contribution and issue guidance](CONTRIBUTING.md).

