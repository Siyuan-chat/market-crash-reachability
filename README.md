# When Can Markets Crash Without News?

**Siyuan Ye · Mathematical finance and systemic risk · Latest GitHub manuscript: V14 (working narrative revision V14-R1)**

Can trading generate systemic losses while fundamental values stay fixed? This research studies which losses are mathematically reachable in a resilient multi-asset market with nonlinear price impact, paired-dollar trading and terminal settlement. It studies structural feasibility under explicit assumptions, rather than forecasting actual crashes.

**Working V14-R1:** [Revised LaTeX source](submission/v14-turnover-dissipation/main.tex) · [Twin-benchmark evidence and reproducibility](docs/TWIN_TEN_ASSET_REVISION_V1.md). **Prior V14 PDF:** [Compiled manuscript](submission/v14-turnover-dissipation/manuscript.pdf) · [Build provenance](submission/v14-turnover-dissipation/manuscript-build.json). The PDF reflects its *recorded build commit*; it must be rebuilt before it can be used to review new source revisions.

The **frozen V14 edition** was deposited on [Zenodo, DOI 10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787) (46 pages, 20 October 2026); the checksum matched the previously recorded V14 GitHub PDF at that snapshot. The new **working V14-R1 narrative revision and its A1/A2 numerical code are not in that deposit**, and no new archive DOI has been assigned. V13 remains a preserved [Zenodo archival edition](https://doi.org/10.5281/zenodo.23444647). The [live SSRN record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079) reported 46 pages and a 19 October revision when last checked; the SSRN PDF has not been matched to this new source. No journal acceptance is asserted. [Version and archive reference](docs/VERSIONS.md).

## Model and research findings

Positive prices start at a fixed fundamental benchmark F. Purchases and sales are dollar matched, each asset's signed executed-dollar ledger closes at the terminal time, and resilience pulls prices toward F. Response-adapted coordinates give the normal form

```math
dy=B\,dz-\rho R(y)\,dt.
```

For terminal log losses L_i=log(F/S_i), the systemic-loss statistic is C_alpha=min(mean(L), kth-largest(L)), with k=ceil(alpha N). A crisis at threshold delta requires both average loss and losses across at least k assets to reach delta. This is loss from a common benchmark, rather than rolling peak-to-trough drawdown.

- Response elasticity at least 1 excludes a decline in every asset; elasticity at least 2 excludes positive systemic losses under the barrier theorems' hypotheses.
- The original A/B/C regimes distinguish exclusion, inventory-bounded severity and arbitrarily severe partial-coverage reachability. Execution resources, rates and price bands restrict these possibilities.
- V14 extends severe partial-coverage reachability to each fixed power-law exponent 0<=p<1 with uniform finite resource bounds, and adds a turnover–dissipation bound and two robustness propositions. Bounds are not uniform as p approaches 1; the severe-loss theorem does not establish bounded gross-rate feasibility.
- A specified original ten-asset two-session path is interval certified. V14 adds loss–breadth constructions under uniform rolling bands, with fixed and relaxed turnover budgets distinguished. Unfilled feasibility cells are open, not impossibility results.
- The working narrative revision links the generalized-coordinate conservation mechanism to twin ten-asset benchmarks: an **idealized 50% all-asset loss** (ordinary numerical reconstruction, not a new interval certificate); a **nine-asset severity series**; and separately **interval-certified constrained** seven-target (>20.2%, turnover <5) and full-coverage (>2%, turnover <7) witnesses. These use different controls and budgets.

## Proofs and computational evidence

The manuscripts contain analytical proofs. The Lean source and historical acceptance manifest cover **16 original numbered results**, subject to their precise hypotheses and the recorded Proposition 7.5 boundary amendment. **The five V14 additions are not Lean-formalized.** The original interval certificate and newer internally checked loss–breadth certificates have different protocols and audit scope. Ordinary numerical regression is separate from rigorous interval verification; no independent external audit of the V14 additions is claimed.

Use the [result-to-evidence matrix](docs/RESULTS_AND_EVIDENCE.md) for stable labels, proof sources, commands and limitations, and the [Lean guide](formal/README.md) for pinned build instructions.

## Reproduce

Python 3.11 is the primary environment; dependencies are pinned in [pyproject.toml](pyproject.toml).

```sh
python -m venv .venv
# Activate .venv for your shell, then:
python -m pip install .
python scripts/run_checks.py quick
python scripts/check_v14_resource_bound.py
python verification/loss_breadth/verify_all.py
python verification/twin_ten_asset_benchmarks.py --check
```

The original full 80,000-step certificate, V14 TeX build and Lean build have separate prerequisites and commands. Follow [REPRODUCE.md](REPRODUCE.md) and the [complete reproduction guide](docs/REPRODUCIBILITY.md). The original full suite does not reproduce every V14 extension.

## Scope, citation and rights

The assets are hypothetical and normalized. The model does not estimate crash probabilities, explain a particular historical event or supply a trading strategy. Results depend on their response laws, settlement conventions, admissible controls and execution constraints.

Cite the **frozen** Siyuan Ye, *When Can Markets Crash Without News?*, V14 (2026), [10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787), with its recorded Git commit. **Do not attribute the working V14-R1 narrative or its new numerical fixture to this archival DOI**; cite a specific Git revision for work in progress. For the deposited V13 edition use [10.5281/zenodo.23444647](https://doi.org/10.5281/zenodo.23444647). The separate immutable software archive is [10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183), version `1.0.0rc1+git.d6e2606`, commit `d6e2606590f955a6287c6945488a080e5acab004`. [CITATION.cff](CITATION.cff) retains those fixed citation identities.

Software is [MIT licensed](LICENSE); manuscripts, figures, translations and research artifacts retain the separate terms in [NOTICE.md](NOTICE.md). Academic AI-use declarations remain in the manuscripts.

## Further reading

- [Working V14-R1 revision, twin benchmarks and evidence scopes](docs/TWIN_TEN_ASSET_REVISION_V1.md)
- [Research overview and FAQ](docs/RESEARCH_OVERVIEW.md)
- [Results and evidence](docs/RESULTS_AND_EVIDENCE.md)
- [Versions and archival records](docs/VERSIONS.md)
- [Reproducibility](docs/REPRODUCIBILITY.md)
- Original-baseline translations: [简体中文](translations/zh-CN/README.md) · [日本語](translations/ja/README.md) · [Translation guide](translations/README.md)
