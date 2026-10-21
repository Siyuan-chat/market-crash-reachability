# Current GitHub manuscript — V14-R1

**[Read PDF](manuscript.pdf)** · [Edit/inspect LaTeX](main.tex) · [Verify exact build identity](manuscript-build.json) · [References](references.bib) · [Editable model diagram](twin_conservation_figure.tex)

This is the **current English GitHub working manuscript** of Siyuan Ye's *When Can Markets Crash Without News?* It incorporates the V14 analytical results, a revised conservation-geometry exposition, twin ten-asset benchmarks, and later analytical proof-completeness updates (including a finite-variation lemma).

The PDF is published by [V14 GitHub Actions](../../.github/workflows/v14.yml) after compilation and the relevant V14 checks. Its `manuscript-build.json` records the exact **source commit**, PDF SHA-256, build details and workflow run. The commit that writes the PDF may be newer than its unchanged scientific source. The [frozen V14 Zenodo deposit](https://doi.org/10.5281/zenodo.23478787) is a distinct **earlier** source/PDF (20 October 2026, 46 pages): it contains neither the later A1/A2 reconstructions nor the BV proof supplement. No new V14-R1 archival DOI has been issued. [Versions and citations](../../docs/VERSIONS.md).

## Scientific contents

The price-impact coordinate `\Phi(S)=\int_F^S u/g(u)\,du` makes paired-dollar execution additive: matched transfers preserve the aggregate price potential, while price-level resilience can move between its level sets. Under exact assetwise terminal dollar closure, the paper classifies structural drawdown exclusions and reachability, and establishes resource and rate bounds.

The current working paper includes:
- **Barriers and regimes:** elasticity thresholds, a three-market `p=2,1,0` comparison, sublinear partial-coverage severe-loss constructions with uniform finite resources, and the sharp full-coverage horizon ceiling.
- **Execution constraints:** dollar-turnover/share-inventory bounds, turnover–dissipation, bounded continuous execution and sessionwise rolling limits.
- **Two evidence classes:** idealized analytic paths with numerical regression (A1/A2), alongside prescribed, internally interval-checked finite-rate and rolling-band controls (B1/B2).
- **Analytical proof supplement:** the one-sided BV variation lemma for graph-completed pulses and explicit two-pulse Taylor terms. The historical Lean accepted family does **not** include these additional results.

### Ten-asset benchmark index

| Case | Terminal outcome | Verification and budgets |
|---|---|---|
| A1 | Ten assets each finish at `F/2` (ordinary fall **50%**) | Constant-impact analytic construction; numerical reconstruction `M≈34.37368` and gross share sales `≈16.58848`; allows idealized pulses |
| A2 | Nine target assets with severity `L=3,5,10,20` | Analytic bounded-resource severe-loss family plus ordinary numerical ledger checks |
| B1 | Seven target ordinary falls **>20.2%**, geometric-index ordinary fall **>6%** | Internally interval-certified rational control, rolling ±25% bands, **`M<5`** |
| B2 | All ten ordinary falls **>2%** | Separate internally interval-certified rational control under same band/rate class and higher **`M<7`** budget |

The B-series controls also obey gross share rate `<0.285` and gross shares sold `<2` per asset. The A-series numerical reconstruction is **not** a new outward-rounded interval certificate. See the [benchmark/evidence record](../../docs/TWIN_TEN_ASSET_REVISION_V1.md) and [interval verifier](../../verification/loss_breadth/README.md).

## Files and build inputs

| File | Function |
|---|---|
| [`main.tex`](main.tex) | Authoritative current English mathematical manuscript |
| [`shared.tex`](shared.tex), [`references.bib`](references.bib) | SIAM definitions and bibliography |
| [`twin_conservation_figure.tex`](twin_conservation_figure.tex) | Editable analytic/model-derived Figure 1 (TikZ) |
| [`manuscript.pdf`](manuscript.pdf) | CI-built current working PDF |
| [`manuscript-build.json`](manuscript-build.json) | Build provenance (`source_commit`, PDF hash, logs/run identity) |

Other PDF figures are deliberately reused from [the earlier English figure directory](../siam-language-revision/figures/), as specified in [`scripts/build_v14_resource_bound.py`](../../scripts/build_v14_resource_bound.py). Those archival assets must not be relocated without updating LaTeX and build fixtures.

## Verify and compile

From the **repository root**, with Python 3.11:

```bash
python scripts/check_revision_hashes.py
python scripts/check_v14_resource_bound.py
python verification/twin_ten_asset_benchmarks.py --check
python verification/loss_breadth/verify_all.py
python scripts/build_v14_resource_bound.py
```

The final command requires pdfLaTeX, BibTeX and the SIAM style dependencies. It produces `build/v14-turnover-dissipation/main.pdf` and a build summary; it **does not** silently overwrite a deposited Zenodo PDF or the tracked GitHub PDF. The workflow handles GitHub PDF publication after checks. See [the complete reproduction guide](../../REPRODUCE.md), [evidence matrix](../../docs/RESULTS_AND_EVIDENCE.md) and [repository map](../../docs/REPOSITORY_STRUCTURE.md).

Software is MIT licensed; this manuscript, figures and research data have the separate terms in [NOTICE.md](../../NOTICE.md).

