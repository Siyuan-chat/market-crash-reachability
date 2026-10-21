# Repository structure and file policy

**Current reader entry point:** [root README](../README.md) · [V14-R1 PDF](../submission/v14-turnover-dissipation/manuscript.pdf) · [exact PDF build identity](../submission/v14-turnover-dissipation/manuscript-build.json).

This research repository intentionally preserves historical file locations. Some directories contain earlier manuscripts, archived figures or validation logs: they are **not duplicate candidates to delete**. Renaming an established path would break published deep links, LaTeX inputs, regression checks, or historical SHA-256 records.

## Directory map

```text
.
├── README.md                  Current paper entry point and evidence guide
├── REPRODUCE.md               Fast, target-specific reproduction commands
├── CONTRIBUTING.md            Issue / pull-request evidence expectations
├── CITATION.cff               Fixed software citation identity (historical)
├── LICENSE / NOTICE.md        Distinct software and research-artifact rights
├── submission/
│   ├── v14-turnover-dissipation/   CURRENT GitHub V14-R1 English manuscript
│   │   ├── main.tex              Working LaTeX manuscript
│   │   ├── manuscript.pdf        PDF published by CI
│   │   ├── manuscript-build.json Source commit and PDF SHA-256
│   │   ├── shared.tex, references.bib
│   │   └── twin_conservation_figure.tex
│   ├── v13-review-response/      Preserved V13 edition
│   ├── siam-language-revision/   Earlier English source and figure assets
│   └── siam/                     Earlier SIAM-oriented edition
├── paper/                     Original V12 paper and figure baseline
├── supplementary/             Original supplement and figure baseline
├── verification/              Certifiers, numerical checks and exact controls
│   └── loss_breadth/           B-series internally interval-checked controls
├── data/                      Original certificate, fixtures, A1/A2 dataset
├── formal/                    Lean sources and original-result scope audits
│   └── lean/                   Pinned Lean 4 + Mathlib project
├── scripts/                   Build, regression, documentation, hash scripts
├── docs/                      Reader documentation, audits and provenance
├── release/                   Frozen checksums, revision overlay, older logs
├── translations/              Original-baseline Japanese / Chinese editions
├── third_party/               Preserved SIAM style distribution
└── .github/workflows/         Existing V14, reproducibility, Lean and QA CI
```

The tree is selective; use GitHub's file browser for the full list. The `build/`, `release/rebuilt/` and Lean `.lake/` folders are generated locally and ignored. Source fixtures and historical certificates remain tracked.

## What to open first

| Reader objective | Canonical starting point |
|---|---|
| Read the current study | [GitHub V14-R1 PDF](../submission/v14-turnover-dissipation/manuscript.pdf) |
| Inspect the exact formulas/proofs | [V14-R1 `main.tex`](../submission/v14-turnover-dissipation/main.tex) |
| Verify PDF/source match | [`manuscript-build.json`](../submission/v14-turnover-dissipation/manuscript-build.json) — follow its `source_commit` and `pdf_sha256` |
| Review claims and proof boundaries | [Results-to-evidence matrix](RESULTS_AND_EVIDENCE.md) |
| Regenerate A1/A2 numeric examples | [`verification/twin_ten_asset_benchmarks.py`](../verification/twin_ten_asset_benchmarks.py) · [fixture](../data/twin_ten_asset_benchmarks.json) |
| Rerun B1/B2 interval checks | [`verification/loss_breadth/verify_all.py`](../verification/loss_breadth/verify_all.py) · [certificate README](../verification/loss_breadth/README.md) |
| Regenerate original V12 certificate | [Baseline reproduction guide](REPRODUCIBILITY.md) · [original certificate](../data/certificates/final_interval_certificate.json) |
| Read Lean's exact scope | [`formal/README.md`](../formal/README.md) · [original-result manifest](../formal/ORIGINAL_RESULT_MANIFEST.md) |
| Cite a specific paper edition | [Versions and archive identities](VERSIONS.md) |

## Version and release boundaries

**V14-R1 (GitHub working edition).** Its `submission/v14-turnover-dissipation/` source has evolved after the frozen V14 deposit: new conservation illustration, A1/A2 reconstructions, B-series comparison, and a later analytic BV variation lemma and proof additions. The numeric fixtures have distinct proof/evidence scopes. The PDF is uploaded to GitHub only after a V14 CI build and is tracked with exact source and SHA-256 metadata.

**Frozen earlier editions.** `paper/`, `supplementary/`, `submission/v13-review-response/` and the earlier SIAM revisions are retained at established paths. The frozen V14 DOI [10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787) represents the earlier 20 October 2026 source/PDF, not the evolving V14-R1 file.

**Two checksum layers.** [`release/SHA256SUMS`](../release/SHA256SUMS) is the preserved baseline; [`release/SHA256SUMS_V14_R1`](../release/SHA256SUMS_V14_R1) pins an explicitly reviewed set of newer editable files. Use `python scripts/check_revision_hashes.py` to verify both layers. It never reclassifies the original certificates, Lean proof sources, data or historical release PDFs as new work.

## Maintenance rules

- **Keep original paths and SHA-256 inputs stable.** Do not move an archival document or rename certificate inputs solely to make the root tree shorter.
- **Do not equate a PDF-only publishing commit with a new scientific source version.** Follow `manuscript-build.json`, not the tip of `main`, for the exact compiled source commit.
- **Record evidence class explicitly.** Analytic proof, Lean formalization, internally outward-rounded interval certificate and ordinary double-precision reconstruction are not interchangeable.
- **Run the relevant checks before merging.** At minimum: `python scripts/check_revision_hashes.py`, `python scripts/check_documentation.py`, `python scripts/check_v14_resource_bound.py` when source changes, and the applicable numerical/interval verifier.
- **Separate publication from repository edits.** Updating GitHub does not create a new Zenodo DOI, revise an SSRN PDF, or imply journal acceptance.

For proposed updates see [CONTRIBUTING.md](../CONTRIBUTING.md), [reproduction instructions](../REPRODUCE.md) and [current status](STATUS.md).

