# Reproduce *When Can Markets Crash Without News?*

These commands are for the **current GitHub V14-R1 working manuscript**. Run them from the repository root. The [full technical guide](docs/REPRODUCIBILITY.md) covers the original V12 baseline, exact-rational certificates, figure regeneration, pinned Lean environment and source/PDF comparisons. [Version boundaries](docs/VERSIONS.md) · [Evidence types](docs/RESULTS_AND_EVIDENCE.md).

## 1. Python environment and basic regression

Use **Python 3.11** for the CI acceptance environment and create a virtual environment:

```bash
python -m venv .venv
# Activate .venv for your shell
python -m pip install .
python scripts/check_revision_hashes.py
python scripts/run_checks.py quick
```

`check_revision_hashes.py` verifies the frozen original SHA-256 manifest plus the explicitly versioned **working-file overlay**. The original baseline manifest must never be rewritten to disguise a revision.

## 2. Verify the working V14-R1 manuscript and benchmarks

```bash
python scripts/check_v14_resource_bound.py
python verification/twin_ten_asset_benchmarks.py --check
python verification/loss_breadth/verify_all.py
python scripts/check_documentation.py
```

| Command | What it establishes |
|---|---|
| `check_v14_resource_bound.py` | Editorial and source consistency, selected algebraic/numerical sanity checks and preservation of historical mathematical statements; **not** a formal theorem prover |
| `twin_ten_asset_benchmarks.py --check` | A1/A2 analytic-primitive numerical reconstruction and individual terminal-dollar ledger residual checks; **double precision**, not interval certification |
| `loss_breadth/verify_all.py` | Prescribed B-series rational controls and **internally outward-rounded** interval checks; run with Python assertions enabled |
| `check_documentation.py` | Local links, reproduction command paths and version/documentation consistency |

An optional independent SciPy/NumPy consistency check is `python verification/loss_breadth/verify_all.py --audit`. It is a floating-point cross-check, not a second rigorous interval proof.

## 3. Rebuild the English PDF

Install pdfLaTeX, BibTeX, the packages requested by the source, and the preserved SIAM class distribution. Then run:

```bash
python scripts/build_v14_resource_bound.py
```

Generated output: `build/v14-turnover-dissipation/main.pdf` with build logs and summary. The published repository [`manuscript.pdf`](submission/v14-turnover-dissipation/manuscript.pdf) is maintained by a validated GitHub Actions workflow and includes a sibling [`manuscript-build.json`](submission/v14-turnover-dissipation/manuscript-build.json) linking PDF SHA-256 to the exact source commit. A local compile does **not** automatically rewrite the published GitHub file.

## 4. Original full certificate and Lean formalization

The original large interval certificate (80,000 steps, outward rounding) is separate from the newer B-series control package:

```bash
python scripts/run_checks.py full
```

For the original **16 result families** formalized in Lean 4 (not the V14 additions or the working BV lemma), install the pinned toolchain and use:

```bash
cd formal/lean
lake exe cache get
lake build
cd ../..
python formal/check_proof_integrity.py
```

[Original-result scope](formal/README.md) · [Full reproduction instructions](docs/REPRODUCIBILITY.md) · [Current repository layout](docs/REPOSITORY_STRUCTURE.md). A completed command verifies only its declared evidence scope, not independent external review or journal acceptance.

