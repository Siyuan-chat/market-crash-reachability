# Reproducing V12 Final

Install Python 3.11 and run `python -m pip install .` in a fresh virtual
environment. Dependencies are pinned in `pyproject.toml`. Python 3.10 is also
supported; local validation records the actual interpreter used.
`requirements-lock.txt` records the complete Python 3.11 acceptance environment;
use `python -m pip install -r requirements-lock.txt` before `python -m pip install .`
when reproducing that dependency set. Platform-specific wheels may differ.

Run `python scripts/run_checks.py quick` for basic numerical regression,
earlier multiday-model regression, symbolic generalized-coordinate identities,
coordinate ODE equivalence, final-certificate consistency, and manuscript/ODE
alignment. Reports are written under `data/` and `verification/`; supplied
fixtures and the final certificate live in separate subdirectories.

Run `python scripts/run_checks.py full` to add certificate regeneration with
80,000 steps at 1/2000, integer fixed-point scale 10^32, outward rounding,
exact rational root isolation and exponential comparisons. The regenerated
JSON must be byte-identical to `data/certificates/final_interval_certificate.json`.
Assertions are never relaxed on mismatch. The independent DOP853 integration
is a diagnostic cross-check, not a second interval proof.

Run `python scripts/reproduce_figures.py` to regenerate the figure collection
and CSV/JSON data in `figures/` and `data/`. These generated files do not
overwrite the V12 Final figures used by the distributed PDFs. PDF metadata,
fonts, rendering, and floating-point values may vary with platform. Claims and
fixture values are checked by the regression suite; generated figure PDFs are
not expected to have identical bytes. The supplement includes earlier
exploratory paths and a deliberately infeasible pulse-path comparison; these
are retained because the final supplement refers to them.

Install a TeX distribution with pdflatex, amsmath, amssymb, amsthm, mathtools,
geometry, graphicx, booktabs, caption, float, hyperref, microtype, lmodern,
enumitem and the other packages named in the source. Run
`python scripts/build_papers.py`. It copies source inputs to
`release/rebuilt/`, compiles in fresh workspaces for at least two passes until
cross-references stabilize (at most five passes), and preserves original PDFs.
The included `main.bbl` avoids a BibTeX dependency for the faithful build.
For a portable alternate-engine comparison, use
`python scripts/build_papers.py --tectonic /path/to/tectonic`.
For portable pdfLaTeX use `--pdflatex /path/to/pdflatex`; `--output-root`
selects a separate output directory. Scratch evidence is retained under
`build/latex_workspaces/`, including failed runs. The local TeX Live 2026
acceptance needed three passes for the paper and two for the supplement.
Tectonic downloads its own TeX bundle; its output is not a byte-faithful
pdfLaTeX build and must be compared separately with the original PDFs.
Do not replace the distributed final PDFs without comparing the rebuilt
documents and recording the new hashes.

Run `python scripts/check_hashes.py` for the distributed-file checksum check.
The checksum manifest excludes itself, generated outputs, Git internals and
transient build files. CI artifacts retain command stdout/stderr and reports.
CI configuration is not evidence that GitHub Actions has already run.

For an inspectable full-document comparison, install the optional PDF tools
with `python -m pip install '.[pdf-validation]'`, then run:

```bash
python scripts/compare_pdfs.py --repository . --rebuilt release/rebuilt --out build/pdf_comparison
```

This records every page at 144 dpi, text extraction, page dimensions, numeric
sequences, citations, equation numbers and SHA-256 identities. It reports
differences; it does not automatically certify semantic equivalence. Inspect
the difference ledger and rendered pages. Mathematical Unicode mappings may
differ across TeX/font versions even when visible mathematics is unchanged.
The completed local comparison is documented in PDFLATEX_ACCEPTANCE.md.
