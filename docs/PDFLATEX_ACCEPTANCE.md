# pdfLaTeX and original-PDF acceptance

Date: 2026-10-15 (Asia/Tokyo). Historical scope of this acceptance run: local
builds and comparison only; no publication, upload, tag or release was performed
as part of that run. This is historical evidence, not a current publication gate.
The paper and software archive are now public; current links and fixed-version
boundaries are recorded in [project status](STATUS.md).

## Result

Both unmodified V12 Final documents compile with pdfLaTeX. The complete
34-page manuscript and 10-page supplement were compared to the supplied
originals. No substantive text, number, reference-number or equation-number
change was found. The previously reported 12.6654 pt overflow is absent from
both the original manuscript and the current pdfLaTeX build. It occurred only
in the earlier Tectonic reconstruction. No manuscript correction is needed
for that finding.

The original final PDFs remain the publication candidates. The new PDFs are
comparison artifacts, not replacements, because TeX versions and PDF bytes
differ. Original source files, bibliography, embedded figure inputs, final
PDFs, interval code and certificates remain unchanged.

## Clean build

Toolchain: workspace-local official TinyTeX v2026.10, pdfTeX
3.141592653-2.6-1.40.29 (TeX Live 2026). The original PDF producer is
pdfTeX-1.40.26. The downloaded portable archive has SHA-256
`dc1d6e63b21af62130ede1dcc4113bffdc184544690a23e3f489d75340f4ff61`.
No system TeX installation or permanent PATH modification was made.

The build helper creates fresh scratch directories, copies source inputs,
disables shell escape, and compiles for at least two passes until references
stabilize, with a five-pass limit. Failed workspaces and per-pass logs are
preserved. A fixed two-pass rule was insufficient for this toolchain: the
manuscript stabilized after three passes; the supplement after two.

| Check | Manuscript | Supplement |
|---|---:|---:|
| Source-based compilation | Pass | Pass |
| Final pages / original pages | 34 / 34 | 10 / 10 |
| Final overfull boxes | 0 | 0 |
| Final unresolved references/citations | 0 | 0 |
| Remaining label-rerun warning | 0 | 0 |
| Underfull boxes | 4, table at source line 488 | 0 |

Both logs contain the expected epstopdf notice that shell escape is disabled;
all actual figures are already PDFs and no conversion is needed. The underfull
table paragraphs are spacing warnings; the rendered table was reviewed and is
legible. No paper layout or mathematics was edited to remove warnings.

## Full comparison

All 44 page sizes match. Every page was rasterized at 144 dpi and compared;
all page layouts were also reviewed in contact sheets, with full-size review
of the model-definition page, certificate page and representative figures.
There are no missing pages, clipped formula content or missing figures in
the inspected rendering. Numeric sequences, extractable numeric citations
and equation-number sequences agree on every page.

Raw/NFKC-normalized PDF extraction is not identical: 195 changed spans across
28 manuscript pages and three spans across two supplement pages. Each distinct
delta and its context was reviewed. They are legacy math-font Unicode mapping
differences (integrals, sums, products, radicals, accents and extensible
delimiters), rather than rewritten text or changed mathematics. No hyphenation
changes were found in this pdfLaTeX comparison. This is document-content
verification, not a machine-formalized mathematical proof.

The rebuilt documents are not byte-identical or pixel-identical. Maximum
per-page fraction of pixels with any changed channel at 144 dpi is 3.3225%
for the manuscript and 1.4871% for the supplement; with channel difference
greater than 16/255 it is 0.4897% and 0.4550%, respectively. These metrics
describe the observed raster differences; they are not relaxed pass thresholds.

## The reported overflow

The implicated paragraph is `paper/main.tex:138–139`, Definition 2.2 on
PDF page 5. On a 612 x 792 pt page, the configured body right edge is
537.84 pt. Its first line ends at 537.840 pt in the original and 537.8398 pt
in the pdfLaTeX rebuild. The long mean-loss expression wraps to the next
line in both. Equation (2.7) itself is also within the body. Full-page renders
were checked against character bounding boxes.

The earlier Tectonic log contains `Overfull ... 12.6654pt` at the same source
lines. It is evidence about that engine only. A historical package compile log
also has no overfull warning, but reports a different PDF byte count, so it is
not treated as an exact provenance record of the final supplied PDF. The
original-PDF conclusion rests on the original artifact itself.

## Evidence and reproduction

`release/validation/pdflatex/` contains the final compiler logs, per-pass
results, full page-comparison JSON, classified text-difference ledger,
source/PDF hash summary and the original page-5 geometry evidence. Logs have
local absolute workspace paths redacted. Large rendered images and rebuilt
PDFs are retained in the separate local comparison bundle.

```bash
python scripts/build_papers.py --pdflatex /path/to/pdflatex --output-root release/rebuilt/pdflatex
python -m pip install '.[pdf-validation]'
python scripts/compare_pdfs.py --repository . --rebuilt release/rebuilt/pdflatex --out build/pdf_comparison
```

The local pdfLaTeX gate is closed. At completion of this acceptance run,
GitHub-hosted CI was unexecuted because Push permission was withheld. The
author subsequently authorized public Push and selected MIT for software;
see STATUS.md and repository Actions for the current publication/CI state.
