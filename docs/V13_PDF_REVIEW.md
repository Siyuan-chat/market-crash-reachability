> Historical technical record. Applies to its named source revision; see [current versions](VERSIONS.md) and the current evidence matrix. Retained at this path for provenance and compatibility.

# V13 page-by-page writing and PDF review — 18 October 2026

Reviewed the complete rendered PDF and extracted text; the second-half prose
also received an independent read-only review. The final PDF has 37 pages.
This is an editorial/layout review, not a fresh mathematical proof or a new
80,000-step certificate run.

Corrections: fixed the page-3 `(author?)` narrative citation by naming the
authors explicitly; removed the SIAM review-only footer through the author
preamble; clarified the abstract's drawdown criterion and small-rate bounds;
changed qualifying-asset sale counting to “at most once”; clarified the scope
of the terminal-interval cost bound and historical certificate regeneration;
removed revision-process wording; replaced a forced page break by a float
barrier. The original numbered statements and numbered equations are unchanged.

| Final page | Writing / rendered-page result |
|---|---|
| 1 | PASS — Abstract and introduction; criterion and small-rate wording clarified |
| 2 | PASS — Literature and result overview |
| 3 | PASS — Market assumptions; narrative author citation fixed |
| 4 | PASS — Execution/settlement and price response |
| 5 | PASS — Normal form and drawdown definition |
| 6 | PASS — Resource definitions and cost identity |
| 7 | PASS — Global barriers |
| 8 | PASS — A/B/C classification |
| 9 | PASS — Response examples and local result |
| 10 | PASS — Local proof and common-budget illustration |
| 11 | PASS — Full-coverage boundary |
| 12 | PASS — Execution resources; sale-counting explanation clarified |
| 13 | PASS — Dimensionless normalization and finite-rate setup |
| 14 | PASS — Rate and band bounds |
| 15 | PASS — Quadratic finite-rate bound |
| 16 | PASS — Attainability and controls |
| 17 | PASS — Rate plot/table and multiday introduction |
| 18 | PASS — Rolling bands and breadth criterion |
| 19 | PASS — Systemic criterion and rolling shock bounds |
| 20 | PASS — Compensator plot and all-asset obstruction |
| 21 | PASS — Obstruction proof and preparatory recovery |
| 22 | PASS — Receiving-capacity condition |
| 23 | PASS — Two-session certificate setup |
| 24 | PASS — Certified bounds and sensitivity |
| 25 | PASS — Resource comparison table and price plot |
| 26 | PASS — Execution plot and cost discussion; excess page break removed |
| 27 | PASS — Resilience, metric dependence and witness interpretation |
| 28 | PASS — Extensions, conclusion and code availability |
| 29 | PASS — Provenance and Appendix A accounting; at-most-once clarification |
| 30 | PASS — Appendix B expansions |
| 31 | PASS — Appendix C construction |
| 32 | PASS — Appendix C closure and resources |
| 33 | PASS — Appendices C/D constructive bounds |
| 34 | PASS — Appendices E/F and numerical tables |
| 35 | PASS — Appendices F/G certificate protocol |
| 36 | PASS — Certificate completion and references |
| 37 | PASS — References completion |

Validation: four pdfLaTeX passes plus BibTeX completed; no overfull boxes,
missing glyphs, undefined references/citations or natbib undefined-author warning.
All 37 pages were rendered and inspected. The static V13 identity check passed
(26 unique cited keys). Build report: `qa_siam/v13-page-review/build_report.json`
in the local review workspace; final PDF SHA-256: `2837b37a8623bcb98f83c9e3189307dea8e40d5b4e45bd6f670849d5a4e2936e`.
Zenodo public file MD5 matches local `e61cf62ac212e84da6cd0e5a8bb48517`.
The portable public PDF is `submission/v13-review-response/manuscript.pdf`.
Earlier PDF editions and the immutable software DOI are preserved.
