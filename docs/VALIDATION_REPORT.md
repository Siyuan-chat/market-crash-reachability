# Local acceptance report

Acceptance date: 2026-10-15 (Asia/Tokyo).

## Passed

- A separate clean source directory and fresh virtual environment installed the
  project with Python 3.11.17 and the dependency set in requirements-lock.txt.
- Basic regression: 75 assertions. Earlier multiday model: 44 checks.
- Symbolic generalized-coordinate identities and independent two-asset ODE
  equivalence passed. Selected figure data and all source figure references
  passed. All distributed figure filenames were independently regenerated;
  generated numerical summaries matched supplied fixtures (relative 1e-8,
  absolute 1e-11 for auxiliary floating-point figure summaries only).
- Full 80,000-step integer outward-rounded certificate regenerated with
  byte identity to the supplied final certificate. Its algorithm and assertions
  are unchanged; output newline normalization is documented separately.
- Certified compensator endpoint enclosure:
  (1.40478740981483169755689137671669,
  1.40555423111958453123472102742373), strictly inside the published bounds.
  Certified crisis enclosure is approximately (0.0207834039, 0.0208379753).
  Maximum compensator gross-rate upper bound: 0.284480404287 < 0.285.
  Exact-rational crisis tests, daily bands and dollar closure passed.
- Independent DOP853: y(40)=1.4051608219897378 and crisis=0.02081139744399201;
  independent target dollar residual approximately -2.08e-16.
- Fixed-path band and exploratory k-count sensitivity audit passed. These
  outputs retain their stated distinct mathematical scopes.
- Main and supplementary sources and distributed PDFs are byte-identical to
  the original final inputs. Included figure assets are also unchanged.
- Both documents compiled with Tectonic 0.17.0 in the initial preview. The
  subsequent clean pdfLaTeX acceptance is now complete: 34 and 10 pages,
  three and two passes respectively, no overfull boxes, unresolved references
  or remaining label-rerun warnings. All 44 pages were raster-compared and
  reviewed in contact sheets; extracted differences were classified as math-font
  Unicode mapping. No substantive text, numbers or reference changes were found.
  See PDFLATEX_ACCEPTANCE.md and release/validation/pdflatex/ for evidence.
  CITATION.cff passed the CFF 1.2.0 schema validator.
- Whitelist/source inventory and static scans found no private keys, credential
  assignments, developer absolute paths, internal corporate material or bundled
  third-party full texts in the publication files. The intentional author name,
  academic references and AI-assisted tools declaration remain. This is a static
  review, not a guarantee of detecting every possible sensitive string.

## Limits and publication gates

- The rebuilt pdfLaTeX PDFs differ in bytes, font Unicode mappings and raster
  detail from the original PDFs; no byte/pixel equivalence is asserted. The
  original PDFs remain the release candidates and are unchanged.
- Correction to the initial preview: the 12.6654 pt overflow was specific to
  Tectonic. It does not exist in the original PDF or the current pdfLaTeX
  rebuild. Four underfull table-paragraph warnings remain in the latter and
  do not clip content. No manuscript edit was made.
- The author subsequently authorized public publication and selected MIT for
  code. The repository URL is https://github.com/Siyuan-chat/market-crash-reachability.
  Check Actions for actual Ubuntu CI results; the local evidence does not
  certify a remote workflow. No formal release tag or DOI is asserted.
  Subsequent remote acceptance is complete for source-publication commit
  `ba2af5771bbaf74166545818a0e90fe6fea0fb2b`: both the Push quick run
  (38744237565) and manual full run (38744445130) succeeded. The latter includes
  exact certificate regeneration, figure generation and clean Ubuntu pdfLaTeX.
  Evidence artifacts are downloadable from the corresponding Actions run.
- MIT applies to software as scoped in NOTICE.md. No CC BY permission was
  added to the manuscript or figures. No claims of journal acceptance or
  machine formalization have been introduced.

Run `python scripts/run_checks.py full` for the numerical acceptance suite;
`python scripts/reproduce_figures.py` for the complete figure regeneration;
`python scripts/build_papers.py` for pdfLaTeX; and
`python scripts/check_hashes.py` for the explicit distributed-file manifest.
Raw verification reports and logs are in `release/validation/`.
