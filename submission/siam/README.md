# SIAM standard review edition

This is a formatting-only edition of the canonical English V12 Final manuscript,
using the supplied SIAM `siamart251216` standard template (2025-12-16).

- [Manuscript PDF](manuscript.pdf) · [LaTeX](main.tex)
- [Supplement PDF](supplementary.pdf) · [LaTeX](supplementary.tex)
- [Shared preamble](shared.tex) · [Bibliography](references.bib)

The manuscript has 33 pages and the separate supplement 9 pages. Both use SIAM
review line numbering, running headers, the class typography, and hidden link
colors. Keywords and MSC codes use the class environments; references are
regenerated with `siamplain`. The supplement uses the class's `SM` numbering
and the same title/author as the article. Main theorem, equation, figure and
table numbers are unchanged. All body prose and mathematical content are
unchanged after reversing an explicitly recorded display line break and
front-matter/section formatting. The AI-assisted tools declaration is preserved.

The canonical files under `paper/` and `supplementary/`, translations, Lean
formalization and numerical certificate are not replaced or modified.

## Rebuild

Install Python 3.11 and a TeX distribution with pdfLaTeX, BibTeX, `ntheorem`,
`cleveref`, `algorithms`, `hypcap`, `lineno`, `microtype` and `xurl`, plus the
original manuscript's packages. On Ubuntu, install `texlive-latex-extra`,
`texlive-fonts-recommended` and `texlive-science` (which supplies `algorithm.sty`).
From the repository root:

```bash
python scripts/check_siam_submission.py
python scripts/build_siam_submission.py
python scripts/build_papers.py --output-root build/siam-baseline
python scripts/check_siam_submission.py --compiled
```

The build reads the pinned complete distribution in `third_party/siam/`,
without contacting SIAM's server (which can reject CI runners with HTTP 403).
Its unmodified members come from the [official standard macro archive](https://epubs.siam.org/pb-assets/macros/standard/siamart_251216.zip)
plus the separately supplied official documentation source. Alternatively, pass
`--template-zip /path/to/siamart_251216.zip` for offline/local template use.
Portable TeX installations can supply `--pdflatex /path/to/pdflatex` and
`--bibtex /path/to/bibtex`. The canonical comparison script accepts its own
`--pdflatex` option. A fresh build directory prevents stale auxiliaries.

Build outputs, logs, the original-to-SM label map and content checks are in
`build/siam/`. `author-sources/` contains a standalone set of author-owned
sources and original figures, but excludes SIAM's class/style files. Install
those from the official distribution to compile the sources. The repository
snapshots use original figure assets through relative paths rather than
duplicating all figure PDFs. `--update-edition` intentionally refreshes the
committed sources/PDFs after a successful zero-overflow build. PDF timestamps
may change bytes between builds; mathematical/prose equivalence and numbering
are checked independently of PDF byte identity.

## Template rights and scope

The SIAM class prohibits modification and redistribution by itself. The supplied
ZIP lacks `docsiamart.tex`, a file named in its redistribution conditions. The
repository therefore preserves the complete distribution as a single ZIP under
`third_party/siam/`, adding that missing file from SIAM's official download.
All member contents, including the class/style, are unmodified. Provenance and
license conditions are recorded there. The CI author-source artifact excludes
SIAM's third-party files; they are not relicensed under MIT.
They retain SIAM's rights; the manuscript/supplement and their generated sources
retain the author's existing copyright and do not inherit software MIT.

The [official author guide](https://epubs.siam.org/journal-authors) distinguishes
standard templates from the multimedia/online-only templates for SIFIN, SIADS,
SIAGA, SIIMS, SIMODS and JUQ. This edition follows the archive supplied by the
author and is **not** represented as a journal-specific SIFIN edition. The target
journal has not yet been confirmed. Once selected, check its required class,
page policy, journal-name abbreviations and submission metadata. The existing
author information is retained; no email, address, ORCID, funding, submission
date or acceptance status has been invented. Complete contact details and any
cover letter must be supplied before an actual journal submission.

This work prepares files and GitHub publication only. It does not submit to a
journal or create a GitHub Tag/Release.
