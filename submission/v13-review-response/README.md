# V13 review-response draft — 18 October 2026

This directory contains the **editable, not-yet-published V13 candidate** of
*When Can Markets Crash Without News?*, based on the [public 18 October English
edition](../siam-language-revision/README.md).

- [Revised LaTeX](main.tex) · [Revised bibliography](references.bib) · [shared SIAM preamble](shared.tex)
- [Review-response tracking matrix](../../docs/V13_REVIEW_RESPONSE_MATRIX.md)
- [Validation status and non-claims](../../docs/V13_VALIDATION_STATUS.md)

**Do not cite this revision as an accepted journal paper or an interval-certified
new model.** All original numbered theorem statements, source numerical
certificates, Lean files, and published V12 PDF artifacts are intentionally
unchanged. The new exposition addresses recovery assumptions, cost accounting,
resource normalization, metric dependence, and literature placement. Extensions
requiring new proofs are described as future work, not included as results.

The main figure PDFs are reused from the previous English edition rather than
copied into this source directory. They remain unchanged.

## Reproduce the V13 candidate

From the repository root (Python 3.11 plus pdfLaTeX/BibTeX and TeX packages):

```sh
python scripts/check_v13_revision.py
python scripts/build_v13_revision.py
```

The build extracts the two SIAM-owned class/style components from the
repository's separately documented official template archive, compiles an
isolated copy, and writes `build/v13-review-response/main.pdf` and build
logs. No PDF is committed for this draft before compilation and layout review;
GitHub CI makes a build artifact available when its checks pass.

This revision is not a replacement for the archived paper and code DOIs. See
the [original reproduction guide](../../docs/REPRODUCIBILITY.md) for the
unchanged 80,000-step proof certificate.
