# Contributing and reporting issues

This repository accompanies a theoretical research manuscript. Reproducible corrections, mathematical counterexamples, independent audits and documentation improvements are welcome. A proposed change is **not** an amendment to a frozen published edition unless the author separately updates its archive.

## Before opening an issue

Please identify the **exact artifact**: a manuscript edition and section/equation label; a script and command; or a named fixed control/certificate. Include the Git commit, Python/TeX/Lean versions where relevant, the expected result and the actual outcome. Never infer that a GitHub working PDF and an older Zenodo/SSRN PDF have identical content. The current PDF's source identity is in [`manuscript-build.json`](submission/v14-turnover-dissipation/manuscript-build.json).

For mathematical issues, specify the hypotheses, admissible control class, and exact line of reasoning in question. For numerical reports, attach a **minimal reproducible input**, exact command and observed residual, without replacing the original certificate data.

## Pull-request checklist

- Is the change **analytical**, **interval-certified**, **ordinary numerical**, **formal Lean**, or **editorial/documentation**? State the evidence class.
- For manuscript edits, explain any altered theorem hypothesis, conclusion or label. Mathematical claims and proof steps are not changed merely to simplify English prose.
- Retain the original datasets, Lean proofs, historical PDFs, checksum records and versioned archive sources. Revise only explicitly authorized working files and their separate revision overlay; never rewrite the frozen [`release/SHA256SUMS`](release/SHA256SUMS).
- Run relevant checks from [REPRODUCE.md](REPRODUCE.md); for documentation links run `python scripts/check_documentation.py`. For a TeX edit provide a newly compiled PDF and render-review pages containing changed figures/tables.
- Distinguish archival DOI claims from mutable repository commits. No acceptance, independent verification or optimality assertion without matching evidence.

Source code is MIT licensed. Manuscripts, research data, figures, translations and the SIAM distribution are governed separately by [NOTICE.md](NOTICE.md).

