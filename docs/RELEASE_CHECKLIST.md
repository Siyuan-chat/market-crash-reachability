# Archive identity and release verification

The [version reference](VERSIONS.md) records the manuscript deposits and immutable software identity. This file retains the technical checks applicable to future separately versioned archives; it is not an execution queue.

- Identify the exact source commit, software version, manuscript edition and license boundaries in NOTICE.md.
- Retain original source/PDF pairs, certificate inputs and provenance manifests; rebuilt PDFs belong in separate output directories.
- Run relevant reproduction commands, documentation QA and hash verification, recording failures and environment limits.
- Check citation metadata against actual deposited records. Assign no DOI, acceptance status or release identity that has not been issued.
- Distinguish original certificate byte comparisons from cross-environment PDF comparisons.

Historical original-baseline checks and PDF comparison evidence remain in [VALIDATION_REPORT.md](VALIDATION_REPORT.md) and [PDFLATEX_ACCEPTANCE.md](PDFLATEX_ACCEPTANCE.md). No software version promotion, tag or existing release alteration accompanies the documentation cleanup.
