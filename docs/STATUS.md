# Current project status

Scope: publish the curated V12 Final repository with its original mathematical
content and final artifacts, preserving the completed reproducibility evidence.

Latest author decisions (2026-10-15): public repository publication is authorized;
the code license is MIT. The public repository is
https://github.com/Siyuan-chat/market-crash-reachability and includes the reviewed
README. The curated tree is published on `main` at software version 1.0.0rc1.
Source-publication commit: `ba2af5771bbaf74166545818a0e90fe6fea0fb2b`.
Local Python 3.11 and pdfLaTeX/original-PDF acceptance is complete.

Remote acceptance completed successfully on that source-publication commit:
- [Push / quick CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38744237565).
- [Full CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38744445130):
  80,000-step interval regeneration, exact certificate identity, regressions,
  figures, clean Ubuntu pdfLaTeX builds and downloadable evidence all passed.
- An unauthenticated clone passed all 107 distributed-file SHA-256 checks.

This acceptance-status update changes documentation/checksums only; research
sources and verification code remain identical to the validated source commit.

Evidence: `release/validation/`, `release/SHA256SUMS`, SOURCE_INVENTORY.json,
CERTIFICATE_PROVENANCE.json, ENGINEERING_CHANGES.md, VALIDATION_REPORT.md and
PDFLATEX_ACCEPTANCE.md. The overflow reported in the initial Tectonic build
is absent from both the original PDF and the pdfLaTeX rebuild.
The original ZIP and history remain in the sibling local private backup.

The manuscript's generic availability paragraph remains accurate for the
curated package; README and CITATION.cff supply the real repository URL.
The original PDFs and LaTeX sources are retained unchanged. Software licensing
is in LICENSE; separate research-artifact rights are in NOTICE.md.

Next: obtain separate authorization for v1.0.0, Tag/Release creation or Zenodo archival. None of those
formal-release actions is included in the current Push authorization. No
scheduled continuation has been created.
