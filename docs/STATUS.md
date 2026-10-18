# Current project status — V13 synchronization, 18 October 2026

The author authorized all-page writing review followed by public synchronization.
The reviewed 37-page V13 PDF is public on [Zenodo](https://doi.org/10.5281/zenodo.23444647).
The root README and preferred paper citation now identify V13; earlier PDFs are
preserved. See [page review](V13_PDF_REVIEW.md) and
[validation details](V13_VALIDATION_STATUS.md).

SSRN V13 revision succeeded on 18 October 2026. The public
[record, abstract 7622079](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079),
was verified to show 37 pages, the V13 abstract and revision date 18 October 2026.
The previous temporary reauthentication blocker is resolved.
V13 manuscript build CI passed (run 39086681193); Reproducibility CI passed
on da70760 (run 39086734505). No local background job or
automatic continuation has been started. The immutable software archive remains
DOI 10.5281/zenodo.23428183 (d6e2606); this editorial update does not rerun the
certificate or create a new code archive.

## Historical publication checkpoints

## Revised English preprint — 18 October 2026

The approved 33-page manuscript and its LaTeX sources are in
`submission/siam-language-revision/`; the root README opened this edition at that historical checkpoint.
Zenodo v2 is public at https://zenodo.org/records/23438609
(DOI 10.5281/zenodo.23438609; concept DOI 10.5281/zenodo.23427879),
with the unchanged supplementary PDF. Main PDF SHA-256:
`c4f870b05c31f839da3c4e503b25f9efe3cc2ab6f8f5b38110aa3472a325b0ff`.
SSRN revision succeeded under abstract 7622079. Its public page was checked
to show 33 pages and the revised abstract after submission.
The fixed software archive DOI 10.5281/zenodo.23428183 remains the historical
snapshot described below. Existing Lean work on main is preserved.

### Earlier publication records

# Current project status

Publication status updated 2026-10-17:

- Paper and supplement are public on [Zenodo](https://doi.org/10.5281/zenodo.23427880)
  and the paper is public on [SSRN, abstract 7622079](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079).
  SSRN public availability was confirmed by the author; this is not journal acceptance.
- The complete fixed source snapshot is archived as software on
  [Zenodo, DOI 10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183),
  version `1.0.0rc1+git.d6e2606`, commit
  `d6e2606590f955a6287c6945488a080e5acab004`. Later documentation changes
  are outside that immutable archive. All 215 archived Git blobs, 214 manifest
  hashes and six quick checks passed; the full certificate was not regenerated
  for this deposit.
- [CITATION.cff](../CITATION.cff) distinguishes paper and software DOIs.
  Software MIT and the research-artifact/third-party exclusions remain unchanged.
- No GitHub release/tag, promotion to final `1.0.0`, or journal acceptance
  is asserted. Those are separate from preprint publication and Zenodo archival.
- This documentation cleanup does not rerun scientific proofs or modify papers,
  code, data, archived snapshots or historical validation logs. No background
  process or scheduled continuation is running for it.

## Historical source-publication acceptance — 2026-10-15

The remaining text records that earlier checkpoint. Its authorization gates,
commit identity, counts and next steps apply to that checkpoint, not the current
publication status above; they are retained as historical evidence.

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
