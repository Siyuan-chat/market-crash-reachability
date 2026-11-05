# V20 editorial provenance and CI repair audit — 2026-11-06

Status: **proposed repair, pending GitHub Actions retest**. No mathematical or Lean theorem is accepted by this document.

## Before

GitHub PR-head run 42054219647 failed `scripts/check_revision_hashes.py` on four editorial files: `README.md`, `docs/VERSIONS.md`, `scripts/check_documentation.py`, `submission/README.md`. The original `release/SHA256SUMS` and the historical 22-entry `release/SHA256SUMS_V14_R1` have **not been changed**. The mismatched paths are among the pre-existing narrowly whitelisted V14 editorial file paths, not historical certificate inputs or PDFs.

Run 42054219634 failed documentation link checking on a math expression in `research/v19-activity-recovery/GATE2_EXPLICIT_POSITIVE_H_CERTIFICATION_ZH.md`: `[...] ( ... )` was inside an **inline code span**, but the checker excluded only fenced code blocks. This repair excludes inline code spans from Markdown link detection while preserving checks on actual links.

Run 42054219429 failed because the GitHub copy of the V20 coverage register contained two **file-service spreadsheet parser wrapper lines** (`<PARSED TEXT FOR SHEET:...` and `TAB NAME:...`) and a synthesized leading `index` column. The original scientific 43 IDs were still present. This repair removes only that wrapper and synthetic column, and adds a regression assertion requiring the canonical `ID,` header before CSV parsing. It does **not** delete any of the 43 research items.

## After — separate, limited editorial overlay

New `release/SHA256SUMS_V20_EDITORIAL_R1` pins exactly the following current-file bytes:

- `README.md`
- `docs/VERSIONS.md`
- `scripts/check_documentation.py`
- `submission/README.md`
- `scripts/check_revision_hashes.py`

The verifier checks the set of paths exactly, and also requires them to be members of the **already permitted V14 editorial whitelist**. The merge order is frozen release -> historic V14 working revision -> narrowly pinned Lean entrypoint change -> current five-file editorial revision. The original two release manifests, original data, numerical certificates, formal proof files, historical manuscripts and previous identifiers remain unchanged.

Expected acceptance: the actual GitHub Actions rerun must pass `scripts/check_revision_hashes.py`, `scripts/check_documentation.py`, and `research/v20-gate3/check_gate3_draft.py` without skipping checks or suppressing errors. Any failure must be investigated rather than recorded as a green CI.

The separate Lean workflow issue (failure to unpack a 92-byte `leantar` download) is not addressed by these edits and must be fixed independently. The old V12/V14 Lean formalization Issues remain open until their paper-identical kernel proofs exist.
