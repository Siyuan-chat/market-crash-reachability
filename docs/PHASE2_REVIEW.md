# Phase 2 local review and acceptance

Review date: 2026-10-15. Canonical mathematical baseline: English V12 Final,
commit `e5339a47f29ccb669d1f228ca930a1c1146200bf`.
This is a **historical local review checkpoint**, not the current publication
status. All pending CI/approval/merge items and statements of no public PR,
merge or Zenodo deposit below apply to the 2026-10-15 checkpoint only.
Phase 2 was subsequently merged into public main; the paper and fixed code
snapshot now have separate Zenodo DOIs, and SSRN is public. See
[current project status](STATUS.md) for links and the archive commit boundary.
The local results and original acceptance checklist below are retained unchanged
as historical evidence, not reclassified as newly performed checks.

## Delivered scope

The local review branch integrates complete Chinese and Japanese manuscript and
supplement drafts, a glossary, protected-content checks, a fresh-source PDF build,
and a partial Lean project. The root README contains all language and formalization
entry points. Original English manuscript, bibliography, figures, verification
algorithms, model parameters and final certificate remain unchanged.

Development commits:

- Formal foundations: `661d3e9` on `phase2/formalization` (subsequent CI installer
  and audit-discovery fixes are included in the review candidate).
- Translations: `cde2a4c` on `phase2/translations`.
- Integration: local `phase2/review`; its final commit is recorded in the external
  review package's `REVIEW_IDENTITY.json`, avoiding a self-referential source hash.

## Actual validation

| Check | Local result | Evidence / repeat command |
|---|---|---|
| English identity | PASS: seven baseline hashes; no changes in paper, supplement, verification or certificate data | `docs/PHASE2_BASELINE.json`; translation checker |
| Lean kernel | PASS: fixed Lean 4.19.0, pinned Mathlib, fresh project build using pinned dependency cache | `cd formal/lean && lake exe cache get && lake build` |
| Proof completeness | PASS: all 34 project theorem declarations audited; no sorry/admit/custom axioms; only propext, Classical.choice, Quot.sound | `python formal/check_proof_integrity.py`; `build/formal/` |
| Complete result inventory | PASS: exact English statements for all 17 numbered results | `formal/THEOREM_MAP.md` |
| Math and structure | PASS: each main has 926 protected mathematical units; each supplement has 90; contents and order equal | `python scripts/check_translation_consistency.py` |
| References and numbering | PASS: labels, references, citations, theorem environments, explicit numeric sequences, scientific identifiers and figure/table structure; compiled label numbers equal | `python scripts/check_translation_consistency.py --aux-root build/translations` |
| TeX | PASS: English pdfLaTeX comparison plus all four LuaLaTeX drafts; stable references; no missing glyph or overfull warning | `python scripts/build_translations.py`; `build/translations/build_summary.json` |
| Layout | All 79 translated pages rendered and overview-reviewed, selected pages inspected at reading scale; no text outside page bounds | Chinese 28 + 10 pages; Japanese 31 + 10 pages |
| Python reproduction | PASS in a newly created Python 3.11 environment: all eight full-mode commands | `python -m pip install .`; `python scripts/run_checks.py full` |
| Interval certificate | PASS: regenerated 80,000-step certificate byte-identical to the canonical certificate | SHA-256 `354c7797c1e25ebee143d04d11e23ec92cb93214b7333eed7fcd91dd0493c18f` |
| Source integrity | PASS after integration; per-file SHA-256 manifest | `python scripts/check_hashes.py`; `release/SHA256SUMS` |
| Security / portability | No secret-pattern or machine-specific path detected in added/modified repository text; no font binaries or dependency cache included | local review audit; pattern scan is not a guarantee |
| New GitHub Actions | YAML/static and local-command validation only; **remote runs pending** | `.github/workflows/lean.yml`, `translations.yml` |

Local Lean compilation retains advisory tactic/unused-variable lint warnings.
Generated PDFs are not committed twice. The review package supplies the four
draft PDFs and exact original English PDFs; its independent SHA256SUMS binds
the generated files, code archive and validation evidence. Build timestamps may
change PDF bytes on a later rebuild; canonical English PDFs are never replaced.

## Review findings and limitations

Independent review checked formal scope and CI logic. The Lean installer was
corrected to use its absolute Elan executable within the installation step.
Language review corrected two Japanese semantic role errors (shares versus time;
small amplitude h versus k-th largest loss), restored M and MSC identifiers, and
clarified Chinese compact-neighborhood and positive-orthant terminology.
Final sources were rebuilt and checked after corrections. Formula equality alone
does not prove prose equivalence; these remain complete scholarly drafts awaiting
the author's language acceptance.

No complete numbered paper theorem is claimed Lean verified. The partial project
does not yet prove admissible-path equivalence, inverse smoothness, actual recovery
dynamics, Jensen barriers, A/B/C classification, sharp horizon/resource/rate
theorems, or multiday capacity results. Proposition 7.6 remains an independent
Python interval computer-assisted existence proof; Lean does not check its
rounding logic or certificate. See `formal/FORMALIZATION_STATUS.md` for precise
hypotheses, theorem names and next steps.

Original figure-internal English labels, bibliography titles, and protected
English phrases inside math are deliberately retained. Language REVIEW files
document these items. No new DOI, arXiv ID, journal acceptance or author ORCID
has been invented. The original AI-assisted tools statement is retained in
English and translated in both editions.

## Local PR preview

Proposed title: **Add partial Lean foundations and complete Chinese/Japanese research editions**.

Proposed description: Add a pinned Lean project proving coordinate, conservation
and p=0/1/2 response foundations, with a complete paper-result map and kernel
axiom audit. Add complete Chinese/Japanese manuscript and supplement drafts,
exact protected-math and compiled-number checks, fresh-source PDF builds and CI.
The English mathematical baseline and interval proof are unchanged. Local kernel,
translation and full Python reproduction checks pass; remote CI and author
language/public-edition approval remain pending.

No remote PR has been opened, no Phase 2 branch pushed, no public main merge,
Tag, Release or Zenodo deposit has been performed.

## Author's final acceptance checklist

- [ ] Accept Chinese terminology and complete text, including supplement.
- [ ] Accept Japanese terminology and complete text, including supplement.
- [ ] Accept the clearly partial Lean scope and unfinished-results list.
- [x] Confirm permission to publish the translated research editions; their
      text/figures retain copyright and are excluded from software MIT. No CC
      grant is presumed. Any future journal agreement needs separate review.
- [x] Approve pushing the review branch and opening the public PR.
- [ ] Run and review both new GitHub workflows on the real remote PR.
- [ ] Approve public-main merge only after mathematical/language acceptance and CI.
- [ ] Choose the final Release version; bind its commit/tag, PDFs, certificate,
      source and checksums. No version DOI should be cited before it exists.

The review package is a local preview. The software's existing MIT choice remains
in force; it does not decide the publication status or reuse license of translations.
