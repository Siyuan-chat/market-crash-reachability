# Public research repository maintenance — 20 October 2026

This documentation revision makes V14 the primary GitHub manuscript and separates current research navigation from historical original-baseline evidence. Current status remains [STATUS.md](STATUS.md); [VERSIONS.md](VERSIONS.md) is the single version reference.

## Implemented changes

README now explains the question, systemic-loss criterion, main results, assumptions, evidence and reproduction routes. The overview adds a compact academic FAQ. The consolidated [result matrix](RESULTS_AND_EVIDENCE.md) links stable V14 labels, original canonical Lean families, exact hypotheses, analytical proofs, interval protocols and commands. Reproduction is divided into original quick/full, V14 static/build, loss–breadth and pinned Lean targets. Historical technical records remain at their established paths with scope banners; no published research asset was moved.

The root workflow instructions and obsolete execution queue were removed. Their scientifically necessary model-fidelity and result-scope information remains in the original manifest, individual scope audits, theorem map and certificate provenance. Session IDs, pause/resume commentary and repeated release authorization queues were omitted from current summaries. Git history is preserved. No human review, external audit or publication was invented.

## Publication conflict and citation integrity

Live retrieval on 20 October confirmed [Zenodo V13](https://zenodo.org/records/23444647) and [the immutable software record](https://zenodo.org/records/23428183). The [SSRN record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079) now displays **46 pages, revised 19 October 2026**, and an abstract containing V14 additions, conflicting with historical 37-page V13 status text. The current SSRN PDF has not been matched to a local artifact. Further verification of the concept DOI found [Zenodo V14, DOI 10.5281/zenodo.23478787](https://zenodo.org/records/23478787), deposited 20 October 2026. The record explicitly identifies V14, 46 pages, PDF commit `d548d287e221097b82b46cb7affbfd366a96875b` and source commit `3b6dc06bcdba4ec18764ace6adf1c0211be14006`; its displayed MD5 matches the retained GitHub manuscript exactly. This verified newer deposit supersedes the initial assumption that V13 was the latest external deposit. V13 remains preserved; no journal acceptance is asserted. CITATION.cff retains its software version, commit, software DOI and preferred paper DOI; the explanatory note records both the newer verified V14 deposit and the changed SSRN display.

## File disposition

ARCHIVE below means historical material retained in place with an explicit scope banner or rewritten historical framing, preserving deep-link compatibility; no directory relocation was needed.

| File | Disposition | Reason |
|---|---|---|
| `AGENTS.md` | REMOVE | Obsolete operational instructions and execution queue; scientific scope already retained in manifest, audits and proof sources |
| `CITATION.cff` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `README.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `REPRODUCE.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/ENGINEERING_CHANGES.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `docs/MATHEMATICAL_RESULTS.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/PDFLATEX_ACCEPTANCE.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `docs/PHASE2_REVIEW.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `docs/RELEASE_CHECKLIST.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/REPRODUCIBILITY.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/RESEARCH_OVERVIEW.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/STATUS.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/V13_PDF_REVIEW.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `docs/V13_REVIEW_RESPONSE_MATRIX.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `docs/V13_VALIDATION_STATUS.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/V14_SIFIN_V11_MIGRATION.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `docs/VALIDATION_REPORT.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/A01_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/A02_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/A03_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/C01_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/C03_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/C05_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/CODEX_EXECUTION_PLAN.md` | REMOVE | Obsolete operational instructions and execution queue; scientific scope already retained in manifest, audits and proof sources |
| `formal/D01_SCOPE_AUDIT.md` | REWRITE | Only internal reviewer/process phrasing normalized; mathematical scope, source identities and evidence retained |
| `formal/DIRECT_PAPER_PROOF_ROUTE.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/FORMALIZATION_STATUS.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `formal/MODEL_FIDELITY.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/ORIGINAL_RESULT_MANIFEST.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `formal/PHASE2_BV_GATES.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/PHASE3_AE_GATES.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/PHASE4_ATOMIC_GATES.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/README.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `formal/THEOREMS_3_1_3_2_COMPLETION_AUDIT.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/THEOREM_MAP.md` | ARCHIVE / REWRITE | Historical technical evidence retained at original path; dated scope clarified and obsolete operational sections shortened where present |
| `formal/WHOLE_PAPER_LEAN_COMPLETION.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `submission/siam/README.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `submission/v14-turnover-dissipation/README.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |
| `verification/loss_breadth/README.md` | REWRITE | Current reader navigation, version accuracy, formal scope or reproduction clarity |

| `docs/VERSIONS.md`, `docs/RESULTS_AND_EVIDENCE.md` | ADD | Consolidated version and evidence references |
| `submission/README.md` | REWRITE | Current V14 entry point; fixed V13 archive and live SSRN record distinguished |
| `translations/README.md` | REWRITE | Original V12 translation scope distinguished from current V14 additions |
| `scripts/check_documentation.py`, `.github/workflows/documentation.yml` | ADD | Standard-library deterministic documentation QA and lightweight CI |
| Manuscripts, PDFs, Lean source, verification algorithms, rational controls, fixture data, archival snapshots and input SHA manifests | KEEP | Scientific and immutable evidence; no changes in this documentation diff |
| LICENSE, NOTICE.md, pyproject.toml and V14 PDF publication workflow | KEEP | Licensing boundaries, scientific dependencies and publication mechanism preserved |

## Scientific integrity

The maintenance diff is measured from `5f34f4991640829cfa9b3585a4564d44cbc3f645` on the existing Lean cleanup branch. It changes documentation, a citation note, documentation QA/CI and the active working-tree release manifest only. No mathematical statement, hypothesis, analytical proof, Lean proof semantics, numerical algorithm/result, exact rational input, manuscript AI-use declaration, historical PDF, archive snapshot, tag or release was edited. The current release checksum file is maintained only for changed documentation paths; original numerical input manifests and archived software identities are preserved.

This branch was based on `codex/lean-scope-cleanup`, one commit ahead of main at task start. During delivery, that earlier cleanup was merged separately as PR #29. Main commit `9283ac7` has the identical tree to the original review base, so the documentation PR now targets `main` with the same documentation-only diff. No merge of this documentation PR is part of the maintenance delivery.

## Executed validation

The successful Python environment was 3.11.17 with NumPy 2.1.3, SciPy 1.14.1 and SymPy 1.13.3 from the existing project environment. Initial default-Python attempts used 3.10.11 with missing dependencies and script search-path failures; these failures were retained and resolved by selecting the project interpreter.

| Command / check | Result and actual scope |
|---|---|
| `python scripts/run_checks.py quick` | PASS: all six original quick programs |
| `python scripts/check_v14_resource_bound.py` | PASS: manuscript consistency, six main-table interval paths, exponent/resource and robustness checks |
| `python scripts/check_sublinear_severe_extension.py` | PASS: ordinary numerical radial-control and ledger regression; not rigorous proof |
| `python verification/loss_breadth/verify_all.py` | PASS: all twelve internally interval-checked retained controls and input/program hashes |
| `lake build` in `formal/lean` | PASS with existing lint warnings after verified-identical project inputs allowed reuse of pinned local dependency/build cache. Initial uncached attempt failed cloning Mathlib through the unavailable proxy |
| `python formal/check_proof_integrity.py` | PASS: 1,211 declarations audited; no unfinished proofs or extra axioms; all sixteen original canonical proof families present. This does not formalize the five V14 additions |
| `python scripts/build_v14_resource_bound.py` | FAILED: Windows TemporaryDirectory ACL denied copying `main.tex`; preserved original builder unchanged |
| Isolated fixed-directory pdfLaTeX/BibTeX build | PASS: same source/template/figure inputs, reference convergence, no unresolved citations, missing glyphs or overfull boxes. This is a separately identified fallback, not success of the original wrapper |
| `python scripts/run_checks.py full` | Not rerun: heavy original certificate regeneration; original algorithms/inputs unchanged. Quick consistency and separate V14 interval checks executed |
| `python scripts/check_documentation.py` | PASS: 69 Markdown files and 10 authoritative documents; local targets/anchors, version/scope markers, known DOI set, citation identities and program references |
| Documentation checker regression fixtures | PASS: thirteen positive/negative fixtures covering broken assets/headings/line ranges, unknown DOIs, verified V14 DOI punctuation, current version, formal scope, script paths, citation DOI roles and legitimate disclosures/history |
| CFF YAML parse and identity assertions | PASS: YAML syntax and fixed DOI/version/commit roles; a full CFF-schema validation was not rerun |
| `python scripts/check_hashes.py` | PASS: 329 active manifest entries; changed documentation hashed with repository LF bytes. Historical input manifests and archive identities unchanged |
| Protected-file byte comparison | PASS: 293 preexisting non-documentation files match baseline Git blob bytes exactly, including scientific source, PDFs, numerical inputs/algorithms, Lean source, archival files, licenses and existing workflows |
| `git diff --check` | PASS: whitespace consistency; final staged scope reviewed before commit |

Full local stdout/stderr and compact result JSON are retained outside the public tree in the sibling maintenance evidence directory: `docs-quick/`, `docs-interval/`, `docs-tex/`, `docs-manual-tex-run/`, `cached-lean/`, and `cached-axioms/`. Build products remain ignored and are not replacement published artifacts. No validation task is scheduled to continue later.

## Repository discoverability metadata

The live repository API showed description `Reproducibility companion to When Can Markets Crash Without News? — V12 Final, Siyuan Ye.`, no topics and no homepage. Available GitHub connector tools support repository reads and Git/PR operations, but expose no repository-description/topics update endpoint; the host has no GitHub CLI. Metadata was **not changed**. Proposed exact values for the repository's About settings:

- Description: `Reproducible research, rigorous interval certificates, and Lean proofs for When Can Markets Crash Without News? by Siyuan Ye.`
- Topics: `systemic-risk`, `market-microstructure`, `mathematical-finance`, `price-impact`, `interval-arithmetic`, `lean4`, `reproducible-research`.
- Homepage: leave unchanged unless a suitable real project page is selected. No homepage was invented.

Apply these through GitHub repository → About → Edit → Description/Topics. Research title, author, field, methods, assumptions, manuscript versions, evidence and valid source links are consistently visible in the public documentation. No speculative SEO files were added.

The historical Zenodo version records `23438609` and `23427880` also returned HTTP 200 with matching title and DOI. The concept DOI resolved to V14, establishing the current version reference.

## Remaining limitations

The changing SSRN PDF/source identity remains unresolved: direct public PDF retrieval returned HTTP 403, so no byte-identity claim is made. The stock V14 build wrapper remains affected by a local Windows temporary-directory ACL problem; the isolated TeX build passed. V14 additions remain outside original Lean coverage and have no claimed independent external proof audit. Repository About metadata remains proposed. None of these limitations is represented as a passing check or a new publication event.
