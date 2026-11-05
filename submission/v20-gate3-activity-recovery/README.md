# V20: Gate 3 activity-driven recovery — **WORKING DRAFT**

This directory is the **first substantive English manuscript reconstruction** after scoped Gate 1 and core-construction Gate 2 reviews. It is **not** an accepted Gate 3 manuscript, release, or DOI. Original author 40-page PDF and GitHub V16 remain the scientific coverage baseline. V16/V17 files are not modified.

## Draft contents as of 2026-11-05

- `main.tex`: 17 primary sections including appendices; 26 theorem/lemma/proposition environments plus a new mathematical corollary; both an analytic severity ladder and a separately labelled numerical reconstruction table. The article-class fallback preview is about 25 pages, **not** evidence of full original-paper coverage.
- `shared.tex`: SIAM interface with an article-class fallback only for inspection when the SIAM class is absent.
- `figures/`: six V19-model PDF plots. The I/II numerical trajectories are **NUMERIC_ONLY**, not plots of the rigorously certified new explicit high-budget witnesses. Construction III is an internally cross-checked interval proof, **not an external certificate**.
- `../../research/v20-gate3/GATE1_GATE2_RECHECK_GATE3_ENTRY_2026-11-05_ZH.md`: scope-limited independent audit and go/no-go.
- `../../research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv`: all 43 original items preserved; **32 drafted, 4 partial, 7 partial-open, 0 not yet drafted**. Per-row status is the governing coverage record.

## Reproducibility/build note

The manuscript cites the preserved 33-entry original BibTeX at `../v16-three-certified-constructions/references.bib`; review/correct citations for the final version. Build from this directory with the repository's SIAM manuscript environment and working LaTeX/BibTeX tooling. An independent **local fallback article-class PDF** was rendered on 2026-11-05 (25 pages, checked for undefined references and overflow). Its *temporary* nine-entry BibTeX substitute was for offline display only and is **not** the scholarly reference baseline.

## Core research claims and acceptance scope

1. Activity-driven recovery occurs only during *actual* nonnegative paired-dollar execution; `C0` admits simultaneous gross buy/sell at a node and `C1` does not. Close each individual dollar ledger and count true seller-side share inventory.
2. Gate 1 **reverse mathematical audit** is scoped to checking correct assumptions, formula derivations, invalid V16 transfers, and OPEN boundaries. It does *not* settle full phase diagrams or optimal breadth.
3. Gate 2 core constructions: (I) exact all-ten half-price analytical positive-h witness; (II) p=0 all-severity nine-target fixed-resource positive-h witness; (III) two-session C1 five-target internally cross-checked interval witness. Previous low-turnover floating-point roots for I/II remain NUMERIC_ONLY; no inference of real-world crash probability.
4. General 0<=p<1 severity extension and all appendix statements must be independently checked and fully stated in the final manuscript. The complete quantitative proof and parameter source remain `research/v19-activity-recovery/`, not abbreviated into unexamined slogans.

## Gate 3 completion obligations

- Restore **all 43** source-coverage items with either a correct theorem/proof, explicitly bounded result, or substantively explained open problem; no dropping sections just to shorten the paper.
- The second-round draft restores a BV appendix (L01), a bounded-gross-share-rate appendix (A05/T08), heterogeneous quadratic identities and a two-node counterexample (P12), and a general-p radial/inventory appendix (A07). All still require independent line-by-line peer-style review. The sharp all-asset/full-phase classification, general-p uniform cut roots, and 6-to-9-target repeated-band reachability remain open.
- Audit all source bibliography entries and finish the final SIAM template/build review. Match every asserted theorem to explicit hypotheses and its actual evidence level.
- Replace any unsupported theorem statement, verify full SIAM build/figure/cross-reference layout, then prepare a complete English paper before any line-by-line Chinese translation or editable Word artifacts (Gate 4).
- Do **not** release a new edition or overwrite V16/V17 until this Gate 3 acceptance is independently recorded.

## Round 2 update (still not Gate 3 acceptance)

- New proof: activity-driven heterogeneous p=2 weighted-log balance and a C1 two-node dollar-closed counterexample for unequal kappa_i/D_i.
- Necessary rolling-limit bound: all N assets cannot both close at lower limits in two consecutive sessions, so the ten-asset two-day 25% optimum is bounded by 5 <= k* <= 9, **not** known to equal 5 or 7.
- Both analytic and historical numerical severity tables are kept; old I/II floating-point roots remain `NUMERIC_ONLY`.
- Tests: `check_gate3_draft.py` is structural, `audit_new_math.py` is exact rational algebra, and `audit_bibliography.py --strict-original` verifies the original 33-entry source corpus in GitHub Actions. These checks do not replace theorem auditing.
