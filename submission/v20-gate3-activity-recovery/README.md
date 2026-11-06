# V20 / Gate 3 — Activity-Driven Recovery (working scientific manuscript)

**Status 2026-11-05: Gate 3 in progress — NOT ACCEPTED / NOT A RELEASE.** The original 40-page author paper and repository V16 are the research-coverage baselines. V16/V17 sources and historical release/DOI remain unchanged. This V20 paper is a *substantive scientific reconstruction*, not a shorter replacement that omits research tasks.

## Working draft

- `main.tex` and `shared.tex`: English manuscript; 28-page article-class preview as of round 3, 17 first-level sections (including appendices), 11 theorems, 11 propositions, 5 lemmas and 1 corollary, 6 source research PDF figures. Article preview page length is **not** a coverage/acceptance criterion.
- `figures/`: 6 activity-driven scientific figures. Historical I/II **floating-point reconstructions are NUMERIC_ONLY**, not plots of the analytically certified alternative high-resource witnesses. Construction III has two internally independent interval algorithms; this is not third-party formal verification.
- `../../research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv`: full 43 original IDs; current authoring classification **35 drafted / 2 partial / 6 partial-open / 0 undrafted**. Classification describes prose coverage and proof-draft status, **not 35 externally certified statements**.
- `../../research/v20-gate3/GATE3_ROUND2_MATH_REVIEW_ZH.md`: historic round-two math review; `GATE3_GENERAL_P_FIXED_RESOURCE_PROOF_AUDIT_ZH.md`: subsequent round-three fixed-`p` uniform-resource proof audit. The latter supersedes the former where the prior report called general-p closure OPEN.

## New general-p theorem (round 3)

For **each fixed** `p in [0,1)`, the paper proves at research-manuscript standard that one finite event horizon, positive smoothing width, gross paired-dollar turnover ceiling, and per-asset *true gross seller-share* inventory ceiling suffice for all arbitrarily severe nine-target terminal drawdowns in `C0` while closing every dollar ledger. The proof treats sharp positive role weights, compensator endpoint signs, exact cut Jacobian, `q`-uniform moving-cut smoothing, graph completion, and integrability at the terminal low-price ramp. **Quantifiers:** constants may depend on fixed `p`; not uniform for `p` approaching 1 and not a bounded pointwise gross-share-rate theorem. This is an internal analytical manuscript proof, not external referee acceptance; the p=0 fixed numeric constants are not transferred to general p. No legacy low-turnover floating-point roots are promoted to rigorous witnesses.

## Reference/build provenance

- Scholarly reference master is the unchanged 33-entry `../v16-three-certified-constructions/references.bib` (GitHub blob `f5ebe530c08ce5d12a89b227a1677c440a07c1c6`).
- The downloadable 28-page PDF is an *article-class local-preview build*. It uses a temporary 9-entry `.bbl` file for offline display because this local runtime does not contain the traditional BibTeX executable. It is **not** a final SIAM manuscript or reference audit. GitHub `audit_bibliography.py --strict-original` checks the master 33-entry corpus; it does not replace a complete independent SIAM build.
- Run `python research/v20-gate3/check_gate3_draft.py` from repository or elsewhere to check all 43 IDs, paths, figure count and evidence markers. Other algebra checks (`audit_new_math.py`) are exact rational regressions, not theorem verification.

## Remaining Gate 3 acceptance obligations

1. Independently review all 43 statements and sources, especially `P02`, `T03`, `T05`, `P10`, `R01–R03`, and the general-p cut continuation. Do not turn open problems into unjustified theorems. The original 15 high-risk IDs remain traceable even where subclaims have now been proved.
2. Audit the full SIAM-class build, bibliography and all 6 figures, equations, page-level line wraps and mathematical claims against the original 40 pages and V16. Reconcile any discrepancy in the working article preview.
3. Retain the difference between deterministic reachability and real-world crisis probability, internally verified intervals vs external formal verification, necessary bounds vs sufficient paths, and numerical reconstructions vs rigorous analytic witnesses.
4. Only after a written Gate 3 acceptance decision should the project move to Gate 4's paragraph/formula aligned Chinese version and two fully editable/annotatable Word deliverables.

**No new release or DOI is authorized by this working draft.**
## Genuine SIAM + original V16 BibTeX build (new CI guard)

The original SIAM workflow builds the historic paper; it does not validate this V20 draft. Use `python research/v20-gate3/build_siam_v20.py` (with `pdflatex` and `bibtex` installed) to build this source against the pinned complete SIAM template and **the original 33-item V16 bibliography**. The new `v20-gate3-siam.yml` workflow executes that build, requires resolved references and no overfull boxes, and uploads the actual PDF, .bbl, .log and hash-bearing JSON report. This is a research build checkpoint, **not Gate 3 acceptance**. The temporary nine-entry reference list previously used for local display is not the scholarly bibliography.

## Scientific literature identity and citation coverage (2026-11-06)

After a source-by-source comparison against the preserved V16 manuscript, the current V20 English text now cites **16 distinct keys**, preserving all **15** keys explicitly cited in V16. The original 33-entry BibTeX master is preserved byte-for-byte and validated by its exact SHA-256, not just reference count. The full crosswalk is `../../research/v20-gate3/V20_REFERENCE_CROSSWALK_2026-11-06.md`. Bibliography records not cited remain in the source master; publication output should not artificially list unused sources.

This revision also separates financial-market mechanisms (strategic order flow, supply curves and optimal execution) from this paper's deterministic activity-driven reachability, and explicitly distinguishes the hypothetical repeated 25% research band from real exchange price-limit rules.
