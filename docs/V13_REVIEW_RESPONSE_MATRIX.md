# V13 reviewer-response matrix (work scope)

Baseline: `submission/siam-language-revision/` at main commit `9616803c95985ac6eecd854338d0f9d35a9a27b0`.
Target: `submission/v13-review-response/` on `revision/v13-review-response`.
Historical V12 `paper/`, Lean `formal/`, numerical `verification/` and
`release/`, and published PDFs are frozen in this work package.

| Concern | Decision | Location | Scope / status |
|---|---|---|---|
| M1 Price versus volume resilience | Explicit joint-assumption scope; alternative drift formula | Secs 2,3,8 | Expository derivation; **no** alternate-model barrier theorem asserted |
| M1 Square-root law and elasticity | Distinguish cumulative metaorder impact from local price response | Secs 1,8 | Literature-supported discussion, not empirical inference |
| M2 Log singularity and finite resources | Explain constant-impact zero boundary and finite-depth abstraction | Secs 4,8 | Original proof and asymptotic claims preserved |
| M2 Depth and rate units | Define local dollar-impact scale and dimensionless turnover/inventory/rate | Sec 5 | Algebraic normalization; no ADV/real-book calibration |
| M3 Costs and counterparties | Interpret existing cost identity; derive witness potential-only lower bound | Sec 8 | Existing interval terminal bound reused; no newly certified dissipation value |
| M3 Global minimum cost | Define optimization problem | Sec 8 | Future work, **not solved** |
| M4 Weak real-world crash evidence | Clearly label path as specified feasibility witness; report arithmetic/geometric differences | Abstract, Secs 7,8 | Original certified values and qualification preserved |
| M5 Definition sensitivity | p=1 arithmetic conservation and distinction from geometric mean | Secs 2,8 | Direct algebraic consequence; weighted-target global classification deferred |
| M6 Heterogeneity | Explicit scope and differential-form obstacle for cross-impact | Sec 8 | Future work; no extension theorem claimed |
| TSE attribution / Section 7 scope | Recast as exchange-agnostic rolling price-band analysis; retain venue-specific details only as institutional contrast | Secs 6,7,8 | Narrative-only; synthetic 3%/25% certificate untouched |
| M7 Certificate and rate bracket | Preserve published interval certificate and distinguish rate bounds/optimization | Secs 7,8, availability | New 80,000-step audit and global rate optimum **not claimed** |
| Minor terminology and framing | Clean up discussion, bibliography, source/reproduction provenance | Secs 1,8,9 and docs | Remaining layout validation tracked separately |

## Provenance and acceptance gates

1. Run `python scripts/check_v13_revision.py`: assert exact identity of
   all numbered assumption/definition/theorem/proposition bodies with the
   18 October published English source, and validate bibliography coverage.
2. Run `python scripts/build_v13_revision.py`: BibTeX, repeated pdfLaTeX,
   no unresolved references/citations, no overfull boxes or missing glyphs.
3. Inspect all resulting rendered pages, floating tables, captions, and reference list.
4. Original 80,000-step certificate remains evidence from the V12 archive.
   A genuinely fresh rerun must be recorded separately before saying V13
   independently regenerated it.
5. The historical `manuscript.pdf` in the previous source directory is
   **not** the V13 PDF. Do not modify its SHA and claim it corresponds to V13.
6. Superseded on 18 October 2026: PR #11 is merged, and the author authorized
   the completed PDF review followed by publication. See
   [current validation/publication status](V13_VALIDATION_STATUS.md) and
   [all-page review](V13_PDF_REVIEW.md).

Not in scope: numerical optimal control for a tight rate bracket, calibrated
market-depth/ADV evidence, fully heterogeneous or matrix cross-impact theorems,
stochastic crisis probabilities, and a complete volume-restoration A/B/C theory.
