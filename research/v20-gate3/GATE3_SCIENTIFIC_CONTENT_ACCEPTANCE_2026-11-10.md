# V20 Gate 3 scientific-content acceptance (2026-11-10)

**Decision:** `GATE3_SCIENTIFIC_CONTENT_CLEARED_WITH_EXPLICIT_OPEN_RESEARCH_BOUNDARIES`

**Boundary:** This certifies the authoring/research-coverage gate specified by the V19 Handoff, **not** external refereeing, Lean formalization of the new model, a final camera-ready SIAM PDF, bilingual Word, release or DOI. Reproducible *final-edition* compilation and independent output comparison are Gate 4 responsibilities.

## I. Scientific-content contract checked

| Handoff obligation | Internal review result | Supporting artifact |
|---|---|---|
| Original 40-page PDF and GitHub V16 as full scientific coverage baseline, not the V17 12-page summary | PASS — all 43 original identifiers retained; no claim that the old physical-time model theorem automatically transfers | `research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv` and `research/v19-activity-recovery/GATE0_BASELINE_FREEZE_2026-11-05.md` |
| Unique new activity-driven equation, genuine nonnegative paired-dollar edge transactions, C0/C1, ordered flow-completed events | PASS — explicit assumptions and unchanged original monetary/true seller-share accounting | V20 `sec:model`, `prop:account` |
| Terminal crisis, alpha coverage, positivity, precise horizon vs rate constraints | PASS — clear model definition and positive-time reparameterization proof with rate-capped cases excluded | `def:crisis`, `prop:time-change`, `thm:ratequadratic` |
| Reachability and obstruction classification; do not silently delete global phase questions | PASS with OPEN high exponent sectors — exact p<=3/2 two-node finite C1 result plus a nonempty K-dependent interval above; price floors, aggregate barrier and genuine open phase sectors | `sec:twoasset`, `thm:floor`, `thm:aggregate`, `cor:nearcritical-beyond`, `sec:open-sharpness` |
| Execution resources, gross-share speed, nonnegative inventory, market cuts | PASS — positive analytic resource bounds, explicit small-rate conditions, pure-sale necessary test, cut capacities and a new two-day necessary speed bound | `thm:lower`, `thm:kresource`, `prop:rate-explicit`, `prop:cutcap`, `prop:two-day-rate-lower` |
| Three core ten-asset constructions with non-overstated evidence levels | PASS internal scoped mathematics — (I) analytic ten-halves alternative with explicit positive h; (II) fixed-p<1 uniform-resource nine-target analytic family; (III) five-target C1 internal dual-interval crosscheck. Legacy low-budget I/II witnesses stay NUMERIC_ONLY | `thm:tenhalf`, `thm:nine`, `thm:nine-general`, `thm:two`, `research/v19-activity-recovery/` |
| New-model robustness and heterogeneous response, with boundaries | PASS conditionally — precise compact-strip perturbation Gronwall, zero-integral closure conditions, exact weighted balance and two-node heterogeneous counterexample; global closed-loop robustness remains OPEN | `prop:unmatched`, `prop:hetero-weighted`, `prop:hetero-two` |
| All original appendix research responsibilities preserved in substantive proof sections | PASS in source coverage: original eight appendix obligations mapped to corresponding model-specific proofs/sections, not mechanically restored by identical appendix count | `research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv`, manuscript proof sections |
| Figures, original severity table function, bibliography integrity | PASS in scientific evidence labeling — six source PDF research figures; two tables explicitly separate analytic severity guarantees and numerical trial reconstructions; 33-entry original V16 BibTeX retained, 16 relevant keys cited | V20 figures, `tab:analytic-severity`, `tab:reconstruction`, pinned V16 bibliography |
| Independent reader can inspect each asserted theorem and locate its proof | PASS in manuscript structure — **33** theorem/proposition/lemma/corollary environments, each with a unique label and adjacent nonempty proof; the core analytical arguments and their quantified hypotheses have been reviewed, while numeric diagnostics explicitly do not substitute for proofs | `research/v20-gate3/GATE3_SCIENTIFIC_SOURCE_PROOF_REVIEW_2026-11-10.md`; `check_scientific_coverage.py` (structural only) |

## II. Exactly seven original questions retain mathematically open subproblems

A genuine open question is not treated as a proved theorem, nor deleted merely to claim a complete paper.

- `T03`, `P02`, `R02`: higher-exponent, multiasset and graph-dependent complete phase regions remain open. The strict p=3/2 finite C1 witness **continues into a nonempty K-dependent neighborhood above 3/2**; no global sharp critical exponent is asserted.
- `A04`: for p=0,N=10,K=4×10^-18, `log(2) <= delta_all*(K) <= log(10)/2`, but the sharp all-asset amplitude is unknown.
- `P10`, `R03`: repeated 25% lower-limit coverage is bounded by `5<=k*<=9`; the five-target gross-share-speed infimum satisfies `[atan(1/2)-atan(1/8)]/20 <= v*5 <0.133`. Neither maximum breadth nor sharp minimum rate is proved.
- `R01`: compact-strip unmatched dollar stability and heterogeneous response identities are proved under hypotheses; unrestricted global robustness is open.

These seven stay `partial` or `partial_open` in the **43-row research register**. Their manuscript treatment is substantive and bounded; no part of the abstract depends on asserting their unproved optimum/phase classification.

## III. Explicit separation from CI and Gate 4

- The **previous** V20 PR #70 source had seven successful GitHub workflows, including real SIAM/BibTeX build with the original bibliography and the Lean historical-proof integrity check.
- The **new** November 10 manuscript revision in PR #72 was merged at `aa89afb4e615f80f1760f3833753c52723e9be6b`. Its current full CI may still be queued or incomplete; **this document does NOT assert the new edition already passed the final PDF build**. Gate 4 must recheck the exact current source against the authentic SIAM class, BibTeX, PDF references, figures and page layout and retain hashed artifacts.
- Lean passing on prior commits verifies existing formal declarations, **not** the 33 new manuscript theorems as kernel-checked statements. The eight historical GitHub issues must not be silently closed by this Gate decision.
- No Chinese draft, English/Chinese editable .docx, archive/release, DOI registration or overwriting of V16/V17 is authorized by this acceptance.

## IV. Gate interpretation

The Handoff's Gate 3 is **complete research-question coverage and substantive English mathematical writing**; its Gate 4 separately specifies independent final PDF build, bilingual correspondence and Word review files. Under that division of responsibility, the English V20 science can be **internally accepted for Gate 3** with accurately disclosed still-open research questions. It would be mathematically false to say that all 43 research questions are solved, or that peer review/Lean has certified all results.

**Next gate:** independent final-build/formula and figure audit, then exact formula-matched full Chinese translation and two annotatable Word documents. Any later discovered mathematical error must reopen the affected result and Gate 3 acceptance, rather than being concealed to preserve a status label.
