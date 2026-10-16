# Direct Lean formalization route — 16 original numbered results

**Objective:** prove the exact 16 numbered statements in `paper/main.tex`, with *minimum* extra mathematical abstraction. This supersedes the earlier strategy of solving the unrestricted countably atomic BV completed-graph problem before attempting 3.1/3.2.

## Scope discipline

1. The **paper**, not an expanded mathematical model, is authoritative. M5 specifies piecewise-continuous finite-execution-variation paths with finitely many flow-completed instantaneous pulses. Do not demand a separate theorem for infinitely many atoms as a prerequisite. Do not quietly replace a continuous finite-variation piece by an absolutely-continuous piece; when needed, reuse `ContinuousWeakBVPriceSegment` and explicitly prove the primitive M2-to-weak-normal-form connection.
2. Start from the existing audited Lean declarations. Avoid introducing a new engine/framework, full general-completed-graph existence, or ad hoc extra hypotheses just to make a theorem pass.
3. **Measure delivery by 16 paper results with matching hypotheses**, not number of auxiliary lemmas. A theorem that assumes the key original physical price law as a new independent fact is only a restricted/conditional result.
4. Only one canonical top-level Lean theorem per paper numbered result; add private/local helpers only when their proof is necessary. Reuse Mathlib FTC, convexity, integration, order-statistic, ODE comparison, interval and sum lemmas.
5. Every delivered commit must have full same-SHA CI PASS (Lean build, complete axiom audit, hashes, other required workflows). Draft PR until exact-source scope audit.

## Immediate minimal bridge for 3.1/3.2

Paper M2 + M3 + M4 imply on each continuous finite-variation execution piece

`Φ(S_i(t)) - Φ(S_i(a)) = Σ_e B_ie (Z_e(t)-Z_e(a)) - ρ ∫_a^t [S_i(S_i-F)/g(S_i)] du`.

This is exactly `ContinuousWeakBVPriceSegment.weak_physical_price_response`; do **not** assume it is a consequence of a generic BV path without proving the correct nonlinear Stieltjes/chain rule. At an instantaneous pulse, use the existing physically verified `FlowCompletedPulse.coordinate_endpoint`. For finitely many pieces, use the existing `RadiallyElasticWeakBVPriceReachable` induction; check that its price-only projection of M1–M5 is genuinely implied by all paper controls, preserving original positivity and admissibility (and the paper's attained-price elasticity condition).

Then **re-use**, do not re-prove:
- `ContinuousWeakBVPriceSegment.potential_nonnegative_of_visited_elasticity`;
- `RadiallyElasticWeakBVPriceReachable.no_all_asset_decline`;
- `RadiallyElasticWeakBVPriceReachable.no_systemic_crisis_at_breadth`;
- `positive_full_coverage_crisis_forces_all_below`.

No requirement for a universal countably-infinite atomic execution representation, a generic a.e.-FTC route, or arbitrary positive finite-prefix approximation. Those extensions are optional follow-up research rather than gates to the original 3.1/3.2.

## Remaining paper-result closure order

| Paper result | Minimal proof ingredient; reuse before creating helpers |
|---|---|
| 3.1 / 3.2 | Above M2 continuous-BV chain rule + finite physical pulse joining; inherited radial elasticity and exact coverage statistic |
| 7.1 | Finite-dimensional log-product and kth-largest loss identity, using existing `CrisisQuantile` |
| 7.5 | Subset sum of incidence columns; integrate elementary cut-capacity inequality |
| 6.1 / 7.2 | Scalar linear-ODE comparison, closed-form rate and price-band bounds |
| 5.1 / 7.4 | Direct monotone coordinate integral/resource bounds from the original accounting identity |
| 7.3 | Second-session maximum-price and sign of recovery; paired-dollar conservation |
| 6.2 | Constant-g bounded-rate price law, aggregate cancellation, Taylor/elementary exponential inequality |
| 4.2 / 4.3 | Explicit two-/three-pulse constructions, second-order Taylor remainder, exact ledger closure and inventory |
| 6.3 | Explicit continuous bounded-rate example with nonnegative shares, dollar closure and strict positive loss |
| 4.4 | Sharp threshold: universal bound **and** feasible approaching sequence, including non-attainment |
| 4.1 | Assemble p=2/1/0 from proved components; prove finite caps and parameter uniformity in C |
| 7.6 | Independently check the existing strict rational interval certificate via a small verified checker or Lean computation, *not* floating-point assertions |

This is an **implementation order**, not a completion claim. Never add a theorem whose statement is a disguised rephrasing of the desired conclusion. Preserve original theorem quantifiers, all resource constraints and paper version.
