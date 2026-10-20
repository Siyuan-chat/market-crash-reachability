> Historical technical record. Applies to its named source revision; see [current versions](../docs/VERSIONS.md) and the current evidence matrix. Retained at this path for provenance and compatibility.

# Direct Lean formalization route — 16 original numbered results

Historical route, 16 October 2026: the exact 16 numbered statements in `paper/main.tex` were the target. The route replaced the earlier proposed prerequisite of solving the unrestricted countably atomic BV completed-graph problem before 3.1/3.2. Final acceptance evidence is in [the completion matrix](WHOLE_PAPER_LEAN_COMPLETION.md).

## Mathematical scope

M5 specifies piecewise-continuous finite-execution-variation paths with finitely many flow-completed instantaneous pulses. A theorem for infinitely many atoms is therefore not a prerequisite. Continuous finite variation is broader than absolute continuity; the primitive M2-to-weak-normal-form connection is a separate proof obligation, represented by `ContinuousWeakBVPriceSegment`.

Coverage concerns the 16 paper results with matching hypotheses, rather than auxiliary-lemma counts. A theorem assuming the original physical price law as an independent extra fact has only restricted or conditional scope. Exact-source scope audits, kernel builds and individual axiom audits supply the acceptance evidence linked in the completion matrix.

## Historical bridge for 3.1/3.2

Paper M2 + M3 + M4 imply on each continuous finite-variation execution piece

`Φ(S_i(t)) - Φ(S_i(a)) = Σ_e B_ie (Z_e(t)-Z_e(a)) - ρ ∫_a^t [S_i(S_i-F)/g(S_i)] du`.

This is `ContinuousWeakBVPriceSegment.weak_physical_price_response`. Its derivation from a generic BV path requires the nonlinear Stieltjes/chain rule. At an instantaneous pulse, `FlowCompletedPulse.coordinate_endpoint` supplies the physical endpoint identity. For finitely many pieces, the `RadiallyElasticWeakBVPriceReachable` induction requires the price-only projection to follow from M1–M5 controls, preserving positivity, admissibility and attained-price elasticity.

Related audited ingredients at this checkpoint were:
- `ContinuousWeakBVPriceSegment.potential_nonnegative_of_visited_elasticity`;
- `RadiallyElasticWeakBVPriceReachable.no_all_asset_decline`;
- `RadiallyElasticWeakBVPriceReachable.no_systemic_crisis_at_breadth`;
- `positive_full_coverage_crisis_forces_all_below`.

No requirement for a universal countably-infinite atomic execution representation, a generic a.e.-FTC route, or arbitrary positive finite-prefix approximation. Those extensions are optional follow-up research rather than gates to the original 3.1/3.2.

## Historical paper-result dependency outline

| Paper result | Proof ingredient |
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

This outline records dependencies, not completion evidence. Original quantifiers, resource constraints and source versions determine each result's scope; the completion matrix records final acceptance.
