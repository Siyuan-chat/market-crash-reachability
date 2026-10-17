# A03: Proposition 7.2 scope audit (2026-10-17)

Source: `paper/main.tex:551–575`. No manuscript changes.
Canonical proof family in `MarketCrash/RollingRate.lean`:

| Original clause | Physical proof |
| --- | --- |
| A session beginning at any s>0 requires the exact positive-part rate lower bound | `proposition_7_2_single_session` takes an actual physical session with arbitrary a, b and initial price, derives variation-of-constants comparison by the already proved a.e. integrating-factor/FTC argument, then rearranges with positive rho, eta and session duration |
| Fixed constant per-share impact | Impact equals eta at all actually visited prices; this is weaker than global g≡eta, and suffices for the physical response law |
| D equal-duration lower-limit sessions, starts F q^(d−1) | `proposition_7_2_rolling_streak` uses an actual finite family of physical sessions d∈{1,…,D}. The conclusion is exactly rho F/eta times the finite maximum, represented as `Finset.sup'`. No assumptions on future sessions |
| No terminal matching/closure sufficiency claim | The single-asset inequalities are necessary and are derived on actual paired physical sessions; no existence, optimality or sufficiency is asserted |
| Perpetual rate-only floor, independent of session count | `ACPhysicalSession.perpetual_rate_floor_at` covers every t in an arbitrary finite horizon beginning at F, without assuming eta v<rho F |
| Integer D upper bound only when eta v<rho F | `proposition_7_2_perpetual_and_integer` combines the actual endpoint floor with terminal price ≤F q^D and `rollingRate_integer_streak_bound`, proving positivity of the logarithm argument and reversing division by log q<0 correctly |

The comparison allows arbitrary real initial s; for the actual session s>0
follows from its positive prices. The physical benchmark is positive by
construction. D is natural (not relaxed to a real streak variable), and the
maximum branch explicitly requires D≥1. The perpetual branch allows D=0.
The integer branch requires 0<q<1 and uses the strict cap condition only for
the finite log bound. The single-session conclusion is proved for an endpoint
at or below its lower limit, a larger class than equality at that limit.

All price derivatives are required only almost everywhere. Bounded-rate
Lipschitz prices and the endpoint FTC are derived by the A01/A02 physical
integral machinery; no smooth-only or assumed-FTC replacement is used.
Original controls with their original inventories, price bands and terminal
cash conditions are included in the larger class used for these necessary
scalar inequalities. The reset-session terminology does not replace the
unchanged fundamental benchmark F by each preceding close.

Main agent read all source proofs and checked the three manuscript formulas,
positive part, maximum, integer quantifier and logarithm sign. Acceptance
requires the separate full project/audit/hash/same-SHA CI gates in the single
authoritative completion matrix.

Local validation: full pinned Lean 4.19.0 project build PASS; 256-declaration permitted-axiom audit PASS; 230 release SHA-256 entries PASS. Independent source scope review found no omitted quantifier, band/closure strengthening, future-session restriction or formula/sign error. A03 Proposition 7.2 PAPER_ACCEPTED，证明 SHA `5c84995094b736c0231df6d804c8daad638bbfc7`；本地全量构建、256项公理审计、230项发布哈希 PASS；四项同 SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011779671)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011779650)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011781951)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011779633)。
