# B05: Proposition 7.4 original-scope audit

Source: `paper/main.tex`, `prop:streak-precondition`. Candidate canonical
`MarketCrash.proposition_7_4_original` in `OriginalPreconditioningWorking.lean`.

The first actual finite physical trace represents session one; a second trace
represents all later sessions. Their full economic boundary state is shared.
The traces admit continuous singular-BV execution and finite original pulses.
The conclusion needs only the chosen asset's initial benchmark and closed
dollar ledger, a weaker premise than original per-asset terminal closure.

| Original clause | Candidate derivation |
| --- | --- |
| Exact closed-ledger recovery integral | Each raw continuous piece uses the derived physical normal form. Each pulse has zero physical-time recovery and its coordinate increment equals its actual ledger increment. Finite trace induction telescopes, yielding rho times the actual dt recovery integral = integral from final price to F of u/g(u). |
| Strict positivity and above-F physical-time measure | Strictly lower positive final price makes that integral positive. If actual above-F physical times had zero volume, the recovery integral would be nonpositive. The defined excursion measure is proved equal to volume of the union of chronological physical-time excursion sets; no operational or pulse-parameter duration is counted. |
| First-session-only upper-band budget | All later visited prices≤F make their recovery contributions nonpositive. The first trace has its actual elapsed physical duration tau_1 and all visited prices≤U_1. `recoveryCeiling_properties` constructs and attains the continuous integrand's maximum on [F,U_1]. Below-F contributions are nonpositive, hence the full bound is rho*tau_1 times that actual maximum. |
| Constant eta and rolling terminal F q^D | Integrating the quadratic coordinate yields the manuscript's exact necessary rho*tau_1 bound, with arbitrary natural D, eta>0, beta_+>0 and 0<q<1. |
| Integer streak bound | Under 2H_+<1, positivity of 1−2H_+ and log q<0 are checked before dividing. The conclusion is the original D≤log(1−2H_+)/(2 log q), with D natural. |

The recovery normal form is proved, not a premise. No above-F time is inferred
from an isolated pulse; fixed-time pulses contribute no dt measure. No
sufficiency, rate cap, global curvature, or reset of the benchmark is assumed.

Status: full formal-module Lean 4.19.0 build PASS; complete 433-declaration permitted-axiom audit PASS; 253 release SHA-256 entries PASS. B05 Proposition 7.4 PAPER_ACCEPTED；证明 SHA `131256911c0d21ff837a477cc63c8241ebcb27c7`；本地全量构建、433项公理审计和253项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405730)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405801)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405755)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405739)。
