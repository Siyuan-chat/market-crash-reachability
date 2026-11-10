# Gate 3, 2026-11-10 — two analytic boundary improvements and evidence scope

**Status:** internally derived and independently cross-checked analytical arguments; no external peer review or theorem-by-theorem Lean certification. The source manuscript is `submission/v20-gate3-activity-recovery/main.tex`.

## 1. Reachability strictly above the two-asset p=3/2 index

The previous scalar reversal proof for every fixed K>0 at p=3/2 produces some **finite** dollar amount z_K with strict endpoint x1(2z_K)*x2(2z_K)<1 and a price path bounded below by a positive path-dependent constant. On any closed positive-price strip around that path, the buyer and seller vector fields f_±(x;p)=±x^(p−1)−K(x−1) are smooth in both state and exponent p.

Classical ODE continuous dependence, applied to the **same two edge events of fixed amount z_K** with the same order and opposite signs, therefore yields epsilon(K)>0 such that for every p in [3/2,3/2+epsilon(K)) the terminal price product remains strictly below one. Price minima stay positive, and actual gross seller shares and gross share rates have uniform finite envelopes in this neighborhood. Executed-dollar ledgers close *exactly*, since event dollar amounts are unchanged.

**Deduction:** p=3/2 cannot be identified as the proven upper critical exponent of homogeneous two-node finite-dollar reachability. The true boundary for p above that local neighborhood, and any sharp minimum successful dollar budget, remain open. No explicit numerical epsilon is claimed; none was required to prove existence.

## 2. A positive necessary gross-share-speed bound in two rolling sessions

Consider the previously certified Construction III parameters p=0,K=2,F=eta=1, two sessions of length 20 and any asset closing at 3/4 then 9/16. At all positive prices,
`1+2x(x-1)=2(x-1/2)^2+1/2>0`.
The paired-dollar inequality |u_dot|<=a_dot and a_dot/x<=v imply
`x_dot >= -v[1+2x(x-1)]`.
For `phi(x)=atan(2x-1)`, the exact derivative
`phi'(x)=1/[1+2x(x-1)]` gives
`phi(x(40))-phi(x(20)) >= -20v`.
Therefore
`v >= [atan(1/2)-atan(1/8)]/20 > 0.0169`.

The strict decimal comparison has a **pure rational** certificate:
`atan(1/2)-atan(1/8) = integral_(1/8)^(1/2) 1/(1+t^2) dt`, and
`1/(1+t^2) >= 1-t^2+t^4-t^6` on that interval, giving
`integral >= 24890949/73400320 > 169/500`.
These fractions are independently checked by `audit_rolling_rate_bracket.py` and are not floating-point heuristics.

Construction III already provides a five-target C1 witness with maximum genuine gross share rate strictly below 0.133. For the infimum over the same model, duration, bands and endpoint target condition, with resources large enough to admit the existing witness, we therefore have:
`[atan(1/2)-atan(1/8)]/20 <= v*5 < 0.133`.
This **does not** prove sharpness or change the breadth range 5<=k*<=9. It is a necessary speed bound paired with a separate sufficient witness. The lower bound uses only one target's second-session endpoint and the paired-dollar/gross-rate inequality.

## Coverage and acceptance guard

- All 43 legacy IDs remain present.
- P02/T03 gain a nonempty K-dependent p>3/2 reachability subregion, but the full 3/2<p<2 classification remains open outside that subregion.
- R03 gains a strict lower speed bound under explicit fixed session settings; the optimum and maximum target breadth remain open.
- No new theorem or corollary is claimed as Lean formalized. Structural/theorem-number and exact rational test success is not itself proof of continuity or optimum.
- Gate 3 final acceptance requires a complete statement/hypothesis audit, original scope coverage, exact figure/table provenance, coherent discussion of genuinely open results and an authentic SIAM plus original bibliography build.

This report records the mathematical **premises and deductions**, not a Gate 3 clearance decision.
