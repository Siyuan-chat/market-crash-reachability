# C04: Theorem 6.2 original-scope audit

Source: paper/main.tex, thm:quadratic-rate. Canonical theorem:
`theorem_6_2_original`; unrestricted-network upper branch:
`theorem_6_2_original_upper`.

| Original obligation | Proof correspondence |
|---|---|
| Every finite N >= 2 and every valid breadth | The combined theorem quantifies N and alpha; the upper theorem even proves the mean bound for every natural quantile index. |
| Actual paired dollars, before-net gross share cap | The upper branch accepts any finite paired network and actual ACPhysicalSession, not only the complete graph. It uses its actual physical primitive and derives the signed-share bound from before-net gross capacity. |
| With or without terminal closure | The entire upper branch has no closure, inventory, or price-band hypothesis. |
| Exact coefficient under b_T < 1 | Variation-of-constants comparison bounds individual prices; pairing gives the true aggregate forcing. An integral comparison proves d_T-rho*T*exp(-rho*T). A proved logarithmic Taylor inequality supplies exactly d_T^2/(2*(1-b_T)^2). No coefficient is postulated. |
| O(v^2) and attained positive Omega(v^2) | A uniform small-rate upper coefficient is proved. The fixed C03 family chooses constants before amplitude; scaling a=v/C gives actual positive c*v^2 severity for every sufficiently small v. |
| Fixed N,T, bands, positive inventory | The attained family fixes these parameters and arbitrary positive H before varying v. It has the same actual execution for cap, inventory, terminal closure and admissible band via RealizesACSession. |
| Minimum required cap Theta(sqrt(delta)) | minimumOriginalRate is the sInf of caps for actual admissible executions. For every small positive delta the set is proved nonempty. The upper bound uses an actual family witness; the lower bound holds for every feasible cap, including large caps outside b_T<1, using the explicit quadratic necessary bound. Both constants are positive and independent of delta. |
| No exact optimizer asserted | The statement bounds the genuine infimum and proves feasibility; it does not claim an optimizing control or exact constant. |

The feasible-path predicate exposes prices, times, parameters, holdings,
all visited prices, terminal cash closure, and the physical realization of
the same AC execution. The infimum is never used without nonemptiness and
a proved lower bound. No additional regularity assumption on an arbitrary
upper-bound path is introduced.

Status: LEAN_PASS, pending exact proof-SHA four-CI. Full pinned Lean 4.19.0
integration build PASS (formal/lean/build/formal/c04-full-build/result.json,
stdout SHA-256 aa0fa561f2c7fcd03e6a4782537258f94bdf07a656316d62ba0d2bd3915208a8).
All 615 registered declarations pass the complete permitted-axiom audit:
build/formal/c04-integrity/result.json, stdout SHA-256
506b6407d2a4d235dc04da469b28c42a0534263a56530b125af2c78938797081.
Only propext, Classical.choice and Quot.sound occur. Release hashes cover
272 artifacts. Independent original-quantifier review found no omission.
The real-valued sInf definition is used only after nonemptiness is proved;
it is not claimed to assign +infinity to an empty feasible set.
Not yet paper-accepted.
