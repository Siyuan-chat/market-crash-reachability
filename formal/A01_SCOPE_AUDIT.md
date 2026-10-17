# A01: Proposition 7.5 scope audit (2026-10-17)

Source: `paper/main.tex:626–659`. The user expressly authorized only the
nonempty-J / zero-capacity boundary correction after the empty-J counterexample
was identified: for empty J every descent premise is vacuous but K=0, not K>0.
The complement-empty impossibility remains a separate conclusion. The m>0
specialization now states its denominator domain. These three clarifications
are mirrored in both translations. `docs/PHASE2_BASELINE.json` retains the
historical publication identity and original source digest alongside the
authorized amended source digest; historical PDFs are not represented as
newly rendered amended editions.

## Source-to-kernel correspondence

| Manuscript clause | Canonical Lean theorem / derivation |
| --- | --- |
| Every finite asset subset, a.e. genuine ledger derivative | `proposition_7_5_ledger_derivative_bound`; uses `ACPhysicalSession.ledger_derivative` and `cut_rate_ae` |
| Physical marginal settlement and asset-specific response | `ACPhysicalSession` has asset-specific F, rho, Response, original level-price integral equation and a.e. price ODE; edge-dollar primitives and derivatives encode actual directed execution |
| Integrate Phi'(S)=S/g(S) | `ACPhysicalSession.coordinate_derivative`, `coordinate_lipschitz`, `coordinate_endpoint`; coordinate endpoint identity is a theorem, not a structure field |
| General AC paths under gross-rate cap | `physical_primitive` is the integrable-primitive formulation of the original AC level-price equation, not a smooth subclass. `prices_lipschitz` derives bounded-rate Lipschitz regularity from this equation, compactness and the cap; it does not assume price smoothness |
| Unconditional endpoint FTC for those paths | `lipschitzOn_integral_eq_sub_of_hasDerivAt_ae`, from Stieltjes measure absolute continuity, Radon–Nikodym differentiation and measure integration. No FTC endpoint hypothesis or everywhere differentiability |
| K strictly positive for nonempty J with strict endpoint descent | `ACPhysicalSession.cutRequirement_positive`, strict coordinate monotonicity for each positive endpoint |
| Below-benchmark recovery has nonpositive integral; net received dollars in complement at least K | `ACPhysicalSession.cut_funding`, derived physical endpoint law plus exact incidence cancellation |
| Paired turnover counted once | `ACPhysicalSession.turnover` integrates sum of directed edge rates once; `cut_turnover_bound` proves net inflow ≤ turnover using cut incidence coefficient ≤1 |
| Complement upper capacity and required v | `cut_capacity_bound` integrates a.e. gross capacity; `proposition_7_5_market_cut` derives positive denominator from positive session duration, positive prices and nonempty receiving side |
| Empty complement impossible | `proposition_7_5_empty_complement`; zero net complement flow contradicts strict positive K |
| Constant-impact coordinate difference | `constant_coordinate_session_difference`, from the verified coordinate integral, not an assumed quadratic coordinate |
| Rolling upper band evolved from F | `rolling_upper_reference_bound_finite` derives it from actual finite reference recursion; no constraints on future sessions |
| k/m specialization, d≥2 | `proposition_7_5_rolling_constant_impact` derives K and actual complement-cardinality capacity from the physical session, then applies `market_cut_constant_impact_specialization` |

The price-only session projection drops no-shorting, finite initial holdings,
and terminal closure because this necessary bound holds on a larger class.
None of these conditions is used to infer existence or feasibility. The
original AC paths, with their original physical integral equations and edge
ledgers, satisfy the projection's conditions. Singular-continuous BV paths
and pulses are outside this proposition's explicit AC scope; the general BV
bridge B01 is not claimed here.

The strict-result family covers arbitrary finite asset types and arbitrary
finite directed networks. It permits nonnegative asset-specific resilience,
a superset of the original positive-resilience assumptions, and continuous
positive responses, a superset of the original response regularity. The
instantaneous theorem also covers empty J, where its two sides are zero.

## Verification and acceptance

Local fixed toolchain: Lean 4.19.0; Mathlib
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. Targeted compilation and full
project build passed. Main agent inspected the proofs; an independent
read-only scope review found no missing formula, sign error or strengthened
economic hypothesis. Full axiom audit, release hashes and same-SHA CI are
separate acceptance gates, recorded in `WHOLE_PAPER_LEAN_COMPLETION.md`.
This document is scope evidence, not a competing task-status ledger.

Acceptance: PAPER_ACCEPTED at proof commit `772d72d6c3b819814ce39a165a1bb56ad6729ee6`. All four same-SHA workflows succeeded: [lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704394)；[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704369)；[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704465)；[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704392)。Local full build, 228-declaration permitted-axiom audit and 226-entry release hash check passed. This exact proof revision is the second accepted numbered result.
