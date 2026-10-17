# M1–M5 formal-model fidelity audit

## Current original-model bridge (2026-10-17)

The current implementation supersedes the restricted-class gaps described in
the historical audit below. `PhysicalContinuousBVPiece` encodes physical
price/share Stieltjes primitives and the paired dollar ledger, with continuous
finite execution variation including singular continuous controls.
`PhysicalBVNormalForm` derives the nonlinear Phi equation from those primitives;
`PhysicalBVProjection` constructs the actual Lipschitz operational price, share
and ledger process. The inverse variation clock, measure change of variables,
derived physical ODE and Lipschitz FTC are proved, rather than input fields.
The physical-time recovery extension is constructed by interval projection.

`OriginalFlowCompletedPulse` uses integral physical dynamics on [0,1], without
the older pulse type's endpoint two-sided differentiability. Its coordinate and
dollar laws hold at every internal parameter. `OriginalPhysicalReachable` joins
the full time/price/share/cash state through finitely many continuous pieces and
pulses. The admissible path records no short sales, finite share variation and
terminal per-asset dollar closure. `OriginalVisitedPrices` proves actual-path
radial attainment and observations at every physical time. Elasticity conditions
are confined to this path's attained prices.

Theorem 3.1's original candidate is compiled in `OriginalBarrier`; full audit,
release hashes and exact-SHA CI acceptance remain pending. The bridge itself is
not a numbered result. No countably atomic framework is required or added.

## Historical regular-subclass audit

**Research baseline:** English V12 Final, \`paper/main.tex\`, M1–M5 and Theorems 3.1/3.2.  
**Verified source:** \`PhysicalSmoothMarket.lean\`, \`PhysicalPulse.lean\`, \`AdmissibleMarketPath.lean\`, \`AdmissiblePathBarrier.lean\`.  
**Evidence:** [GitHub Actions Lean #38844596170](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38844596170): \`PASS: 76 theorems audited; no unfinished proofs or extra axioms\`.

## What is encoded

| Manuscript assumption | Lean physical regular-subclass representation | Boundary |
| --- | --- | --- |
| M1 Positive prices, F benchmark | Smooth positive prices at all times, pulse positive prices for every internal execution parameter; initial state prices F | Stronger smooth/endpoint regularity |
| M2 Marginal settlement | Price, share and dollar-ledger differential equations use the same matched-dollar execution; pulse-coordinate and ledger endpoints **derived by FTC** | Full BV Stieltjes/flow-completed equivalence pending |
| M3 Fixed fundamentals, resilience | Fixed F, rho; original physical price ODE with recovery term | Need general piecewise BV execution |
| M4 Paired-dollar network | Incidence columns cancel, nonnegative edge rates, single directed-edge pulses | Full bidirectional graph instantiation/equivalence pending |
| M5 Bounded execution, no short, closure | Finite share variation per step, nonnegative shares, finite concatenation matching all price/holdings/ledger/time fields, zero initial and terminal per-asset dollar ledgers | Full original finite-variation path inclusion pending |

## Three proved links for the finite regular subclass

1. **Model:** \`PhysicalSmoothSegment.coordinate_ode\` derives the generalized dynamics from physical price/share equations; \`FlowCompletedPulse.coordinate_hasDerivAt\` derives the transformed pulse ODE.
2. **Invariant:** \`PhysicalSmoothSegment.potential_nonnegative\` handles smooth segments; \`FlowCompletedPulse.coordinate_endpoint\` and \`ledger_endpoint\` derive pulse endpoints using FTC; \`physical_step_preserves_potential\`, \`physical_reachable_preserves_potential\` and \`AdmissibleMarketPath.potential_nonnegative\` establish H ≥ 0 across a finite path.
3. **Exclusion:** \`admissible_regular_no_all_asset_decline\` and \`admissible_regular_no_systemic_crisis\` prove the analogues of Theorems 3.1/3.2 for this typed **regular subclass**. These are genuine kernel-checked theorems, but **not the original whole-paper quantifiers**.

## Remaining gates before marking original 3.1/3.2 complete

- Smooth segments currently require \`HasDerivAt\` everywhere on ℝ; pulses require a derivative even at internal-parameter endpoints. M5 allows a broader piecewise-continuous, finite-variation class. Extend to intervals, absolutely continuous / BV executions, or prove a faithful reduction covering every paper-admissible path.
- Current elasticity-to-concavity lemmas assume bounds at **all positive prices**; the paper requires the condition only on reachable prices. Prove the restricted-domain argument rather than silently strengthening the theorem.
- Connect \`k=⌈αN⌉\` for \`0<α≤1\`, coverage order-statistic and actual log prices to \`systemicCrisis q k\`. The present 3.2-style proof needs only the mean-loss bound and therefore does not establish all quantile semantics.
- Confirm nontrivial admissible examples and total variation/chronological bookkeeping for the complete M1–M5 class.

The manuscript, certificates and numerical verification algorithms have not been changed. The strict interval certificate in Proposition 7.6 is **not** checked by Lean.
