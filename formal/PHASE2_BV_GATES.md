# Phase 2 — BV market fidelity and crisis semantics

**Paper:** English V12 Final, Assumption M1–M5, Theorems 3.1–3.2.  
**Tracking:** [Issue #5](https://github.com/Siyuan-chat/market-crash-reachability/issues/5), [PR #7](https://github.com/Siyuan-chat/market-crash-reachability/pull/7).  
**Accepted on main:** 76 declarations, including the regular physical-market barriers.  
**New branch:** 87 declarations checked with Lean 4.19.0 and pinned Mathlib in [Actions #38846420795](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38846420795). No complete all-BV market theorem is asserted.

## Progress

`BoundedVariationLedger.lean` introduces monotone, finite-variation, cumulative dollar executions for a directed paired-dollar network. This model need not have a classical derivative. The proven lemmas cover nonnegative executed-dollar increments, the zero ledger at the start, total signed-dollar conservation at any time, and exact per-asset ledger differences.

Crucially, **aggregate zero-sum is weaker than terminal per-asset closure** \(\forall i,\ X_i(T)=0\). The latter remains a separate requirement, just as in M5. This module is ledger accounting only; it does not yet infer physical price movements from BV controls.

`CrisisParameters.lean` proves \(1\le\lceil\alpha N\rceil\le N\) for \(0<\alpha\le1\); identifies the actual log loss with minus the benchmark log-price coordinate; reconstructs strictly positive actual prices from that coordinate; and identifies the average of the actual losses with the existing `meanLogLoss`. It instantiates the already checked **regular-path** Theorem 3.2 analogue with the actual price-derived log vector and valid breadth count.

The equivalence of the supremum-defined coverage quantile with the exact kth-largest loss for every valid k still needs a separate proof.

## Real remaining gap: full BV price dynamics

A cumulative finite-variation control can include absolutely continuous, singular-continuous and jump components. Proving a pointwise ODE only on almost every physical time does **not** handle a singular-continuous trading component.

| Original M1–M5 element | Required formal step | Current status |
| --- | --- | --- |
| Cumulative paired-dollar transactions | BV edge flow and exact incidence-ledger algebra | New Lean proofs checked |
| Physical marginal-price settlement | Stieltjes/measure-driven price and share response | Not yet Lean-proved for general BV |
| No-news price resilience | Recovering drift and BV chain rule for \(\Phi(S)\) | Only finite smooth-segment proof checked |
| Flow-completed ordered jumps | Price positivity and physical-time-held-fixed marginal execution | Regular pulse FTC proved; wider endpoint regularity remains |
| General potential invariant | \(H=\sum_i\Phi(S_i)\ge0\) on the full BV class | Proved only for finite regular physical paths |
| Elasticity on attainable price range | Localize concavity/tangent/Jensen without assuming every positive price | Pending |
| Complete crisis definition | \(\alpha\) ceiling, actual log loss, exact coverage quantile | Ceiling and log identity checked; coverage quantile equivalence pending |

## Non-negotiable acceptance criteria

1. Give the **actual** weak/Stieltjes/measure solution semantics of each continuous BV path and the actual Marcus/flow-completed rule for each jump, without assuming the desired coordinate invariant.
2. Prove the chain rule from the physical price-and-share equation, including the singular-continuous part, then derive the potential comparison for arbitrary admissible time windows.
3. Restrict elasticity to attainable prices or the rigorously established reachable interval. Do not silently strengthen the manuscript hypothesis.
4. Prove that the finite-index coverage quantile agrees with the kth-largest loss and that \(k=\lceil\alpha N\rceil\), as well as the terminal log-price representation.
5. Only then claim full Theorems 3.1 and 3.2 are kernel-checked for all M1–M5 admissible paths. Keep all other numbered results and the external Proposition 7.6 interval certificate separate.

A clean `lake build` and axiom audit apply only to the precise typed declarations committed on the tested Git SHA. They do not certify an unformalized equivalence between the regular path model and the full original manuscript model.
