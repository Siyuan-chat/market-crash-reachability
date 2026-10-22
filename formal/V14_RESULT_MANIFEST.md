# V14-R1 mathematical result → Lean verification manifest

**Manuscript:** [V14-R1 source](../submission/v14-turnover-dissipation/main.tex), identified by its versioned source commit in `submission/v14-turnover-dissipation/manuscript-build.json`. Stable LaTeX labels are authoritative; manuscript line numbers move during edits.

**Historical baseline:** The original 16 theorem/proposition families are tracked in [ORIGINAL_RESULT_MANIFEST.md](ORIGINAL_RESULT_MANIFEST.md) with the precise hypotheses, accepted proof SHAs and preserved certificate. This new track does **not** amend that acceptance or its immutable `release/SHA256SUMS`. The existing Lean aggregate and proof-integrity checks remain in place.

## Exactly what is proved

| Stable manuscript label | Paper claim | New Lean declaration / evidence | V14 scope status |
| --- | --- | --- | --- |
| `lem:one-sided-BV` | Restorative drift makes negative transformed terminal displacement no larger than true cumulative dollar/share negative variation on an admissible path | `MarketCrashV14.one_sided_BV_original_path` in [OneSidedBV.lean](v14/OneSidedBV.lean); derives both inequalities from the existing original physical finite-BV trace lemmas, including completed pulses | **Implemented; awaiting fixed-toolchain CI**. Counts true Jordan negative variations of each completed piece, summed over the chronological trace. |
| `thm:sublinear-severe` | For every fixed `0 ≤ p < 1`, fixed finite horizon/turnover/inventory bounds work for all loss thresholds `δ > 0` | [SublinearSevere.lean](v14/SublinearSevere.lean): only the exponent inequality and normalized paired-dollar algebraic identity | **PARTIAL**. The radial ODE, positive flow-completed pulses, all assetwise dollar ledgers, shared `T,M₀,H₀` independent of `δ`, and crisis threshold remain OPEN. |
| `prop:unbalanced-stability` | Recovery-weighted upper bound for arbitrary integrable unmatched dollar flow | No new Lean theorem yet | **OPEN** |
| `prop:heterogeneous-quadratic` | Heterogeneous quadratic impact and weighted-flow loss estimate | [Robustness.lean](v14/Robustness.lean) has weighted-flow decomposition and an instantaneous paired-but-weighted imbalance example only | **PARTIAL**; the recovery-weighted bound and actual terminal dollar-closed two-pulse counterexample are OPEN |
| `prop:turnover-dissipation` | Exact quadratic-potential identity and turnover/time-weighted upper bounds | No new Lean theorem yet | **OPEN** |
| `prop:loss-breadth-eight` | Existence of an 8/10 strictly feasible bounded execution with uniform rolling bands | Python rational outward interval checker [loss_breadth](../verification/loss_breadth/README.md), not a new Lean checker | **INTERVAL ONLY; Lean OPEN** |

**No percentage of the above should be advertised as “whole V14 Lean accepted”** until all six match their current paper statements, quantified assumptions and verification scope. In particular, finite-step algebraic lemmas must not be counted as a completed existence construction, and an internal Python interval result is not a Lean certificate.

## Implementation order and acceptance gates

1. **Preserve original 16**: keep the accepted dependency tree unchanged; retain historical proof and original certificate hashes; rerun the legacy `lake build` plus `python formal/check_proof_integrity.py` before accepting changes to the shared model. The earlier top-level import cleanup is not a deletion of theorem proofs.
2. **P0 — two new V14 proofs**: first close the one-sided variation theorem on the full original physical trace, then derive the complete generalized radial `0≤p<1` severe-construction theorem with a single set of budget constants per fixed model. Reuse existing `OriginalResources` and `SevereAssembly` only where their hypotheses actually match.
3. **P1 — remaining analytical results**: unmatched-flow stability, heterogeneous-impact weighted comparison plus explicit pulse counterexample, and quadratic turnover–dissipation. Each needs a source-faithful top-level Lean theorem, not just a sufficient conditional lemma.
4. **P2 — new certificate families**: verify the exact rational controls for `R80-10` first, followed by the relevant B1/B2 witnesses with their **different** turnover budgets. Either import independently trusted exact proof artifacts or prove the outward-rounding checker sound in Lean; numerical regressions alone are insufficient.

Every result is `PAPER_ACCEPTED` **only** when its exact Lean statement is mapped to the V14-R1 hypothesis/conclusion, the pinned kernel build passes, its own `#print axioms` returns only `propext`, `Classical.choice`, `Quot.sound`, and a passing exact-SHA workflow is recorded. This manifest must record that SHA at promotion; without it, an implemented source file is still **PENDING**. No custom axioms, `sorry` or `admit` are permitted.

## Independent V14 Lean lane

New proofs reside in `formal/v14/`, deliberately **outside** `formal/lean/MarketCrash/` so they cannot silently alter the historical 16-result theorem roster or invalidate the frozen original source hashes. They import and reuse the original model and certified lemmas.

```sh
cd formal/lean
lake exe cache get
lake build
cd ../..
python formal/check_proof_integrity.py
python formal/v14/check_integrity.py
```

The last command runs the V14 source guard, then elaborates every new proof file with pinned Lean/Mathlib and checks each theorem's axioms. `python formal/v14/check_integrity.py --static` is only a lexical and manuscript-label check and **never** claims a successful Lean proof.
