# Partial Lean formalization — whole-paper project

Canonical mathematics: English V12 Final at commit
`e5339a47f29ccb669d1f228ca930a1c1146200bf`.

This project verifies coordinate, finite-dimensional conservation and response-family
foundations. It does **not** formalize the whole paper, the complete barrier
theorems, admissible controlled paths, or the interval certificate of Proposition 7.6.
Follow the [whole-paper proof tracker](https://github.com/Siyuan-chat/market-crash-reachability/issues/5).
Phase 2's [bounded-variation proof gates](PHASE2_BV_GATES.md) distinguish proven accounting and crisis-parameter bridges from the unproved full BV price dynamics.
See the [M1–M5 fidelity audit](MODEL_FIDELITY.md), [complete theorem map](THEOREM_MAP.md) and
[the precise status and hypotheses](FORMALIZATION_STATUS.md).

Install Lean through Elan. The toolchain file fixes Lean 4.19.0; the Lake
manifest fixes Mathlib and its transitive dependencies. From the repository root:

```bash
cd formal/lean
lake exe cache get
lake build
cd ../..
python formal/check_proof_integrity.py
```

The last command requires Python 3.11 and `lake` on PATH. It rejects unfinished
proofs or custom axioms and invokes Lean to inspect the axioms of every project
theorem. Expected foundational dependencies are `propext`, `Classical.choice`
and `Quot.sound`. Logs and a machine-readable inventory are generated in
`build/formal/`; they are CI artifacts, not mathematical assumptions.

Original local validation on 2026-10-15 covered 34 foundational declarations.
Stage-1 PR #6 now has 76 kernel-checked declarations including regular physical execution,
flow-completed pulse endpoint formulas, and 3.1/3.2 analogues for that regular subclass.
Theorems 3.1/3.2 remain incomplete over the paper's full finite-variation admissible class. The stage-1
source and axiom audit have passed a pinned-toolchain GitHub Actions run;
check the latest branch CI status before merging. There are advisory
tactic/unused-variable lint warnings.
The GitHub workflow checks Phase 2 pull requests; consult their checks for
remote execution results. Lean source is software under the repository's MIT license;
the manuscript and translations retain their separate copyright status.

The elasticity-to-concavity proofs currently assume response elasticity bounds
for **all positive prices**. That is stronger than the paper's statement
restricted to attainable prices and does not yet establish hypothesis
equivalence. The exact recovery-step invariant is a genuine result about
pure relaxation, but full resilient paths with concurrent paired executions,
flow-completed pulses, positivity and dollar ledgers are not yet formalized.

CI evidence for the earlier 46-declaration checkpoint:
[Lean kernel build + axiom audit, run 38835500287](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38835500287).

Latest 76-declaration success: [run 38844596170](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38844596170).
