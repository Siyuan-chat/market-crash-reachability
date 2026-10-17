# Partial Lean formalization — whole-paper project

2026-10-17: Propositions 7.1, 7.5, 6.1 and 7.2 are PAPER_ACCEPTED (**4/16**). A03 proof commit `5c84995094b736c0231df6d804c8daad638bbfc7` passed all four same-SHA CI checks, local full build, 256-declaration axiom audit and 230 release hashes. B02/B03 full original candidates and the uncounted B01 physical BV bridge are undergoing final scope/integrity checks. See the [single current status entry](WHOLE_PAPER_LEAN_COMPLETION.md).

Canonical mathematics: English V12 Final at commit
`e5339a47f29ccb669d1f228ca930a1c1146200bf`.

This project verifies foundations, actual finite regular physical market paths,
a nonlinear one-edge physical price response under Stieltjes trade clocks, and
joint multi-edge physically recovering execution under a common smooth operational
clock. The latter now participates in the finite admissible trace and its proved
3.1/3.2 analogues. It **does not yet** formalize the original whole-paper
quantifiers over all M1–M5 BV execution paths or the interval certificate
of Proposition 7.6.
Follow the [whole-paper proof tracker](https://github.com/Siyuan-chat/market-crash-reachability/issues/5).
**Original-paper acceptance: 4/16 (Propositions 7.1, 7.5, 6.1 and 7.2).** Proposition 7.1's exact terminal product criterion, quantile cases, severity and single-compensator consequence are now Lean kernel-verified as a complete original conditional endpoint result; [197/197 proof audit](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38983955426). The other 12 original numbered statements remain unaccepted. Consult the [16-result completion matrix](WHOLE_PAPER_LEAN_COMPLETION.md); older 190-declaration Phase 4 snapshots are historical only, and the optional countable-atom modules have been pruned.

Phase 2's [bounded-variation proof gates](PHASE2_BV_GATES.md) distinguish proven accounting and crisis-parameter bridges from the unproved full BV price dynamics.
Phase 3's [a.e. operational-clock proof gates](PHASE3_AE_GATES.md) record the
Lipschitz/a.e. physical response chain rule, the actual Stieltjes variation
clock estimates, and the distinct absolute-continuity FTC and full-BV
completed-graph inclusion obligations. The latest mathematically tested Phase 3 source commit
`c619ba26805facb0cf5d5cf2a87383fdd0d517a4` passed
[159/159 Lean kernel and axiom audits](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38861075606).
The 159 declarations include the inverse-variation-clock inequalities
on its actual image and conditional a.e.-FTC comparison, still for
**typed restricted classes**. No entire-original-BV theorem is
claimed from these checkpoints.
Phase 4's [historical atomic-gap notes](PHASE4_ATOMIC_GATES.md) document optional extensions removed from the direct-paper Lean branch. The current [Draft PR #10](https://github.com/Siyuan-chat/market-crash-reachability/pull/10) prioritizes exactly the 16 original numbered results, and the finite physical pulse proofs required by the manuscript are retained.
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
Stage-1 PR #6 on main was kernel/axiom-checked for 76 regular physical-market
declarations. Draft PR #7 at commit `83213b607f362a828e5556cd4f09b7d315c3ded0` passed
**138/138** Lean 4.19/pinned-Mathlib kernel and axiom audits:
[Lean workflow #38857616141](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38857616141).
All 138 declarations are genuinely checked, but none may be read as unformalized
equivalence to the full BV manuscript class. Remaining scope is tracked in
[Phase 2 BV gates](PHASE2_BV_GATES.md). Advisory lint warnings may remain.
Lean source is software under the repository's MIT license; manuscript and
translations retain separate copyright status.

Selected one-segment **attained-price** elasticity-1 barriers have been proved
for continuous operational-clock physical paths starting from the benchmark.
The finite-trace 3.1/3.2 analogues and the clocked segment's 3.2 analogue still
assume global elasticity bounds. The full physical BV/a.e. chain rule and faithful
M1–M5 completed-graph inclusion are pending; Stieltjes *accounting* and
one-edge Stieltjes time-change do not supply this general conclusion.

CI evidence for the earlier 46-declaration checkpoint:
[Lean kernel build + axiom audit, run 38835500287](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38835500287).

Stage-1 76-declaration success: [run 38844596170](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38844596170).

Phase-2 138-declaration success (prior to this documentation update):
[run 38857616141](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38857616141).
