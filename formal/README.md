# Partial Lean formalization

Canonical mathematics: English V12 Final at commit
`e5339a47f29ccb669d1f228ca930a1c1146200bf`.

This project verifies coordinate, finite-dimensional conservation and response-family
foundations. It does **not** formalize the whole paper, the complete barrier
theorems, admissible controlled paths, or the interval certificate of Proposition 7.6.
See [the complete theorem map](THEOREM_MAP.md) and
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

Local validation on 2026-10-15: kernel build passed; all 34 project theorems
passed the axiom audit. There are advisory tactic/unused-variable lint warnings.
The GitHub workflow checks Phase 2 pull requests; consult their checks for
remote execution results. Lean source is software under the repository's MIT license;
the manuscript and translations retain their separate copyright status.
