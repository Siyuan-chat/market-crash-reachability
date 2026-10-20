# Lean formalization of the original research results

The repository retains Lean sources for sixteen original substantive numbered results. The [original-result manifest](ORIGINAL_RESULT_MANIFEST.md) identifies canonical declarations, exact hypotheses, scope audits and accepted proof commits. This scope includes the documented Proposition 7.5 boundary amendment; it does not assert that every historical PDF has the amended statement.

**The five V14 additions are not Lean-formalized.** See [current versions](../docs/VERSIONS.md) and [results and evidence](../docs/RESULTS_AND_EVIDENCE.md).

The historical accepted library audited 1,224 declarations at proof commit `15bec0e04613c040489b71a93595861ae5c82343`; [FINAL_AXIOM_AUDIT.json](FINAL_AXIOM_AUDIT.json) retains that snapshot. Subsequent removal of three superseded model modules left a reported 1,211-declaration audit. Counts describe different source revisions and do not replace checking the canonical theorem families. [Acceptance evidence](WHOLE_PAPER_LEAN_COMPLETION.md).

## Reproduce

Install Elan and Lean 4.19.0 from [lean-toolchain](lean/lean-toolchain). The [Lake manifest](lean/lake-manifest.json) pins Mathlib at `c44e0c8ee63ca166450922a373c7409c5d26b00b` and its dependencies. From the root:

```sh
cd formal/lean
lake exe cache get
lake build
cd ../..
python formal/check_proof_integrity.py
```

Python 3.11 and Lake on PATH are required for the integrity checker. It rejects unfinished proofs and custom axioms, audits all project theorem dependencies and writes evidence under `build/formal/`. Permitted foundational dependencies are `propext`, `Classical.choice` and `Quot.sound`. Cache download needs network access. A documented historical pass is not a fresh run.

## Technical references

- [Exact original-result manifest](ORIGINAL_RESULT_MANIFEST.md)
- [Theorem and hypothesis map](THEOREM_MAP.md)
- [Model fidelity](MODEL_FIDELITY.md)
- [Original certificate provenance](D01_CERTIFICATE_PROVENANCE.md)

The retained phase-specific gates describe historical proof approaches and restricted intermediate models. They do not override the original-result manifest. Lean source is software under MIT; manuscript rights remain separate under [NOTICE.md](../NOTICE.md).
