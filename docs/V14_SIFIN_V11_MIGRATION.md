# SIFIN V1.1 editorial migration and verification baseline

This file tracks the working V14 restructuring in PR #26. The published V13, archived software release, and existing interval certificate input files are unchanged.

## Approved manuscript architecture

1. Introduction: seven research-focused paragraphs and a symbol-free Abstract.
2. Model and Systemic Drawdown Criterion (old Section 2): settlement, positive prices, restoration, terminal loss.
3. Structural Barriers and Robustness (old Section 3 plus former Section 8 robustness propositions).
4. Reachability Regimes under Power-Law Impact (old Section 4): includes the full-coverage sharp horizon theorem and the fixed-exponent severe-loss construction.
5. Execution Resources and Turnover Bounds (old Section 5).
6. Reachability under Bounded Execution Rates (old Section 6).
7. Rolling Price Limits: Constrained Realizations (old Section 7): retains above-benchmark preconditioning and original certified witness.
8. Discussion (old Section 8 without the robustness propositions).
9. Conclusion (old Section 9).

All labels in the LaTeX source remain stable; printed theorem numbers change according to the new order.

## Result tracking

| Source result label | Kind | Statement (short title) | New chapter | Evidence / proof status |
| --- | --- | --- | --- | --- |
| `thm:barrier1` | theorem | Barrier to a decline of every asset | Structural Barriers and Robustness | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:barrier2` | theorem | Barrier to a systemic crisis of any breadth | Structural Barriers and Robustness | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:ABC` | theorem | A/B/C reachability regimes | Reachability Regimes under Power-Law Impact | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:three-pulse` | proposition | Local all-asset decline | Reachability Regimes under Power-Law Impact | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:two-pulse` | proposition | Local partial-coverage decline | Reachability Regimes under Power-Law Impact | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:sublinear-severe` | theorem | Uniform-resource severe partial-coverage losses for sublinear impact | Reachability Regimes under Power-Law Impact | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:critical` | theorem | Sharp all-asset horizon threshold | Reachability Regimes under Power-Law Impact | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:resource` | theorem | Execution-resource lower bounds | Execution Resources and Turnover Bounds | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:turnover-dissipation` | proposition | Turnover--dissipation bound under constant impact | Execution Resources and Turnover Bounds | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:rate-band` | proposition | Rate and price-band exclusion certificates | Reachability under Bounded Execution Rates | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:quadratic-rate` | theorem | A quadratic small-rate crisis barrier for constant impact | Reachability under Bounded Execution Rates | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:finite-rate-construct` | theorem | Positive all-asset decline with bounded continuous execution | Reachability under Bounded Execution Rates | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:multiday-crisis-trigger` | proposition | A conditional systemic-crisis trigger test | Rolling Price Limits: Constrained Realizations | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:rolling-rate` | proposition | Rolling-limit shock-rate certificates | Rolling Price Limits: Constrained Realizations | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `thm:no-second-global` | theorem | An obstruction to a second all-asset limit-down close | Rolling Price Limits: Constrained Realizations | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:streak-precondition` | proposition | Preconditioning needed for a dollar-closed limit-down streak | Rolling Price Limits: Constrained Realizations | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:market-cut` | proposition | A market-cut capacity and consecutive-limit lower bound | Rolling Price Limits: Constrained Realizations | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |
| `prop:certified-v7` | proposition | A computer-assisted two-day rate certificate | Rolling Price Limits: Constrained Realizations | Original formal statement retained verbatim; existing proof and/or appendix reference preserved |

## Certificate provenance and boundaries

- Original mixed-band two-session path: `verification/certify_streak_interval.py`, Appendix G (`app:v7certificate`); Section 7 retains its existence proposition.
- Uniform-band R80-10 and five neighboring cases: `verification/loss_breadth_certified.py`, Appendix I (`app:loss-breadth`).
- Six additional controls and twenty-four-cell research matrix: `verification/loss_breadth/` with exact-control input manifest and hash checks; Appendix I supplementary table.
- The original historical Lean acceptance scope is unchanged. New V14 propositions and numerical witnesses are not represented as fully Lean-formalized results.
- Verification requires full source/build CI plus independent mathematical review; a green PDF build alone does not establish the mathematics.

## Further editorial acceptance work

- Recheck theorem references after moving robustness results before the power-law classification.
- Preserve the full mathematical statement of every existing theorem and proposition during further proof exposition edits.
- Evaluate whether Section 7 can be compressed without removing hypotheses or the distinction between mixed-band and uniform-band witnesses.
- Ensure the general sublinear proof treats fixed exponent, fixed horizon and fixed market size correctly; rate-constrained matching-order claims are restricted to the common constant-impact subclass.
- Verify numerical certificate provenance, LaTeX references and PDF rendering after any further structural moves.

