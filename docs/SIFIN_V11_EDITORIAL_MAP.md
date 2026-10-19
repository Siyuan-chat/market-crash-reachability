# SIFIN V1.1 — Editorial Freeze and Proof-Audit Map

**Status:** Work-in-progress editorial restructuring on draft PR #25; no merge into `main` without further review.

**Source baseline:** `bebc17df99174ad7dabe2bd2cc41a9216b04c230`, V14 `submission/v14-turnover-dissipation/main.tex`, original Git blob SHA `dfcaae690cabc30c72d4bf3fdafe078260abdef8`. This commit is frozen for comparison; all new changes occur on `revision/v14-sifin-v11-structure`.

## Contribution narrative (approved V1.1)

1. **Structural barriers and robustness.** Derive homogeneous-market elasticity exclusions and quantify two failures under unmatched dollar flows or heterogeneous quadratic impact.
2. **Reachability regimes and sharp boundaries.** Contrast partial-coverage severe losses at fixed exponent and finite resource bounds against the sharp unattained full-coverage ceiling.
3. **Execution resources and constrained realizations.** Separate dollar turnover, gross share sales, and initial inventory; connect bounded-rate quadratic scaling to feasible multi-session paths.

Section 7 represents constrained construction, not empirical validation. Real market calibration, equilibrium selection and crash probability are outside the mathematical results.

## Result relocation map

LaTeX labels are the stable reference identifiers. Printed theorem and equation numbers may change after relocation, especially the two robustness propositions moving from Section 8 to Section 3. The exact `\begin{...}\end{...}` statement blocks remain byte-identical.

| Stable LaTeX label | Baseline location | Revised location | Proof or supporting evidence | Verification status |
|---|---|---|---|---|
| `asmp:model` | §2 The market: assumptions, execution, and price dynamics | §2 The market: assumptions, execution, and price dynamics | Assumption / no proof | Statement unchanged; proof review pending |
| `def:crash` | §2 The market: assumptions, execution, and price dynamics | §2 The market: assumptions, execution, and price dynamics | Definition / no proof | Statement unchanged; proof review pending |
| `def:budget` | §2 The market: assumptions, execution, and price dynamics | §2 The market: assumptions, execution, and price dynamics | Definition / no proof | Statement unchanged; proof review pending |
| `thm:barrier1` | §3 Structural barriers to market crashes | §3 Structural Barriers and Robustness | §3 inline | Statement unchanged; proof review pending |
| `thm:barrier2` | §3 Structural barriers to market crashes | §3 Structural Barriers and Robustness | §3 inline | Statement unchanged; proof review pending |
| `thm:ABC` | §4 Three market regimes under common constraints | §4 Reachability Regimes under Power-Law Impact | §4 inline; Appendix C | Statement unchanged; proof review pending |
| `prop:three-pulse` | §4 Three market regimes under common constraints | §4 Reachability Regimes under Power-Law Impact | §4 inline; Appendix B | Statement unchanged; proof review pending |
| `prop:two-pulse` | §4 Three market regimes under common constraints | §4 Reachability Regimes under Power-Law Impact | §4 inline; Appendix B | Statement unchanged; proof review pending |
| `thm:sublinear-severe` | §4 Three market regimes under common constraints | §4 Reachability Regimes under Power-Law Impact | §4 sketch and four-stage guide; Appendix H full proof | Statement unchanged; proof review pending |
| `thm:critical` | §4 Three market regimes under common constraints | §4 Reachability Regimes under Power-Law Impact | §4 sketch; Appendix D full construction | Statement unchanged; proof review pending |
| `thm:resource` | §5 Necessary execution resources | §5 Execution Resources and Turnover Bounds | §5 inline; Appendix A | Statement unchanged; proof review pending |
| `prop:turnover-dissipation` | §5 Necessary execution resources | §5 Execution Resources and Turnover Bounds | §5 inline | Statement unchanged; proof review pending |
| `prop:rate-band` | §6 Finite trading rates and abstract price bands | §6 Reachability under Bounded Execution Rates | §6 inline | Statement unchanged; proof review pending |
| `thm:quadratic-rate` | §6 Finite trading rates and abstract price bands | §6 Reachability under Bounded Execution Rates | §6 inline | Statement unchanged; proof review pending |
| `thm:finite-rate-construct` | §6 Finite trading rates and abstract price bands | §6 Reachability under Bounded Execution Rates | §6 inline; Appendix E verification | Statement unchanged; proof review pending |
| `prop:multiday-crisis-trigger` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 inline; Appendix J figure | Statement unchanged; proof review pending |
| `prop:rolling-rate` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 inline | Statement unchanged; proof review pending |
| `thm:no-second-global` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 inline | Statement unchanged; proof review pending |
| `prop:streak-precondition` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 inline | Statement unchanged; proof review pending |
| `prop:market-cut` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 inline | Statement unchanged; proof review pending |
| `prop:certified-v7` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 proof sketch; Appendix G certificate | Statement unchanged; proof review pending |
| `prop:loss-breadth-eight` | §7 Systemic drawdowns under rolling price-band constraints | §7 Rolling Price Limits: Constrained Realizations | §7 proof; Appendix I certificate | Statement unchanged; proof review pending |
| `prop:unbalanced-stability` | §8 Discussion and model extensions | §3 Structural Barriers and Robustness | §3 inline | Statement unchanged; proof review pending |
| `prop:heterogeneous-quadratic` | §8 Discussion and model extensions | §3 Structural Barriers and Robustness | §3 inline and two-pulse example | Statement unchanged; proof review pending |

## Equation, proof and data preservation

- **24 formal environments** (theorems, propositions, assumptions and definitions), **21 original proof environments**, and **86 numbered equation blocks** match the baseline source *verbatim* when compared independently of their order. An automated CI integrity script `scripts/check_sifin_v11_integrity.py` now reproduces the source comparison using `git show` on the frozen baseline SHA; CI fetches full history for this purpose.
- The response-adapted coordinate `eq:phi-intro` was moved from Section 1 into Section 2, preserving its complete equation body and its label. Printed equation numbers should be read from the compiled PDF and not inferred from old page references.
- The original Section 7 Table `tab:loss-breadth` is now in Appendix I alongside the twelve-control supplementary comparison `tab:loss-breadth-additional`. The certified Proposition `prop:loss-breadth-eight` remains in Section 7. All exact inputs and SHA-256 hashes are unchanged.
- Original conditional-threshold figure `fig:multiday-crisis-trigger` and sensitivity Table `tab:sensitivity` are in new Appendix J. The original two price/rate plots share a single two-panel figure in the main text, retaining both figure labels for source-link compatibility.
- Appendix A–I analytical proofs and verification resources remain intact. Appendix J contains relocated discussion and numerical visualization only. V13 published manuscripts and their frozen certificates are not edited.

## Mathematical review checklist (not superseded by GitHub CI)

| Topic | Audit target | Current evidence | Outstanding work |
|---|---|---|---|
| Structural barriers | Correct elasticity range, matched dollars, fixed price-level recovery | Original theorem and proof bodies unchanged | Independent mathematical reading of boundary assumptions |
| Unbalanced/heterogeneous stability | Convolution-sign bounds and weighted-flow counterexample | Original V14 argument and synthetic regression retained | Independent proof audit, including impulse extension |
| Severe sublinear reachability | Quantifiers: fixed exponent, asset count, common finite horizon and resources independent of loss severity | Original Appendix H proof unchanged; four-step exposition added to Section 4 | Independent audit of ledger closure, positivity and inventory bounds |
| Sharp full coverage | Strict unattained supremum and both directions of construction | Original Appendix D proof unchanged | Independent audit of positive-direction limiting argument |
| Resource lower bounds | Turnover counted once; share sales and initial inventory distinct | Original §5 / Appendix A identities unchanged | Independent proof audit |
| Matching finite-rate exponent | Upper and constructive lower order under common constant-impact conditions | Original §6 proofs unchanged | Independent joint-regime audit |
| Rolling-band certificates | Whole-path band, gross rate, turnover, inventory and dollar closure | Source code and interval inputs unchanged; new GitHub workflows replay them | Confirm CI success and inspect rendered panels |
| Publication status | Proof vs internal computer certificate vs external validation | This document distinguishes evidence classes | External peer review / independent mathematical audit remains outstanding |

## Editorial acceptance gates

- Abstract must contain no formula, symbol threshold, or theorem number.
- Introduction uses the seven agreed thematic blocks, including one paragraph grouping the three contribution streams and a proof-method roadmap.
- Structural barriers and both perturbation propositions appear in Section 3; the severe-loss and sharp full-coverage theorems both appear in Section 4.
- Theorem 4.4 gains an explanatory four-step roadmap outside the preserved original proof.
- Section 7 retains all original proposition statements but relocates selected display artifacts to Appendix I and J, with a combined price-and-gross-rate figure.
- Section 8 contains no numbered theorem or proposition.
- All 33 existing references and their in-text citations are preserved.
- GitHub V14 LaTeX, SIAM, independent ODE audit, all twelve synthetic interval witnesses, historical-result integrity, and PDF source checksum must pass; inspect the built PDF layout before changing PR readiness.

**Evidence levels:** Exact source preservation is mechanically verified. Successful CI is a software/build-and-certificate reproduction test, **not** an independent theorem proof or external peer-review acceptance.
