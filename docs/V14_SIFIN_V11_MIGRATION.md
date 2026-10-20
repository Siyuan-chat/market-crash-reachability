# SIFIN V1.1 manuscript editorial migration

Historical editorial map for the current V14 source. See [versions](VERSIONS.md). This is an **editorial manuscript reorganization**, not a new mathematical result or an independent mathematical peer review. The public historical V13 archive and all fixed numerical certificate inputs remain untouched.

## Approved mathematical narrative

1. Introduction — seven substantive paragraphs and a symbol-free abstract
2. Model and Systemic Drawdown Criterion — fixed assumptions, settlement and terminal loss
3. Structural Barriers and Robustness — two global barriers followed by two robustness propositions
4. Reachability Regimes under Power-Law Impact — all original power-law results, including the sharp full-coverage horizon bound
5. Execution Resources and Turnover Bounds — necessary turnover, inventory and dissipation estimates
6. Reachability under Bounded Execution Rates — rate-limited upper and constructive lower quadratic orders
7. Rolling Price Limits: Constrained Realizations — obstruction, preconditioning, market-cut capacity, and two certified existence propositions
8. Discussion — economic accounting, metric choice, deterministic interpretation and extensions
9. Conclusion — the three connected contribution groups

## Section 7 compression and figure provenance

The main rolling-band text has been shortened while **preserving the original formal propositions and their proofs in Section 7**, including the above-benchmark preconditioning statement and both certified two-session propositions.

- Appendix G (\`app:v7certificate\`): original mixed-band certificate, whole-path interval enclosure, terminal-threshold illustration, fixed-control sensitivity table, and adjacent price-path / gross-share-rate figures (\`fig:v7path\` and \`fig:v7rates\`)
- Appendix I (\`app:loss-breadth\`): the original six-witness comparison table (\`tab:loss-breadth\`), six additional uniform-band cases (\`tab:loss-breadth-additional\`), and both rational-certificate provenance descriptions
- The \`verification/loss_breadth/\` 12-witness inputs, exact rational schedules, hash records, and 24-cell research matrix remain unmodified
- Figure and table numbering in the output PDF is dynamic. **Use labels**, never hardcoded old table numbers

## Old-to-new result location map

| Stable LaTeX label | Previous location | SIFIN V1.1 location | Proof display | Status |
| --- | --- | --- | --- | --- |
| `asmp:model` | The market: assumptions, execution, and price dynamics | Model and Systemic Drawdown Criterion | Main text | Unchanged mathematical statement |
| `def:crash` | The market: assumptions, execution, and price dynamics | Model and Systemic Drawdown Criterion | Main text | Unchanged mathematical statement |
| `def:budget` | The market: assumptions, execution, and price dynamics | Model and Systemic Drawdown Criterion | Main text | Unchanged mathematical statement |
| `thm:barrier1` | Structural barriers to market crashes | Structural Barriers and Robustness | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:barrier2` | Structural barriers to market crashes | Structural Barriers and Robustness | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:unbalanced-stability` | Discussion and model extensions | Structural Barriers and Robustness | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:heterogeneous-quadratic` | Discussion and model extensions | Structural Barriers and Robustness | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:ABC` | Three market regimes under common constraints | Reachability Regimes under Power-Law Impact | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:three-pulse` | Three market regimes under common constraints | Reachability Regimes under Power-Law Impact | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:two-pulse` | Three market regimes under common constraints | Reachability Regimes under Power-Law Impact | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:sublinear-severe` | Three market regimes under common constraints | Reachability Regimes under Power-Law Impact | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:critical` | Three market regimes under common constraints | Reachability Regimes under Power-Law Impact | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:resource` | Necessary execution resources | Execution Resources and Turnover Bounds | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:turnover-dissipation` | Necessary execution resources | Execution Resources and Turnover Bounds | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:rate-band` | Finite trading rates and abstract price bands | Reachability under Bounded Execution Rates | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:quadratic-rate` | Finite trading rates and abstract price bands | Reachability under Bounded Execution Rates | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:finite-rate-construct` | Finite trading rates and abstract price bands | Reachability under Bounded Execution Rates | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:multiday-crisis-trigger` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:rolling-rate` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `thm:no-second-global` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:streak-precondition` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:market-cut` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:certified-v7` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |
| `prop:loss-breadth-eight` | Systemic drawdowns under rolling price-band constraints | Rolling Price Limits: Constrained Realizations | Main text (possibly supplemented by Appendix) | Unchanged mathematical statement |

## Acceptance boundaries

- Formal result statements, existing numbered equations and all LaTeX labels are preserved byte-for-byte.
- Theorem and figure *printed numbers* may change after relocation, but all stable \`\\label\` identifiers remain unchanged.
- Existing certified path and resource figures are not converted into empirical results.
- CI checks evaluate stable mathematical statements, bibliography, source validity and LaTeX build.
- **No completed independent mathematical proof review is claimed.** A completed editorial merge must not be presented as completion of the independent proof audit.
