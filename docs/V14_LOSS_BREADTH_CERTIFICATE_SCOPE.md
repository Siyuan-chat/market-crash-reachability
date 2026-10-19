# V14: additional rolling-band loss--breadth certificates

**Repository source:** `verification/loss_breadth/`  
**Manuscript locations:** V14 Section 7 and Appendix `app:lossbreadth`  
**Evidence status:** Internally interval-checked, reproducible
constructive witnesses; **external code audit and new Lean proofs pending**.

## Frozen market assumptions

Ten hypothetical assets; all start at fundamental price F=1.
Common constant per-share impact g(S)=1 and linear price-level
recovery rate rho=0.4. Two model sessions of length 20 each.
The *new* controls apply uniform symmetric +/-25% **rolling** bands
to every asset. All cases impose complete dollar pairing, exactly
zero terminal net executed dollars **for every asset**, gross
share-rate strictly under 0.285, and cumulative gross shares sold
strictly under 2 per asset.

The original V13 witness is separate: the nine target assets
have +/-3% session bands and the single compensator has +/-25%.
Its k=9, ordinary 5.91% target losses, and mean log loss >0.020
are sourced from the existing original certificate, not re-created
by the scripts below. Because its target bands are tighter, its
existence also implies existence in a uniform +/-25% model.

## Fixed matched-dollar turnover, M < 3

| Control | Qualified assets | Strict lower bound: ordinary target drop | Strict lower bound: geometric-index drop | Turnover M | Method |
|---|---:|---:|---:|---:|---|
| P50-20 | 5/10 | >22.29% | >4.00% | 2.600000 | P3 |
| P60-20 | 6/10 | >20.90% | >5.00% | 2.880000 | P3 |
| P70-10 | 7/10 | >12.60% | >3.00% | 2.660000 | P3 |
| R70-15.5 | 7/10 | >15.50% | >4.00% | 2.939070 | P3 |
| k7_16p4_under_M3 | 7/10 | >16.40% | >4.00% | 2.970002 | P4 |
| R80-10 | **8/10** | **>10.80%** | **>3.00%** | **2.850337** | P3 |
| k9_8_under_M3 | 9/10 | >8.00% | >3.00% | 2.970003 | P4 |
| F100-0.65pct | 10/10 | >0.65% | >0.65% | 2.853113 | P3 |
| full_0p75_under_M3 | 10/10 | >0.75% | >0.75% | 2.969999 | P4 |

The main manuscript comparison table uses one stronger witness
per coverage, not every intermediary result. For the 80%-coverage
Proposition, the exact checked schedule gives target terminal
price below 0.892 and terminal market price product below
0.97^10, so the terminal systemic measure satisfies
C_0.8(40) > -log(0.97) > 0.0304.

## Turnover-relaxed witnesses: distinct feasibility regime

| Control | Coverage | Target ordinary drop | Geometric index drop | Used M | Budget |
|---|---:|---:|---:|---:|---:|
| k7_20_under_M4 | 7/10 | >20.00% | >6.00% | 3.960003 | M<4 |
| R70-20-M5 | 7/10 | >20.20% | >6.00% | 4.599448 | M<5 |
| full_2_under_M7 | 10/10 | >2.00% | >2.00% | 6.732000 | M<7 |

None of these belongs to the M<3 feasible set. In particular,
they do **not** establish minimum resource budgets, nor do
they exclude M<3 for 70%/20%, 90%/10%, or 100%/2%.

## What is and is not certified

All new controls have rational per-segment dollar rates,
and each group's signed-dollar flow integrates to zero
exactly. Prices solve `s' = -(2/5)(s-1)+q/s`.
The P3 checker uses outward-directed integers at scale 10^24;
P4 uses 10^25. Both employ bootstrap price enclosures,
bounded second derivatives, monotone scalar autonomous
segments, and conservative bounds on gross share executions,
rolling bands, inventory and matched-dollar turnover.
The geometric-index threshold uses an **exact rational**
terminal-product comparison.

Both programs, all control inputs, the manifest of strict
bounds, full interval-output JSON generated in CI, and
independent numerical reconstructions are in
`verification/loss_breadth/`. Reproduce using:

```sh
python verification/loss_breadth/verify_all.py
```

Python 3.11+ standard library suffices for the proof-critical
checks; optional `--audit` uses SciPy for independent high
precision ODE integration. Those numerical checks cannot
replace independent certification of the interval checker.
The original V13 source, frozen Lean proofs, and published
certificate hashes are not modified.

### Original versus new mathematical scope

The manuscript's new uniform-band Proposition establishes
one particular 8/10, >10.8% witness and a strictly positive
systemic index loss. The table records further **conditional
computer-assisted existence witnesses** under the same rules.
No claim is made that the listed controls are globally
optimal or that any OPEN matrix cell is impossible.

The prior raw exploratory packages are preserved separately
from the published V14 source. Their model assumptions,
verification scheme and individual limitations are reported
in the earlier Phase 3 and Phase 4 research reports.
