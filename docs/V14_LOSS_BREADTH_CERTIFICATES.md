# V14 uniform-band loss–breadth certificate integration

## Scientific scope

This V14 working-manuscript revision adds **a new computer-assisted
80%-breadth existence witness** and an explicit comparison table in Section 7.
It does not change the original nine-target, 3%/25%-band existence certificate
or any published V13 manuscript/Zenodo/SSRN version.

The additional model uses ten normalized assets, F=eta=1, price-level recovery
rho=0.4, T=40 (two sessions of length 20), and a **uniform symmetric +/-25%
rolling band on every asset**. Dollar-paired execution, zero net terminal dollar
flow separately for each asset, per-asset gross share rate <0.285, and cumulative
sales <2 shares remain required. We compare resources by the **same total paired
dollar turnover** M, counting each buyer-seller pair once.

## Main result — eight of ten targets

Exact rational directed rounding with fixed Q=10^25 yields for R80-10:

- k/N = 8/10, target ordinary price loss strictly exceeds **10.8%**
- equal-weight geometric market price-index drop strictly exceeds **3.0%**
- therefore mean log loss exceeds -log(0.97)>0.03, and C_0.8(40)>0.03
- dollar turnover M exactly **2.850336609376 < 3**
- maximum gross executed-share rate strictly less than **0.273 < 0.285**
- maximum shares sold per asset strictly less than **0.874 < 2**
- whole-path rolling price-band margin strictly exceeds **0.007**
- conservative terminal intervals: target (0.89090, 0.89161),
  receiving asset (1.33067, 1.33116), in benchmark price units
- every per-asset dollar ledger closes **exactly**, because the piecewise
  constant rational dollar-rate signal integrates to zero in each group.

The result is mathematical existence for a **specified synthetic path**.
It is not a real exchange case study, a forecast, or an estimate of optimum
market crash severity.

## Comparison of verified model paths

All loss percentages below are **strict conservative thresholds** certified by
the automated rational enclosure, not high-precision best-fit endpoints.
Market index drop is an ordinary geometric-index percent decrease, separate
from the mean logarithmic-loss quantity used in C_alpha. Turnovers are rounded
for presentation but checked as exact rationals.

| Source | Coverage | Target ordinary drop > | Geometric index drop > | M | Cap |
|---|---:|---:|---:|---:|---:|
| Published mixed-band path | 90% | 5.91% (exact terminal) | 1.98% | <3 | 3 |
| P50-20 | 50% | 22.29% | 4.00% | 2.600 | 3 |
| P60-20 | 60% | 20.90% | 5.00% | 2.880 | 3 |
| P70-10 | 70% | 12.60% | 3.00% | 2.660 | 3 |
| R70-15.5 | 70% | 15.50% | 4.00% | 2.939 | 3 |
| R70-16.4 | 70% | 16.40% | 4.00% | 2.970 | 3 |
| R80-10 | 80% | 10.80% | 3.00% | 2.850 | 3 |
| R90-8 | 90% | 8.00% | 3.00% | 2.970 | 3 |
| F100-0.65 | 100% | 0.65% | 0.65% | 2.853 | 3 |
| F100-0.75 | 100% | 0.75% | 0.75% | 2.970 | 3 |
| R70-20 (M4) | 70% | 20.00% | 6.00% | 3.960 | 4 |
| R70-20 (M5) | 70% | 20.20% | 6.00% | 4.599 | 5 |
| F100-2 (M7) | 100% | 2.00% | 2.00% | 6.732 | 7 |

Only the first ten rows have M<3. The last three belong to distinct
relaxed-budget comparisons and cannot be used to claim the M<3 outcomes.
The cases do not identify the globally maximum achievable losses.

## Reproduction map

- Paper Section 7: comparison table and computer-assisted Proposition
  labelled prop:uniform-band-breadth.
- Paper Appendix labelled app:loss-breadth: model, R80-10 exact rational
  control schedule, bootstrap, global price bands, market-index test.
- verification/loss_breadth/certify_loss_breadth.py: standard-library
  directed integer/rational verifier for **12 new** paths.
- verification/loss_breadth/phase4_schedules.b64: losslessly packed source
  dollar-rate schedule inputs for five longer phase-4 controls;
  generated decoded_phase4_schedules.json shows exact rates in plain text.
- verification/loss_breadth/check_paper_sync.py: data/LaTeX table match.
- verification/loss_breadth/independent_ode_audit.py: optional independent
  DOP853/Radau floating ODE audit (SciPy dependency).
- .github/workflows/loss-breadth.yml: reruns the exact checker and uploads
  generated full interval enclosures, derived comparisons, and decoded inputs.

Run from the repository root:

    python verification/loss_breadth/certify_loss_breadth.py
    python verification/loss_breadth/check_paper_sync.py

Optionally install scipy and then run:

    python verification/loss_breadth/independent_ode_audit.py

## Proof and code limitations

The custom checker uses fixed-point integers, outward rational bounds,
case-wise verified whole-strip derivative estimates, and a monotone scalar
ODE comparison/Taylor enclosure. All input controls are frozen exactly.
The script's success supports a **computer-assisted existence certificate**
for those schedules; it does not establish global optimization or
non-reachability of unobserved alternatives. As of this change, the new
certificate implementation has been independently re-run against its
original research snapshot and cross-checked numerically, but has not
been formally Lean-verified or externally independently code-reviewed.

For that reason, the historical V13 accepted theorem/certificate count must
never be silently enlarged by these new results. In the manuscript the new
witness is identified as a computer-assisted Proposition, and its independent
audit requirement is disclosed.
