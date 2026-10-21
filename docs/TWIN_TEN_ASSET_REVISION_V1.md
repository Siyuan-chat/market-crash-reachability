# Narrative-focused major revision — twin ten-asset benchmarks (working V14-R1)

**Status:** GitHub working revision, 21 October 2026. This document describes *revision changes*, not an independently peer-reviewed manuscript, a new SSRN submission or a Zenodo archival deposit. The frozen 20 October 2026 V14 Zenodo edition ([10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787)) and original immutable software archive ([10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183)) **do not contain or validate this revision's added A1/A2 reconstructions and figure**. The preceding research baseline remains separately identifiable.

## Organizing mechanism

For positive impact response $g(S)$ define $\Phi(S)=\int_F^S u/g(u)\,du$. Trade-normalized executed dollars satisfy $d\Phi|_{\mathrm{trade}}=dX$, and paired transfers conserve $H=\sum_i\Phi(S_i)$ along trades. Price-level recovery generally shifts $H$ between those trades. At all times the paired network obeys $\sum_i dX_i=0$; **terminal settlement adds** $X_i(T)=0$ separately for each asset. Neither requires $\theta_i(T)=\theta_i(0)$. Inventory consumption funds terminal price displacements and recovery dissipation through the established cost identity. The full proof and model restrictions remain in [the manuscript](../submission/v14-turnover-dissipation/main.tex).

## Exactly what the twin benchmarks establish

| Case | Parameters and target | Result and resources | Evidentiary status |
|---|---|---|---|
| **A1 idealized, all ten** | $N=k=10$, constant $g=1$, $F=\eta=1$, $\rho=0.4$, $T=40$ | All ten ordinary price declines **50%**; $\mathcal C_1=\log2$; reconstructed $M\approx34.37368048$, maximum cumulative gross sold shares $\approx16.58848226$, per-asset executed-dollar residual $<10^{-12}$. Sharp ordinary full-coverage **unattained** upper limit $\approx68.3772\%$. | Analytic existence/ceiling in Theorem `thm:critical` and Appendix D; *new ordinary double-precision ledger reconstruction*, **not** new interval certification; no rate cap |
| **A2 idealized, nine of ten** | $N=10$, $k=9$, constant $g=1$, $F=\eta=\rho=1$, $T=4$, low direction $c=10^{-3}$, $L=3,5,10,20$ | Nine target prices $e^{-L}$, one compensator. Table in Appendix F reports $\mathcal C_{0.9}$, $M$ and maximum gross sold shares for each target. A theorem supplies a **severity-independent finite resource upper bound** for a constructed family, not for all possible strategies. | Analytic Appendix C construction + ordinary double-precision reconstruction; no finite gross-rate assertion |
| **B1 constrained, seven of ten** | $N=10$, $F=\eta=1$, $\rho=0.4$, $T=40$ in two sessions; uniform $\pm25\%$ rolling bands | Seven target ordinary declines **>20.2%**; geometric-index ordinary fall **>6%**; $M<5$; gross rate $<0.285$; gross share sales $<2$ per asset; individual terminal dollar closure | Existing internal exact-rational outward-rounded interval certificate `R70-20-M5`, not externally peer-reviewed |
| **B2 constrained, all ten** | Same market parameters and bands as B1 but *different execution control and budget* | All ten ordinary price declines **>2%**; geometric-index ordinary fall **>2%**; **$M<7$**, not $M<5$; same rate/inventory limit class | Existing internal interval certificate `full_2_under_M7`, not externally peer-reviewed |

Additional separately certified comparator controls in the main Section 7 table are **P60-20** ($k=6$, target decline $>20.9\%$, index $>5\%$, $M<3$) and **R70-20-M4** ($k=7$, target $>20\%$, index $>6\%$, $M<4$). Each budget and threshold belongs to its own verified control; there is **no joint-budget or optimality claim**. B1 and B2 use different paired transfer schedules from the original nine-target mixed 3%/25% band certificate, which is retained unchanged.

### Reproducibility commands

Run from the repository root, using Python 3.11:

```sh
# A1 + A2 analytic-primitive reconstructions and stored independent numerical regression values
python verification/twin_ten_asset_benchmarks.py --check
python verification/twin_ten_asset_benchmarks.py --json

# B-series existing prescribed rational controls and internal interval checks
python verification/loss_breadth/verify_all.py

# Ensure the original theorem statements, numbered formulas, and V14 result footprint are preserved
python scripts/check_v14_resource_bound.py

# Compile the working LaTeX and new TikZ model-path figure
python scripts/build_v14_resource_bound.py
```

The A1/A2 script implements each fixed-radius trade as a positivity-preserving interpolation in squared-price coordinates, solves the scalar compensator/direction root by bisection, allocates stage lengths using integrated recovery weights, accumulates directed paired-dollar turnover once, and checks both per-step conservation and **each final executed-dollar ledger**. It uses analytic primitives and double precision; numerical residuals do not constitute an interval certificate. The reference values are in [the new fixture](../data/twin_ten_asset_benchmarks.json) and CI reruns the reconstruction. The script does not attest to minima, practical trading incentives, or an empirical price process.

For B1/B2, [the unmodified source-result manifest](../verification/loss_breadth/verified_results_manifest.json), [control inputs](../verification/loss_breadth/phase4_controls.json), [certificate methods](../verification/loss_breadth/README.md), and [hashes](../verification/loss_breadth/SHA256SUMS.json) retain their original evidence identities. Results are exact-control *existence witnesses* only. The working revision's comparative table reuses their conservative strict inequalities and does not claim any new optimized or recertified paths.

## Audit and version boundaries

- **Narrative and layout:** Abstract and Introduction rebuilt to connect impact, conservation, resilience, barriers, attainability and resources. A model-derived two-panel mechanism/ten-asset path figure is added as an editable TikZ source; the plotted paths are the model's explicit control paths, not empirical or freely invented curves. Section 4 adds A1/A2; Section 7 promotes already certified constrained controls; Section 8 distinguishes volume-coordinate recovery from price-level recovery and does not introduce a new elasticity-barrier theorem.
- **Mathematics protected:** Existing theorems, assumptions, numbered equation bodies, appendix proofs, old interval certifiers, Lean modules and legacy source versions are not deliberately rewritten. The historical original Lean coverage does **not** extend to V14's five added results or the new narrative examples. The existing check script validates the original statement/equation boundary rather than substituting for independent mathematics review.
- **Evidence state:** A1/A2 numerical reconstruction is new working-version evidence. The B-series interval evidence predates this revision, with its original immutable control-input hashes. Original 80,000-step certificate and published snapshots retain separate provenance. Do not imply either frozen DOI already includes revised figures/code.
- **No new research claims:** This revision does not estimate crash likelihood, real-market calibration, optimal trading, or all nonlinear-resilience thresholds. Price changes are ordinary percentages where labeled, otherwise log-loss units. Price-level recovery is necessary for the stated elasticity barriers; switching to volume-coordinate recovery requires new proofs except the identified necessary resource bounds and constant-impact special case.

Publication requires rebuilding and auditing the revised PDF, pinning its new source commit and checksums, and establishing a **new** archival identity before claiming that the new revision has been deposited. The old fixed Zenodo identifiers are preserved without revision.
