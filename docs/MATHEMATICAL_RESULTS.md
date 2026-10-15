# Mathematical results and computational evidence

Numbering follows the shared theorem counter in each section of V12 Final.
Labels in `paper/main.tex` are the stable anchors. **Paper proofs are not
machine-formalized proofs.** Computational coverage below is deliberately narrower.

| Result (label) | Mathematical claim | Code / evidence | Kind and actual coverage |
|---|---|---|---|
| Theorem 1.1 (`thm:informal`) | Informal overview | Manuscript | Summary of later results, not a separate machine theorem |
| Theorem 3.1 (`thm:barrier1`) | Global elasticity barrier to all-asset decline | `verification/verify_generalized_coordinate.py`; `scripts/verify_results.py` | Analytic proof; symbolic coordinate identities and selected p-family numerical checks only |
| Theorem 3.2 (`thm:barrier2`) | Global barrier to systemic crisis at any breadth | Same programs | Analytic proof; no exhaustive test of arbitrary response functions or paths |
| Theorem 4.1 (`thm:ABC`) | A/B/C reachability classification | `scripts/verify_results.py`, `scripts/numerical_experiments.py` | Analytic proof; selected common-response examples illustrate classification |
| Proposition 4.2 (`prop:three-pulse`) | Local all-asset decline | `verification/finite_rate_and_bands.py` | Analytic expansion; selected finite-rate illustration, not universal validation |
| Proposition 4.3 (`prop:two-pulse`) | Local partial-coverage decline | `scripts/verify_results.py` | Analytic expansion; selected pulse amplitudes and exponents |
| Theorem 4.4 (`thm:critical`) | Sharp all-asset horizon threshold | `scripts/verify_results.py` | Analytic proof and construction; code checks curve values and monotonicity, not sharpness independently |
| Theorem 5.1 (`thm:resource`) | Necessary execution-resource lower bounds | `scripts/verify_results.py`, `scripts/make_figures.py` | Analytic proof; inequalities compared to selected constructive paths |
| Proposition 6.1 (`prop:rate-band`) | Rate and price-band exclusions | `verification/finite_rate_and_bands.py` | Analytic proof; formula evaluations and numerical examples |
| Theorem 6.2 (`thm:quadratic-rate`) | Small-rate quadratic crisis barrier | `verification/finite_rate_and_bands.py`; `verification/verify_consistency.py` | Analytic proof; selected scaling and exact-rational lower-rate exclusion |
| Theorem 6.3 (`thm:finite-rate-construct`) | Positive decline with bounded continuous execution | `verification/finite_rate_and_bands.py` | Analytic constructive proof; selected ordinary ODE illustrations |
| Proposition 7.1 (`prop:multiday-crisis-trigger`) | Conditional systemic trigger given streak closes | `scripts/verify_multiday.py` | Analytic equivalence; numerical product-condition regressions |
| Proposition 7.2 (`prop:rolling-rate`) | Necessary rolling-limit rates | `scripts/verify_multiday.py`, `scripts/make_multiday_figures.py` | Analytic necessary bound; selected model regressions |
| Theorem 7.3 (`thm:no-second-global`) | Obstruction to second all-asset lower-limit close | `scripts/verify_multiday.py` | Analytic invariant-region proof; finite examples only |
| Proposition 7.4 (`prop:streak-precondition`) | Dollar-closure preconditioning requirement | `scripts/verify_multiday.py` | Analytic necessary condition; selected ledger checks |
| Proposition 7.5 (`prop:market-cut`) | Market-cut funding capacity lower bound | `verification/verify_consistency.py` | Analytic proof; exact-rational evaluations for specified N,k |
| Proposition 7.6 (`prop:certified-v7`) | Existence of specified two-day constrained path | `verification/certify_streak_interval.py`; `data/certificates/final_interval_certificate.json` | **Rigorous computer-assisted existence proof**, one prescribed N=10,k=9 path; 80,000 outward-rounded steps, exact rational root and threshold checks |
| Proposition 7.6 cross-check | Printed endpoints, ledgers, crisis and rate bounds agree | `verification/verify_consistency.py`; `verification/audit_manuscript_certificate.py` | Exact checks of certificate fields plus independent floating-point DOP853; not a second interval proof |

The earlier supplement witness has terminal crisis approximately 0.019932.
It is ordinary numerical evidence and must not be substituted for the improved
certified witness exceeding 0.020. The bracket 0.044 < v* < 0.285 does not
identify the global minimum rate. Sensitivity claims outside the specified
certificate are not certified by it. See VERIFICATION_SCOPE.md.
