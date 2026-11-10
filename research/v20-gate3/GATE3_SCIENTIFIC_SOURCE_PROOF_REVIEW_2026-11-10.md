# V20 Gate 3 scientific source-proof and coverage audit — 2026-11-10

**Scope:** internal mathematical/textual acceptance review; NOT a third-party peer review or a Lean formalization of the new activity-driven theorems. The mandatory source is `submission/v20-gate3-activity-recovery/main.tex`, not `paper/main.tex` or the old V17 12-page draft.

## Coverage and source integrity

- Original 40-page English author PDF and the editable V16 mathematics are retained as the *research-question baseline*. All 43 IDs M01–B01 remain in the V20 traceability CSV. No original question was deleted to shorten the manuscript.
- The active V20 work is a paper with 33 explicit mathematical result environments, each carrying a stable unique label and an immediately following proof environment; the original impact/recovery law, C0/C1 and flow-completed event accounting are explicit.
- Six PDF research figures include explicit `NUMERIC_ONLY` labels for historical I/II floating-point trajectories; their pictures are NOT the explicit high-budget analytic witnesses. Two separate numerical/analytic severity tables retain the original table's analytical role.
- The 33-entry V16 bibliography master is checksum-pinned; current V20 cites the relevant 16 keys, including all 15 keys explicitly cited in the V16 manuscript. Venue-specific JPX rules are not confused with the hypothetical symmetric 25% bands.
- The construction III certificate remains **INTERNAL_INTERVAL_CROSSCHECK_2**, not external formal proof. Strong results I/II use alternate explicit analytically certified high-budget parameter witnesses; old low-turnover float roots remain NUMERIC_ONLY.

## Every result statement and adjacent proof

| Source line | Label | Exact proof method / necessary scope |
|---:|---|---|
| 157 | `prop:time-change` | Positive time reparameterization of absolutely continuous paired flows and finite ordered completed events; exact ledgers/turnover/seller shares invariant; fixed rate caps excluded. |
| 232 | `prop:account` | Activity-coordinate chain rule plus paired-dollar accounting; quadratic term recognized as execution dissipation, not a conserved legacy potential. |
| 268 | `thm:triangle` | Nine ordered edges with exact zero-dollar cycles; second-order signed event expansion and concatenation for N>3. |
| 322 | `prop:two-node-barriers` | Shared N=2 gross clock, scalar concavity comparison and log-space Jensen; limited to e>=1/2 stated regimes. |
| 345 | `thm:two-local` | Two-event perturbation expansion for p<=1 and Gronwall/Cauchy-Schwarz uniform small-budget obstruction for 1<p<2. |
| 403 | `thm:two-large-turnover` | Stable seller/buyer equilibria with product<1 for 1<p<3/2 and independent exact p=5/4 rational finite-budget witness. |
| 503 | `prop:two-critical-p` | Hyperbolic seller rate gamma_->buyer rate gamma_+ at p=3/2, scalar comparison makes finite terminal product <1. |
| 567 | `cor:nearcritical-beyond` | Strict p=3/2 terminal product and uniform ODE continuous dependence on p on compact positive paths, with fixed finite edge dollar amount. |
| 637 | `thm:floor` | Comparison with pure-seller drift f_-, positive scalar roots and tangent noncrossing threshold Kc(p). |
| 662 | `thm:aggregate` | Inward-pointing power-sum barrier at sum x^(2-p)=1; necessary, not sufficiency/sharpness. |
| 682 | `thm:lower` | One-sided variation and actual seller-edge share inventory, summed without double-counting dollars. |
| 712 | `thm:kresource` | Exact signed dollar closure in activity time, nonnegative quadratic potential and causal bound on high-side excursions. |
| 738 | `prop:second` | Below-benchmark sign of the paired activity potential excludes every price strictly falling over the whole session. |
| 770 | `thm:ratequadratic` | Compact strip first-exit bootstrap, paired first-order cancellation and logarithmic Taylor bound. |
| 812 | `prop:pure-sale` | Necessary scalar fastest-decrease differential inequality in price regions where denominator is positive. |
| 860 | `prop:breadthprod` | Exact cross-sectional product identity and order statistic bound for repeated lower closes. |
| 882 | `prop:cutcap` | Cross-cut dollar flow bounded by each side's contemporaneous gross sale/buy capacity. |
| 901 | `cor:at-most-n-minus-one` | Second rolling upper bound lies strictly below F if all closed day1 down; potential prevents all falling further. |
| 927 | `prop:two-day-rate-lower` | Scalar arctan(2x-1) decrease limit integrated across session2, plus rational alternating-series lower and internally certified feasible speed upper. |
| 1010 | `lem:completion` | Zero-diagonal transportation matrix existence via singleton Hall/max-flow conditions under equal gross node amounts. |
| 1026 | `lem:embed` | Activity time exact embedding of prescribed radial trajectories with genuine paired edge-flow completion. |
| 1045 | `thm:tenhalf` | Sharp equal-weight stage cut roots, explicit h>0 contraction/IVT and resource/inventory envelope (not cached float witness). |
| 1103 | `thm:nine` | Fixed-resource p=0 severe family: bracketed compensator roots, q-uniform smooth positive width and integrable final inventories. |
| 1172 | `thm:nine-general` | Fixed-p<1 exact radial identity, uniform stage Jacobian and compact q-uniform contraction, compensated exact ledgers and finite seller inventory. |
| 1271 | `thm:two` | C1 two-session 19-edge+five-cycle path; independently cross-checked *internal* outward-rounded interval certificate. |
| 1468 | `prop:unmatched` | Conditional same-flow compact-strip Gronwall stability; explicit zero net unmatched forcing needed to retain closure. |
| 1518 | `prop:hetero-weighted` | Exact heterogeneous quadratic log-coordinate identity and appropriately weighted high-price gross-activity bound. |
| 1569 | `prop:hetero-two` | Heterogeneous quadratic two-asset C1 counterexample from signed leading triangle and second-order log coefficient. |
| 1767 | `lem:one-sided-bv` | Final below-benchmark excursion and negative Jordan variation dominated by real seller-side shares. |
| 1833 | `prop:rate-explicit` | Explicit fixed-strip causal bootstrap and paired-rate quadratic aggregate/log bound. |
| 1880 | `prop:rate-local-match` | Time-resolved sequential triangle cycles of order (vT)^2, truly C1, equal net dollars. |
| 2090 | `lem:radial-general` | Power-law radial change of variables with exact net flow and ledger identities for each fixed p<1. |
| 2136 | `lem:terminal-inventory` | Affine terminal fractions and integrable (1-s)^(-1/nu) share consumption for nu>1. |

These descriptions summarize source proof obligations, not standalone machine-checked verification. Each claim has been checked for explicit assumptions and the provenance of its supporting analytic lemma, interval checker or original source version. The structural test `check_scientific_coverage.py` checks presence of all 33 result statements, proof environments, their labels and references; it is *not* a substitute for mathematics.

## Unresolved but bounded scientific questions

| Original IDs | What is rigorously supported | What remains OPEN and cannot appear as proved |
|---|---|---|
| `T03`, `P02`, `R02` | N=2 finite C1 crisis for all 1<p<=3/2 and a nonempty K-dependent interval beyond 3/2; small-turnover exclusion for all 1<p<2; p>=2 homogeneous global barrier. | Full two-node 3/2+epsilon(K) to 2 classification, monotonicity and the complete N,graph,K phase diagram. |
| `A04` | At N=10,p=0,K=4e-18, the exact analytic 50% witness and power-sum barrier give log2 <= delta_all^*(K) <= 0.5log10. | Sharp full-coverage loss-amplitude threshold. Calendar-time horizon is a separate question now resolved by time change. |
| `P10`, `R03` | Five C1 targets achieve repeated 25% lower closes, all-ten repeats impossible, so 5<=k*<=9; for five targets v*_5 lies between explicit arctan rate lower and strict internal-certified 0.133 upper. | Optimal 6–9 coverage existence and sharp minimum rate. No claim that five or nine is optimal. |
| `R01` | Exact heterogeneous weighted quadratic equation and counterexample; unmatched-dollar perturbations bounded on a common positive compact strip with explicit zero-integral condition for terminal closure. | Global closed-loop/structural perturbation stability and optimal execution, not needed for main existence claims. |

## Gate 3 judgment criterion

The handoff permits an original mathematical question to remain genuinely unsolved provided a substantive analysis, correct bounded result and explicit OPEN status are present; it **does not** permit promoting a hypothesis to a theorem or dropping it. These 7 original IDs remain partial/open on purpose, and none serves as an unsupported premise of the abstract or three main construction theorems.

Passing GitHub Actions establishes dependency, bibliography, static evidence and build reproducibility; the Lean workflow formalizes *historical existing* declarations, not the V20 theorems. Gate 3 acceptance may be recorded only after the current V20 actual SIAM/BibTeX build, the full 43-item/33-proof coverage checks and the final statement-strength review pass for this exact source commit. Gate 4, bilingual Word creation and new DOI remain separate.
