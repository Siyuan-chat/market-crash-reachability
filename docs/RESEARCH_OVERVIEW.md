# Research overview and FAQ: When Can Markets Crash Without News?

**Author:** Siyuan Ye (Independent Researcher)
**Current manuscript:** *When Can Markets Crash Without News?*, V14 ([GitHub and Zenodo](VERSIONS.md)); V13 is a preserved Zenodo archival edition; see the version reference for the newer live SSRN revision. See [versions](VERSIONS.md).
**Research-software version:** 1.0.0rc1 · [public repository](https://github.com/Siyuan-chat/market-crash-reachability)

This is a reader-oriented guide, not a replacement for theorem statements. For precise claims and hypotheses, consult the [manuscript](../submission/v14-turnover-dissipation/manuscript.pdf), [LaTeX source](../submission/v14-turnover-dissipation/main.tex), [supplement](../supplementary/supplementary.pdf), and [theorem-to-evidence map](RESULTS_AND_EVIDENCE.md). The English manuscript is authoritative.

## The research question

**Can trading produce a systemic market drawdown without adverse fundamental news?** The paper studies deterministic reachability in a specified multi-asset mathematical market. Its assumptions include fixed fundamental benchmark F, nonlinear price impact, price resilience toward F, equal-dollar pairs of risky-asset purchases and sales, and zero *terminal signed executed-dollar flow for each asset*. Prices and executed trades must satisfy admissibility constraints. No endogenous choice of trading strategy, real-world crash probability, or empirical return prediction is derived.

The main technical device is a response-adapted generalized price coordinate. For positive price response g(S):

$$
\Phi(S)=\int_F^S\frac{u}{g(u)}\,du,\qquad
dy=B\,dz-\rho R(y)\,dt.
$$

Executed-dollar transfers then enter additively; the recovery law carries the remaining state dependence. This is a model-specific normal form, not an empirical order-book identity.

## The paper's definition of systemic drawdown

For N positive prices initially equal to F, define terminal log losses L_i(T) = log(F / S_i(T)). Let A(T) be the cross-sectional average log loss and Q_alpha(T) the k-th largest log loss, where k = ceil(alpha N). The crisis statistic is

$$
C_\alpha(T)=\min\{A(T),Q_\alpha(T)\}.
$$

A terminal systemic crisis at threshold delta > 0 requires C_alpha(T) >= delta: both mean loss and losses in at least k assets reach the threshold. This is a **common-benchmark terminal loss**, not a rolling peak-to-trough drawdown.

## Results and qualifications

1. **Global barriers, Theorems 3.1–3.2.** Elasticity e(S) = S g'(S)/g(S) >= 2 throughout the admissible price domain excludes positive systemic drawdowns in this paired-dollar resilient model. The weaker e(S) >= 1 excludes a simultaneous fall in every asset. Neither condition is a universal theorem about real exchanges.
2. **A/B/C reachability, original Theorems 4.1 and 4.4 (`thm:ABC`, `thm:critical`; printed numbering differs in V14).** For g_p(S) = eta(S/F)^p, p = 2, 1, 0 respectively illustrate exclusion, inventory-bounded partial-coverage losses and potentially arbitrarily severe partial-coverage log losses. The severe p = 0 result requires k < N, sufficiently long finite horizons, and allowed execution pulses; finite inventory and turnover budgets remain part of the hypotheses.
3. **Execution resources, Theorems 5.1 and 6.2–6.3.** Necessary turnover and inventory inequalities constrain execution. With constant per-share impact and a bound on gross executed-share rates, the maximal small-rate systemic loss has quadratic scaling, with a continuous construction achieving its scaling order.
4. **Certified two-session example, Proposition 7.6.** A prescribed N = 10, k = 9 path makes nine assets close at their lower daily price limits in two consecutive sessions. Its interval certificate establishes C_0.9(40) > 0.020 in log-loss units while enforcing the specified price bands, positive prices, executed-dollar ledger closure and rate/resource bounds. The certificate proves **existence for this instance**, not a globally optimal control or a general market forecast.

The paper's analytical proofs, selected numerical regressions, rigorous interval certificate, and original-result Lean formalization have distinct coverage. Consult [verification scope](VERIFICATION_SCOPE.md) and [mathematical results](RESULTS_AND_EVIDENCE.md) before generalizing a result.

## Research FAQ

### Can a market crash without news?

Under some configurations of the paper's idealized model, a systemic drawdown is mathematically reachable with unchanged fundamental benchmarks. This does not explain any particular historical crash or estimate the likelihood that market participants would generate that path.

### Does elasticity at least 2 prevent all market crashes?

Only within the model and hypotheses of the corresponding barrier theorem. It is not an empirical safety threshold for actual markets.

### Do daily trading price limits rule out consecutive market-wide declines?

Not automatically in this model. The certified two-session construction satisfies the specified rolling daily bands; the calculation does not model all institutional features, such as locked-limit order queues.

### Is the ten-asset construction merely a numerical simulation?

No. A computer-assisted existence result uses 80,000 outward-rounded interval steps and exact-rational comparisons for one prescribed path. Ordinary floating-point ODE integration provides a consistency check, not a second interval proof. See the [certificate](../data/certificates/final_interval_certificate.json), [certifier](../verification/certify_streak_interval.py) and [verification scope](VERIFICATION_SCOPE.md).

### Which results are formally proved or interval certified?

The [Lean manifest](../formal/ORIGINAL_RESULT_MANIFEST.md) records sixteen original substantive numbered results, with exact hypotheses and the Proposition 7.5 boundary amendment. The historical accepted audit had 1,224 declarations; the later module cleanup reported 1,211. Those counts describe source revisions, not additional paper theorems. **V14's five additions are not Lean-formalized.** The original ten-asset witness and the V14 loss–breadth constructions use separate interval protocols. The latter are internally checked, without an independent external audit. See the [evidence matrix](RESULTS_AND_EVIDENCE.md).

### What new results appear in V14?

V14 adds a turnover–dissipation inequality under constant impact, a constructive uniform-resource severe-loss theorem for each fixed power-law exponent 0<=p<1, an eight-target loss–breadth interval witness, and two robustness propositions for unmatched dollar flow and heterogeneous quadratic impact. Each has explicit hypotheses; the severe-loss bounds are not uniform as p approaches 1 and do not establish bounded gross-rate execution. Extra comparison paths use distinct fixed or relaxed turnover budgets.

### What does mathematical reachability mean?

A loss is reachable if an admissible trading path exists under the specified dynamics, resources, time horizon and terminal settlement. An existence theorem supplies neither a probability of that path nor a model of participants' incentives. An open feasibility cell is not proof of nonreachability.

### What changes under execution constraints?

Turnover, inventory, finite rates and rolling price bands restrict attainable paths. Necessary lower bounds exclude only the regimes covered by their hypotheses. A certified feasible path proves existence for its particular resource protocol, not an optimal boundary for all controls.

### Is this a market prediction or a trading strategy?

No. It is an idealized structural reachability study. It does not supply backtested signals, return predictions, estimated crash probabilities, a profit claim or an empirical manipulation result.

### How do I reproduce and cite the results?

Follow [reproducibility instructions](REPRODUCIBILITY.md) to run quick checks and the full certificate regeneration on Python 3.11. Cite Siyuan Ye, *When Can Markets Crash Without News?* (2026), [paper DOI 10.5281/zenodo.23444647](https://doi.org/10.5281/zenodo.23444647), for results already present in V13. Cite V14 additions using [10.5281/zenodo.23478787](https://doi.org/10.5281/zenodo.23478787), and identify the GitHub source commit for computations. The changing preprint record is also available on [SSRN](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7622079). For computations using the archived snapshot, cite [software DOI 10.5281/zenodo.23428183](https://doi.org/10.5281/zenodo.23428183), version **1.0.0rc1+git.d6e2606**, commit `d6e2606590f955a6287c6945488a080e5acab004`. Later repository documentation updates are outside that fixed archive. [CITATION.cff](../CITATION.cff) gives machine-readable details. Preprint availability does not assert journal acceptance.

## 中文和日文 / Japanese and Chinese editions

**简体中文：** 本研究讨论在基本面不变、交易金额相互配对的理想化多资产市场中，系统性下跌何时在数学上可达，以及价格冲击弹性和交易约束在什么条件下排除这种下跌。研究不预测真实市场崩盘的时间或概率。[完整中文学术译本](../translations/zh-CN/README.md)。

**日本語：** 本研究は、ファンダメンタルズが一定で、売買金額が対応する理想化された複数資産市場において、システミックな価格下落が数学的に到達可能になる条件と、価格インパクトや執行制約による障壁を検討する。実際の暴落時期や確率を予測するものではない。[日本語学術訳](../translations/ja/README.md)。

## Rights and source hierarchy

The software MIT license does not extend to the manuscript, supplemental and translated texts, figures, or research certificates. See [NOTICE.md](../NOTICE.md). Original mathematical results and full conditions reside in the English manuscript; proof scope and computational evidence are indexed in the [result map](RESULTS_AND_EVIDENCE.md). Accessible summaries are for discovery and do not enlarge the scope of verified claims.
