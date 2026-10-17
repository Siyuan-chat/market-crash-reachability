# D01: Proposition 7.6 original-scope correspondence

Source: `paper/main.tex`, `prop:certified-v7` and Appendix
`app:v7certificate`. This is the final numbered result in the execution queue.

The required witness has exactly ten assets, nine falling targets,
F=eta=1, rho=2/5, two sessions of length 20, rolling target bands
plus/minus 3 percent and compensator bands plus/minus 25 percent.
Its actual initial inventory must be two shares per asset, its actual
paired turnover must be below 3, each actual gross share-sales integral
below 2, and its actual systemic crisis at breadth 9/10 above 1/50.
All terminal executed-dollar ledgers must vanish exactly. The same nine
targets must close at 97/100 and 9409/10000. All these properties must
hold on one absolutely continuous original physical execution.

| Obligation | Source-to-kernel correspondence |
|---|---|
| Exact plateau | The original quadratic polynomial and rational root bracket have locally compiled Lean root-isolation proofs; decimal approximations are not treated as equalities. |
| Original interval certificate | The 80,000-step integer fixed-point replay has a completed Lean kernel check and interval/ODE soundness proofs. The final resource argument uses the equivalent mixed enclosure below; the experimental full resource-row computation is not claimed as completed evidence. |
| Same actual compensator | A positive global actual ODE solution has been constructed; its latest compiled refinement preserves every microstep box of every block on that same trajectory. The same-trajectory microstep alignment and global physical consequences have compiled locally. |
| Equivalent mixed resource enclosure | A five-theorem bootstrap bridge has compiled and passed its standard-axiom audit: existing global Lipschitz bound and endpoint boxes give a coarse box; the true AE ODE and a field bound on that coarse box imply a sharper local Lipschitz bound by FTC, hence a refined box. The 798 coarse rational certificates and final 200 dense microsteps have been instantiated on the actual trajectory. The final retained data includes the original day-two reference row at step 40,000; its literal identity and all 801 checkpoints have been reproduced exactly. This argument does not assume the local bound it proves. |
| Cash closure and true turnover | Actual paired-dollar primitives and exact target/compensator closure have compiled proofs. A separate actual 18-edge physical integral bound below 2.984 has compiled and passed its six-declaration standard-axiom audit; the final witness uses this actual integral. |
| Physical witness and initial inventory | The independent actual seller-incidence integral bounds below two, exact two-share initial state and strict positivity of all prefix inventories have compiled and passed an eight-declaration standard-axiom audit. They use continuous Y>=3/4 and the genuine target bounds; the original AC physical factory now instantiates these with the same certificate trajectory and all rates/rolling bands. |
| Strict crisis and rate bracket | Exact endpoint log bounds and a universal physical lower-rate certificate have local proofs. The actual full-witness conclusion has been assembled. The additional infimum bracket uses the arbitrary finite-network AC session interface; local canonical compilation and its two-declaration standard-axiom audit passed (`build/formal/d01-resource-rows/resume-canonical.exit=0`), and no equivalence with a separately defined BV-path feasible set is claimed. |
| Original numerical regressions | `scripts/run_checks.py full` passed all eight original commands and regenerated-certificate byte identity (`build/formal/d01-original-full-tests/result.json`, exit 0; `build/logs/full_summary.json`). No numerical assertion has been relaxed. The exact JSON SHA-256 is `354c7797c1e25ebee143d04d11e23ec92cb93214b7333eed7fcd91dd0493c18f`. |

Status: LEAN_PASS. Official full build and all-1,224-declaration standard-axiom audit passed. Four exact-SHA workflows are required before original-result acceptance. A separate SHA-256 acceptance gate was removed by the latest user instruction.
The manuscript's more precise displayed enclosure bounds must be
distinguished from the weaker thresholds in the numbered proposition:
for example a pointwise bound by 0.284481 alone does not establish a
strict supremum bound below 0.284481.

## Canonical physical correspondence

All names below are in `MarketCrash.OriginalCertificate` unless qualified otherwise.

| Original clause | Actual proof on the same constructed data |
|---|---|
| Unconditional witness and original physical law | `certificateActualData_exists`, `CertificateActualData.session`, `.piece`, `.path`; the public theorem takes no certificate-validity assumption |
| Initial two shares, actual gross sales, all-prefix no short | `CertificateActualData.initial_two`, `.sales`, `certificateInventory_seller_sum`, `certificateInventory_no_short`; shares use actual buyer/seller incidence and marginal execution prices |
| Both target closes and all rolling bands | `CertificateActualData.target_closes`, `.rolling_bands`, relative to the same actual day-one close |
| Strict actual crisis and full-time gross cap | `CertificateActualData.crisis`, `.gross_bound_all`; the latter includes time zero |
| Paired dollars counted once | `certificateTurnover_actual_paired_integral` integrates the actual 18 directed-edge rates once |
| Exact ledger closure and fixed-market conditions | `CertificateActualData.fixed_conditions` and the actual path factory |
| Entire numbered result | `MarketCrash.proposition_7_6_original` in `lean/MarketCrash/OriginalCertificateAssembly.lean:1579` |
| Additional strict minimum-rate bracket | `certificate_minimum_rate_bracket`, for the arbitrary finite-network AC-session fixed-market feasible set, with lower margin 0.0441 and the same upper witness |
