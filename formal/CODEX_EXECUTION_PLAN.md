# Codex execution plan: complete the remaining 15 Lean results

**Repository:** Siyuan-chat/market-crash-reachability  
**Work branch:** formal/phase4-absolute-continuity-and-ordered-jump-graphs (Draft PR #10)  
**As-of baseline:** 2026-10-17; last fully green commit b0b042265c2ae41b1ea70e686c420fd8d3c97771.  
**Original-paper gate:** 1/16 accepted (Proposition 7.1); 15 numbered results remaining.  
**Authoritative source:** paper/main.tex (English V12 Final); the exact text is indexed by formal/THEOREM_MAP.md.

This file is an **execution queue**, not a research proposal. Codex is instructed to **implement and verify the numbered manuscript results**, not merely design new proof abstractions. It supersedes the task *order* in historical Phase 2–4 worklogs and formal/DIRECT_PAPER_PROOF_ROUTE.md; it does not override the actual manuscript or verified mathematical facts.

## Non-negotiable delivery contract

1. **The unit of delivery is one complete original numbered Theorem/Proposition.** A helper, a smooth-only analogue of an all-BV claim, an assumed price-response law, a numerical experiment, or a theorem with additional hypotheses does not count. Proposition 7.1 is already accepted and must not be reimplemented.
2. **Match the literal source quantifiers.** Preserve N, k=ceil(αN), positive price domain, fixed or asset-specific fundamentals, impact regularity, resilience, all permissible times and controls, physical inventory and no-shorting, marginal-price settlement, directed paired dollars, terminal per-asset X_i(T)=0, and any resource/rate/band or uniformity claims **where they occur**. A result may be proved for a larger class if every original path is rigorously shown to belong to it. Do not require irrelevant conditions for conditional endpoint identities.
3. **Model fidelity is a proof obligation.** For arbitrary original continuous finite-variation controls, the M2 physical marginal execution law → integrated per-asset normal form requires the appropriate nonlinear BV/Stieltjes chain rule. Do not assume that identity as a new unrelated premise and call Theorems 3.1/3.2 done. M5 permits finitely many physical flow-completed instantaneous pulses: arbitrary countable-atom graph completion is **not** an original-paper prerequisite. Handle singular-continuous execution if it is admitted by the original language; do not silently reduce all paths to absolutely continuous ones.
4. **Lean kernel, not assertion or favorable CI labels, decides a proof.** No sorry, admit, axiom, custom unsound axioms, opaque proof shortcuts or weakened restatements. Required foundational axioms only: propext, Classical.choice, Quot.sound. Register every theorem exactly once in formal/lean/MarketCrash/AxiomAudit.lean.
5. **Local debugging first.** Do not push one-line tactical experiments just to use GitHub Actions as the compiler. Use the pinned Lean 4.19.0/Mathlib toolchain, local file build, Lean diagnostics and appropriate Mathlib lemmas. Run complete project build/audit locally before pushing; the four CI workflows are the final same-SHA acceptance.
6. **Do not abandon a result after the first passing helper.** Continue until the entire numbered result and all its original clauses pass or document a genuine mathematical/technical blocker with file:line, exact statement and failed obligation. If genuinely blocked, mark BLOCKED and proceed to an independent result rather than adding unrelated lemmas.
7. **No silent manuscript edits.** If an original statement seems mathematically false, incomplete or stronger than its proof, present a concrete counterexample/precise missing premise and a proposed correction; do not automatically weaken paper/main.tex or count the adjusted statement as the original result.
8. Preserve historical research files unless deletion is unambiguously safe. No new general graph model, LLM-driven rewriting, mass refactoring, renamed theorem APIs or unnecessary framework work. Keep PR #10 Draft; do not merge without the user's express instruction.
9. Only use the completion labels **TODO → IN_PROGRESS → LEAN_PASS → CI_PASS → PAPER_ACCEPTED**. A genuine blocker is **BLOCKED**, with evidence. For PAPER_ACCEPTED require an explicit line-by-line manuscript-to-Lean scope audit and the exact latest SHA with all four CI checks passing.
10. **Continue autonomously through this queue.** The user has authorized implementing the remaining proofs; do not ask for confirmation after each result. Report actual accepted numerator, new commit SHA, completed original result, and exact next blocker. Do not claim all 15 will necessarily be provable without changes; honesty and proof soundness take precedence over a schedule.

## Start here: deterministic environment and source audit (T00)

- Fetch the existing branch and inspect git status; preserve unrelated uncommitted work. Work from the latest branch head, **not** a historical SHA. Treat b0b0422 as a reproducibility checkpoint, not a checkout instruction if newer work exists.
- Read paper/main.tex, formal/THEOREM_MAP.md, formal/WHOLE_PAPER_LEAN_COMPLETION.md, formal/MODEL_FIDELITY.md and the modules used by the next theorem. Annotate a short manuscript-versus-Lean correspondence before coding.
- Reuse formal/lean/MarketCrash.Conservation, PhysicalSmoothMarket, PhysicalPulse, BoundedVariationLedger, StieltjesExecution, WeakBVPriceBarrier, WeakBVFiniteExecution, WeakBVOriginalCrisis, CrisisParameters and CrisisQuantile as appropriate. Do not rewrite already kernel-checked proofs.
- Confirm local tools; working directory for Lean is formal/lean:

        cd formal/lean
        lake exe cache get
        lake build
        cd ../..
        python formal/check_proof_integrity.py
        python scripts/check_hashes.py

- During edits, use local targeted compilation (for example cd formal/lean && lake build MarketCrash.Conservation), then full lake build, then audit. Inspect build/formal/axioms.log if needed.
- Update release/SHA256SUMS **once after all file edits in the current result are stable**, using Python hashlib.sha256 over exact UTF-8/raw file bytes for the changed, already-pinned paths; then run python scripts/check_hashes.py. Avoid manually invented or stale hashes. Keep its scope aligned with existing release policy.
- If verification/certificate code changes, also run python scripts/run_checks.py quick; for the full 7.6 certificate run python scripts/run_checks.py full. Do not claim that Python regression alone is Lean proof.
- Before each PAPER_ACCEPTED transition, assert: local build PASS, axiom audit PASS, release hashes PASS, exact proof statement matches the original, and all four checks **lean / verify / siam / translations** PASS on **the same commit SHA** (use GitHub/gh APIs to check the SHA). Record that SHA and proof theorem name in formal/WHOLE_PAPER_LEAN_COMPLETION.md and formal/THEOREM_MAP.md. Update other status documents if they contradict the authoritative tracker.

### Baseline reuse (already proved; do not re-open)

- Proposition 7.1 original terminal endpoint is complete: proposition_7_1_original_endpoint plus proposition_7_1_single_compensator; its conditional product, quantile and exact severity statements are kernel-certified.
- Proposition 7.5 has an **instantaneous** cut capacity lemma market_cut_instantaneous_bound in formal/lean/MarketCrash/Conservation.lean; it is **not** the full proposition.
- Finite physical pulses, matched dollar accounting, continuous weak BV potential inequalities and crisis kth-largest semantics have verified kernels; the *primitive continuous BV physical dynamics-to-weak price equation* remains unproved.
- Historical countable atomic/limit proof modules were deliberately removed from this work branch. Do **not** recreate them as a prerequisite.

## Dependency map — fifteen original numbered results

All statuses below refer to original-paper **full acceptance**, not helper proof counts.

| Task | Original result | Status at baseline | Primary dependencies | Expected workload / core gate |
|---|---|---|---|---|
| A01 | Proposition 7.5 | PARTIAL → IN_PROGRESS | conservation, absolute-continuous price response | Finish full market cut, turnover/rate bound, empty complement, and k/m specialization |
| A02 | Proposition 6.1 | TODO | scalar ODE comparison and price-band model | Rate-only floor, crisis bound, necessary speed, reset-session caveat |
| A03 | Proposition 7.2 | TODO | A02 rate comparison | One-session closing rate, D-session max and integer streak bound |
| B01 | **Proof bridge** (not a numbered result) | BLOCKING | physical M2, BV chain rule, finite pulses | Faithful original finite-BV path → weak normal-form solution; must not count separately |
| B02 | Theorem 3.1 | TODO | B01, existing potential barriers | All-original-path no-all-down and full-coverage non-crisis |
| B03 | Theorem 3.2 | TODO | B01, B02, radial elasticity/quantiles | Any breadth, any time, local admissible-price elasticity ≥2 |
| B04 | Theorem 5.1 | TODO | B01 and physical execution inventory | Dollar, share sale and individual inventory/resource lower bounds |
| B05 | Proposition 7.4 | TODO | B01 / exact price-ledger primitive | Positive above-F excursion; first-session budget and D bound |
| B06 | Theorem 7.3 | TODO | paired dollars + correct session path semantics | Second-session all-asset lower-limit obstruction with asset-specific g_i, F_i, ρ_i |
| C01 | Proposition 4.2 | TODO | finite physical pulses, curvature | Explicit 3-pulse all-down construction; exact O(h³), positivity and dollar closure |
| C02 | Proposition 4.3 | TODO | finite physical pulses, crisis statistic | Explicit 2-pulse partial-coverage construction, Taylor coefficient, terminal closure |
| C03 | Theorem 6.3 | TODO | C01 and continuous physical control | AC fully dollar-closed bounded continuous trading, arbitrary caps and initial positive inventory |
| C04 | Theorem 6.2 | TODO | A02, C03 | Exact quadratic universal bound **and** attained order / Θ(√δ) |
| C05 | Theorem 4.4 | TODO | exact constant-impact flow, physical control | Sharp critical δ, impossible ≥ endpoint, feasible approaching controls and nonattainment |
| C06 | Theorem 4.1 | TODO | B03, B04, C02, C05; p-family | All A/B/C regimes, fixed resource bounds and p=0 δ-independent budgets |
| D01 | Proposition 7.6 | TODO | certificate assets; B/C financial fidelity | Actual N=10 two-day rational interval witness verified and linked to a Lean theorem |

**Total:** 16 work items: 15 rows corresponding to the 15 remaining original numbered results, plus the non-counted shared physical-model bridge B01. At any time accepted = 1 + number of PAPER_ACCEPTED **numbered-result** rows.

## Detailed execution orders and acceptance

### A01 — Finish Proposition 7.5 (do this FIRST; no partial delivery)

**Source:** paper/main.tex, prop:market-cut, eqs. market-cut-instant, cut-required, cut-necessary, cut-special.  
**Reuse:** Conservation.market_cut_instantaneous_bound, trading_sum_zero, marginal dollar flow, relevant interval integral bounds.

Implement in one narrowly scoped Lean result family:
1. Carry instantaneous ∣sum over J of Xdot_i∣ ≤ v * min(sum J prices, sum complement prices) to **almost every execution time** of every paper-admissible **absolutely continuous** session; prove the connection to the derivative of genuine executed-dollar ledgers, not merely an arbitrary vector.
2. With S_i(t) ≤ F_i and strict terminal descent for each i∈J, integrate the **physical price-response law**. Show positive K_J,d := sum[Φ_i(start)−Φ_i(end)] > 0 and net matched dollars received by Jᶜ ≥ K. Preserve direction/sign.
3. Prove paired turnover M_d ≥ K and v ≥ K/[τ_d * sum_{Jᶜ} U_j,d] **when denominator positive**, with the paper's nonempty receiving capacity; do not insert a positivity restriction absent from the original except what follows from original assumptions.
4. Show if Jᶜ is empty, simultaneous strict decreases on a session entirely below benchmark are impossible.
5. Complete the **constant-impact k identical decliners / m compensators / rolling upper-band** specialization with the original d≥2 bound: v ≥ (k/m) F(q^(2(d−1))−q^(2d))/[2η τ_d (1+β_c,+)^d].
6. Prove the full proposition for any finite J and applicable asset-specific F_i,g_i. Do not mark accepted after step 1 or 3.

**PASS gate:** all five original formula/edge clauses are formalized and audited at the exact manuscript scope; entire CI green.

### A02 — Proposition 6.1 (independent fast path)

**Source:** prop:rate-band. Use g(S)≤G on the *entire admissible price region*, rho>0, gross cap and (when stated) fixed bands.
- Scalar comparison: S_i(t) ≥ F−G*v/rho*(1−exp(−rho*t)), all t∈[0,T].
- Positive combined S_floor = max{F(1−β_-), F−G*v/rho*(1−exp(−rho*T))}; crisis ≤ log(F/S_floor) at any t≤T, all α.
- Necessary v bound for δ>0; a one-session lower band excludes δ above −log(1−β_-).
- Separate hypothetical reset-by-previous-close D-session product bound and summed log-loss bound; **not** a fixed benchmark ban.
- No substitution of constant g unless the clause actually assumes it. Proof for all controls covered by the rate cap, not just one sample path.

### A03 — Proposition 7.2

**Source:** prop:rolling-rate. Reuse A02 rather than building new ODE machinery.
- Exact one-session positive-part lower bound for v starting at arbitrary s>0 and ending at (1−β)s in τ.
- D sessions with s_d=F q^(d−1), rho, eta, common τ: required maximum over 1≤d≤D.
- Perpetual rate-only floor and its **integer D** upper bound, only under η v < rho F; handle log q<0 correctly when dividing.
- No false claims of sufficiency for market-wide matching, dollar closure or bands.

### B01 — Minimal indispensable all-BV physical bridge (non-counted)

**Source:** Assumption M1–M5 and eqs. level-dynamics, pulse-flow, normal-form. Do not solve the general arbitrary-countable-atom problem.
- Define a minimal faithful type/projection of **piecewise-continuous finite execution variation**, including singular-continuous continuous pieces and **finitely many** flow-completed pulses. Record actual price positivity, edge-dollar monotonicity, marginal physical cash ledger and shares/inventory.
- Prove the physical M2 nonlinear finite-variation/Stieltjes change-of-variables yields **for each asset**, on every continuous execution piece:
  Φ(S_i(t))−Φ(S_i(a)) = sum_e B_i,e [Z_e(t)−Z_e(a)] − rho * integral_a^t S_i(u)(S_i(u)−F)/g(S_i(u)) du.
- Supply/justify any technical recovery-integrand continuous extension on [a,b] currently carried as a field in ContinuousWeakBVPriceSegment. **Do not** promote an assumed identity to a theorem by renaming its field.
- Join the finitely many existing physically verified FlowCompletedPulse events, with *within-pulse attained prices*, and prove **every** original admissible execution projects to the proven finite trace type; distinguish full economic path validity from the price-only projection used for barrier proofs.
- Preserve local attainable-price elasticity meaning. Audit a precise assumption map. Do not require artificial global e≥1 or e≥2.

### B02/B03 — Full Theorems 3.1 and 3.2

Use B01 plus existing ContinuousWeakBVPriceSegment.potential_nonnegative_of_visited_elasticity, RadiallyElasticWeakBVPriceReachable.no_all_asset_decline, RadiallyElasticWeakBVPriceReachable.no_systemic_crisis_at_breadth and kth-loss lemmas.

**B02:** N≥2; for all original M1–M5 paths, times and physically attained prices with e≥1, no all-asset S_i(t)<F; strict positive full-coverage crisis threshold excluded.

**B03:** for all original paths, N≥2, alpha∈(0,1], any t∈[0,T], e≥2 only on the original admissible price range: C_alpha(t) ≤ 0; prove terminal threshold exclusion. Do not replace “all admissible paths” by smooth-only paths or extra terminal-time assumptions.

### B04 — Full Theorem 5.1

**Source:** thm:resource, eqs. resource-lower, share-bound.
- For every original crisis-attaining terminal path and k=ceil(alpha*N), s=F exp(−δ), prove M≥−kΦ(s)=k∫_s^F u/g(u)du.
- Define Ψ(S)=∫_F^S 1/g(u)du with correct positivity, prove sum_i H_i^-≥−kΨ(s).
- With terminal dollar closure/no short and qualifying initial holdings H_i, prove ∫_s^F (F−u)/g(u)du ≤ F H_i for **every qualifying asset**.
- Cover finite flow-completed pulses and continuous BV physical accounting, not sample trajectories. These are **necessary, not sufficient**.

### B05 — Full Proposition 7.4

**Source:** prop:streak-precondition.
- From original physical price law and X_i(T_D)=0, derive rho∫ S(S−F)/g(S) = ∫_{s_D}^F u/g(u)>0.
- Prove above-F prices occur on a set of **positive physical-time measure** (not merely an isolated execution pulse) under the stated regularity.
- If sessions d≥2 stay at/below F, upper-bound the positive contribution solely in session 1 by rho*tau_1*max_{[F,U1]}u(u−F)/g(u).
- Constant g=η and s_D=F q^D algebraic formula, and bound on D when 2H_+<1. Carefully handle logarithm sign.
- Explicitly retain terminal closure and first-session-only excursion assumptions.

### B06 — Full Theorem 7.3

**Source:** thm:no-second-global.
- Allow **asset-specific** positive g_i, rho_i, F_i; first-day closes q_i F_i and second-day entire bands (1+β_i,2,+)q_i≤1.
- Show pairing and sign of below-F recovery forbid **all** assets ending session 2 strictly below their individual first-day close.
- Include finite physical pulses if admitted by session model; do not invent global curvature or terminal-ledger conditions.
- No rate cap is needed, so theorem cannot implicitly depend on v>0 or an unrelated time bound.

### C01 — Full Proposition 4.2

**Source:** prop:three-pulse.
- For every N≥2 with local C³ response and e(F)<1, **construct** positive physically admissible three-pulse paired-dollar path with per-asset X_i(T)=0, finite inventory and no short sales, all S_i(T)<F.
- Produce an actual zero-sum u with every u_i nonzero. Prove Taylor remainder O(h³) with quantified neighborhood and uniform constants, c=g(F)/F², r=exp(−rho*T/2), coefficient (1−e(F))*c²*u_i²*r*(1−r²)/2.
- Show strict positive losses for small h under original time/horizon conditions; account for within-pulse physical price trajectory and exact dollar closure.

### C02 — Full Proposition 4.3

**Source:** prop:two-pulse.
- Construct paired-dollar h*u and −h*u at time 0,T for k<N with at least k positive u components and sum u=0; check positive prices, finite inventory, pulse ordering, per-asset dollar closure.
- Under e(F)<2 and r=exp(−rho*T)<2−e(F), derive the **exact stated** mean log-loss coefficient c²*h²*(1−r)*(2−e(F)−r)*sum u_i²/(2N)+O(h³).
- Prove both k-coverage and positive mean loss => actual C_alpha(T)>0 for small h. Do not stop after positive coefficient alone.

### C03 — Full Theorem 6.3

**Source:** thm:finite-rate-construct.
- Given any N≥2, T>0, v>0, beta_±>0, *any positive initial share holding* and local C³ g with e(F)<1, construct a **continuous, absolutely continuous** executed control.
- Check actual positive-price ODE, matched-dollar network, per-asset gross share-rate ≤ v at every required time/a.e., prices **strictly inside** the one-session bands, zero terminal X_i(T) for **each asset**, share inventory at all times without shorts, and all terminal prices <F.
- Show C_1(T)>0 via its true kth-largest log-loss definition. Small attainable loss allowed; no assertion of a fixed large δ for arbitrarily small v.
- Do not reuse a jump construction without proving its rate-smoothed version is exactly closed.

### C04 — Full Theorem 6.2

**Source:** thm:quadratic-rate.
- Under g≡η and paired dollars plus gross-share-rate cap, derive for **all N≥2, α, T** the manuscript's exact coefficient: C_alpha(T)≤(ηv/(F rho))² * [d_T−rho*T*exp(−rho*T)+d_T²/(2(1−b_T)²)], where d_T=1−exp(−rho*T), b_T=ηv*d_T/(F rho)<1.
- Show the quadratic O(v²) upper behavior, and **use C03** to prove attained order for fixed N,T, positive band widths and v→0, yielding v_*(δ)=Θ(√δ) as δ↓0.
- This theorem is not fully accepted until both the upper bound and the attained-order/minimum-rate claims are proved. Correct handling of terminal closure optionality is required.

### C05 — Full Theorem 4.4

**Source:** thm:critical.
- Under g≡η, k=N, prove critical δ_crit=log[√N/(1+(√N−1)exp(−rho*T))].
- Universal exclusion of every positive-price path with δ≥δ_crit.
- **Construct actual admissible terminal-dollar-closed finite-turnover paths** for every 0<δ<δ_crit with sufficiently large finite inventory.
- Prove sharpness, nonattainment and supremum — not just the upper bound. Preserve exact N,T quantifiers and positive intermediate prices.

### C06 — Full Theorem 4.1 (assemble LAST in the A/B/C group)

**Source:** thm:ABC, g_p(S)=η(S/F)^p.
- Market A p=2: every M1–M5 admissible path has C_alpha≤0; use B03.
- Market B p=1: **existence** of small positive terminal systemic crisis for k<N **and** finite uniform severity upper bound for any fixed per-asset starting inventory H0, independent of control sequence; use C02 and B04 if valid.
- Market C p=0: for fixed N≥2,k<N, choose a **finite T and finite M0,H0 independent of δ** so every δ>0 has an admissible positive-price, terminally dollar-closed path with C_alpha(T)>δ, M≤M0 and H_i^-≤H0. Assert correct order of quantifiers and no uniform claim as N→∞.
- Existing results with δ-dependent budgets do **not** close this theorem.

### D01 — Full Proposition 7.6: rigorous N=10 certificate (start evidence audit EARLY)

**Source:** prop:certified-v7, Appendix v7certificate. **Reuse** verification/certify_streak_interval.py, verification/verify_consistency.py, data/certificates/final_interval_certificate.json, docs/REPRODUCIBILITY.md. The Python certificate is valuable research prior, **not a Lean theorem**.

- Fix exact data: N=10, k=9, F=η=1, rho=0.4, sessions 20+20, target bands ±3%, receiver bands ±25%, target knots (0,1),(2.3,h),(17.7,h),(20,0.97),(22.3,0.995),(37.7,0.995),(40,0.9409).
- Prove exact root isolation for 101600000000 h²−97138000000 h−6646157699=0, with the source's rational bracket. Do not promote decimal approximations to exact equalities.
- Verify, under exact outward-rounded arithmetic and a **sound interval propagation/ODE enclosure**, the unique positive compensator solution of y'=-0.4(y−1)−9u/y with u=x[x'+0.4(x−1)], bootstrap positivity and all 80,000 intervals at step 1/2000 (or a more efficient **mathematically equivalent** certificate).
- Establish all nine target first/second-day closes, all per-asset terminal X_i(40)=0, actual executed rates, turnover counted once, gross share-sales/inventory and both-day bands, and the strict 0.020 crisis threshold from exact log/rational bounds.
- Original target: **Lean kernel verifies both the certificate checking algorithm's soundness and this concrete rational certificate**, or an equivalently rigorously justified checker **with a formal Lean soundness bridge**. Merely rerunning Python, emitting JSON, comparing floating-point ODEs, or assuming a predicate 'certificate_valid' is NOT enough for 'entire proposition formally checked in Lean'.
- Once C04 is proved, validate the paper's separate **0.044<v_*<0.285** bracket as an additional consequence if included in the target paper-completion scope. Do not confuse the constructive Proposition 7.6 witness with a globally optimized v_*.
- Run the paper's full original numerical tests without relaxing any assertion. Commit the actual proof witness/data and its provenance.

## Fast execution strategy without misleading acceptance

**Primary serial queue:** A01 → A02 → A03 → B01 → B02 → B03 → B04 → B05 → B06 → C01 → C02 → C03 → C04 → C05 → C06 → D01.  
**Safe parallelization when Codex supports isolated worktrees:** Begin an independent D01 *certificate asset/Lean checker* worktree immediately; B01 physical BV bridge can proceed in a different worktree alongside A01–A03. C01/C02 constructions can proceed separately after shared physical pulse APIs are stable. Integration of MarketCrash.lean, AxiomAudit.lean, release/SHA256SUMS and global progress docs is serialized by **one integrator**, after local proof success, to avoid conflicts.

For each accepted item:
1. Copy its literal paper statement into a nearby comment; create **one canonical full-result theorem** named for that paper result; supporting private lemmas are allowed only if strictly needed.
2. Compile targeted Lean file locally until it succeeds, using existing lemmas rather than a new general framework.
3. Compile project, run axiom/integrity checker, release hashes, relevant Python checks; audit original quantifier correspondence.
4. Commit code **and** status/docs/checksum changes in one result-scoped commit; push. Poll **all four same-SHA GitHub Actions** until success/failure; fix and rerun, never finish at failed CI.
5. Change the row to PAPER_ACCEPTED only after all checks and manuscript scope pass. Record exact theorem name, code path, SHA, CI run URLs, fulfilled clauses and any paper caveats. Update count in trackers and PR description.
6. Move immediately to the next unblocked row; if blocked, keep evidence, continue an independent item and report no false count increase.

## Final exit criteria: 16/16

- Exactly 16 manuscript substantive numbered results have individually traceable original-scope theorem acceptance. Theorem 1.1 is an informal overview and does not require its own 17th proof.
- Every local Lean theorem and concrete certificate required by those results is kernel/verified-checker sound; 100% project theorem audit with no custom axioms/sorry/admit. All source files and report/certificate versions are pinned and reproducible.
- Four GitHub CI checks all SUCCESS **on the exact final commit**, not separately successful earlier SHAs.
- Reconcile formal/FORMALIZATION_STATUS.md, formal/THEOREM_MAP.md, formal/WHOLE_PAPER_LEAN_COMPLETION.md, formal/README.md and PR #10. Only after the actual gate is complete may formal/check_proof_integrity.py's historical whole_paper_formalized false output be changed to true as a **derived acceptance fact**, never as a substitute for the 16 checks.
- Publish a compact final manifest per paper result: theorem name, exact assumptions, Lean source, SHA, kernel audit result, numerical certificate provenance when applicable. Keep PR Draft until user authorizes merge.

**Do not report success if fewer than 16 original results are actually accepted.** Report completed results and exact unresolved obligations truthfully, even if a hard step needs extensive mathematical proof.
