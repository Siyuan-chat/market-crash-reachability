> Historical technical record. Applies to its named source revision; see [current versions](../docs/VERSIONS.md) and the current evidence matrix. Retained at this path for provenance and compatibility.

# Phase 3 — a.e. physical BV-response bridge and completed-graph obligations

**Research source:** English V12 Final, Assumption M1–M5 and Theorems 3.1/3.2.  
**Accepted base on main:** Phase 2 merged through PR #7, 138 declarations kernel-checked on the branch before merging.  
**Historical Phase 3 development:** [PR #9](https://github.com/Siyuan-chat/market-crash-reachability/pull/9). No theorem at this checkpoint was a whole-BV manuscript theorem. Subsequent original-scope acceptance is recorded in the [completion matrix](WHOLE_PAPER_LEAN_COMPLETION.md).

## Verified intermediate milestone

**Latest verified mathematical source:** commit `c619ba26805facb0cf5d5cf2a87383fdd0d517a4`, [Lean CI #38861075606](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38861075606) **passed 159/159 declarations**, full kernel/axiom audit, without unfinished proofs or additional axioms. Previous exact-head checkpoints passed [153/153](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38860430862) and [151/151](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38859956202). The number counts formal statements at their precisely tested SHAs, **not** manuscript theorem coverage.

## Completed mathematical upgrades (159 milestone)

### 1. Input clock for general Stieltjes cumulative controls

For a monotone right-continuous executed-dollar cumulative flow `Z_e(t)`, with a **positive unit-conversion scale** `λ` (time units per executed-dollar unit), define

`u(t) = t + λ Σ_e Z_e(t)`.

The file `StieltjesVariationClock.lean` derives, for any ordered times `s≤t`,

- `u(t)-u(s) = (t-s)+λ Σ_e (Z_e(t)-Z_e(s))`;
- `t-s ≤ u(t)-u(s)` for `λ≥0`;
- `λ·μ_e((s,t]) ≤ u(t)-u(s)` for every edge `e`, where `μ_e` is its **actual** Lebesgue–Stieltjes measure;
- `u` is monotone.

The clock `u` can jump when trading contains atoms. These inequalities **do not** construct the completed graph, prove an inverse is 1-Lipschitz, or define execution order within simultaneous atoms. The clock estimate alone does not establish those claims.

### Clock inverse on its actual image (new 159 milestone)

`StieltjesVariationClock.lean` additionally proves the total clock is **strictly** increasing for `λ≥0`. It constructs a unique inverse `t(u)` **only on the clock's actual image**, proves left inversion and order preservation, and establishes

`0 ≤ t(u₂)-t(u₁) ≤ u₂-u₁` for ordered clock-image points `u₁≤u₂`,

together with `λ·μ_e((t(u₁),t(u₂)]) ≤ u₂-u₁` for every directed trading edge. This is the precise nonexpansion estimate needed before constructing a completed inverse graph.

**It is not yet a map on the whole operational interval:** at jump atoms, `u(t)` skips intervals, and multiple simultaneous edge jumps require the ordered internal execution protocol. These arcs, their physical solutions, and preservation of inventory/positive prices remain unconstructed.

### 2. Genuine a.e. nonlinear physical response for a Lipschitz operational solution

`OperationalClockAE.lean` defines a physical market with globally Lipschitz `t(u)`, cumulative `Z_e(u)`, real prices `S_i(u)`, shares and per-asset executed-dollar ledgers. On the interval `[a,b]`, it enforces positive prices, no-short constraints and nonnegative speeds/rates. It imposes only the *physical* marginal price/share/ledger equations **almost everywhere** in operational time, never a transformed-coordinate invariant.

Lean derives:

`d/du Phi(S_i(u)) = Σ_e B_ie Z'_e(u) - rho·t'(u)·S_i(u)(S_i(u)-F)/g(S_i(u))` almost everywhere,

and, using the graph-incidence cancellation,

`d/du H(u) = -rho·t'(u)·Σ_i S_i(u)(S_i(u)-F)/g(S_i(u))` almost everywhere.

With the **global** elasticity-1 condition, it proves that `d/du {exp(rho·t(u))·H(u)}≥0` almost everywhere. It also proves price differentiability a.e. via a Lipschitz/Rademacher result, true-time and edge-dollar rate agreement a.e., and finite total share/edge variation from Lipschitz regularity.

This is a **genuine physical-model-to-coordinate a.e. chain-rule proof for the typed operational solution**. It does **not** yet show that *all original BV controls admit such a solution/parameterization*. That inclusion is the mathematically central unfinished part.

## Historical analytical gap: a.e. derivative versus endpoint comparison

A nonnegative derivative almost everywhere does **not** imply that a continuous real function is monotone. The Cantor function is the standard counterexample. Absolute continuity is needed.

`OperationalClockAEComparison.lean` is verified at the **153** and **159** checkpoints and establishes the exact mathematical bridge **conditional** on

`integral_a^b J'(u) du = J(b) - J(a)`, where `J(u) = exp(rho·t(u))·H(u)`.

Under this explicitly stated FTC identity, `J'(u)≥0` a.e. and `H(a)≥0` yield `H(b)≥0`.

**This is not yet the manuscript's BV potential barrier:** the FTC identity must be **proved** from the completed graph's absolute continuity and positive-price response, rather than installed as a new market assumption. In particular, global Lipschitzness of the individual physical components alone is not a proof term for that identity in Lean; composition/local derivative bounds and the a.e. FTC still need a kernel-checked development with the pinned dependencies.

## Model-equivalence obligations at this checkpoint

1. **From original control to completed graph.** For the full finite-variation, piecewise-continuous controls and finitely many marginally settled pulses, construct a parameterized common graph. Fill every jump explicitly, preserving the directed edge execution order and nonnegative cumulative rates; verify physical time is nondecreasing. An inverse-graph existence theorem and correct handling of co-jumps are still absent.
2. **Physical response solution.** This obligation required a weak/measure price-share-ledger solution for those controls, including singular-continuous transactions and ordered jump arcs, and a proof that `S_i, theta_i, X_i` meet the `AEOperationalClockSegment` hypotheses with suitable extensions. The generalized price-coordinate equation required derivation from that solution.
3. **Absolute continuity and FTC.** Prove the integrating factor `J` is locally absolutely continuous and satisfies its a.e. derivative integral identity. The verified a.e. derivative proof, inverse-clock estimates and the conditional FTC theorem are not by themselves the original all-BV endpoint comparison.
4. **Model side conditions.** Prove strict positive prices at *every* internal graph point, no-short inventory throughout each jump, finite total variation, correct physical-time matching and exact terminal **per-asset** dollar closure for the whole constructed path.
5. **Attainable-price curvature.** Extend the radial/visited-price argument and the log-Jensen argument to the complete original path, including internal jump prices and all concatenations. The current multi-segment barrier uses stronger global elasticity premises.
6. **Original paper theorem scope.** Only after all gates can the full M1–M5 quantifiers in manuscript Theorems 3.1/3.2 be declared Lean-verified. Other numbered results and Proposition 7.6's interval certificate are separate verification projects.

## Proof-scope qualifications

- The cited audit found no unfinished proofs or custom axioms; generalized-price conservation was derived from the physical equations.
- One-edge Stieltjes, operational smooth and a.e. Lipschitz statements have distinct scopes.
- A conditional FTC lemma does not establish a complete physical BV barrier.
- Axiom-audit success applies to the exact tested Git SHA.
