> Original-baseline technical mapping with dated historical checkpoints. Current manuscript: [V14](../docs/VERSIONS.md); current formal scope: [manifest](ORIGINAL_RESULT_MANIFEST.md). Historical pending statements do not describe current acceptance.

# Theorems 3.1–3.2: proof-completion and adversarial Lean audit (2026-10-16)

Status: **proof obligations specified; no new kernel-certified theorem in this document.** Canonical source is `paper/main.tex` (English V12 Final). Keep PR #10 Draft.

## Verified, but restricted, entry points

- `ContinuousWeakBVPriceSegment.potential_eq_primitive` derives aggregate price-potential dynamics by summing the **per-asset** weak Stieltjes price law.
- `ContinuousWeakBVPriceSegment.potential_nonnegative_of_visited_elasticity` and `no_all_asset_decline_of_visited_elasticity` establish the 3.1 analogue for continuous weak-BV solutions, without a separately postulated a.e.-FTC identity.
- `ContinuousWeakBVPriceSegment.no_systemic_crisis_of_visited_elasticity` establishes the 3.2 analogue for the same class, with elasticity only on attained price values.
- `OrderedAtomicJumpTrace` supplies physical finite ordered atomic execution **when a feasible trace is given**; `CountablePhysicalClosure` preserves the barrier under strictly positive pointwise limits of feasible finite physical prefixes.

These are **not** proof that every original M1–M5 admissible path is in one of these restricted classes.

## Blocking Lean obligations, in dependency order

### Gate A — original-control representation (model fidelity)

Construct an explicit mapping from **every** original M1–M5 admissible BV execution (for all original time horizons) to a positive, no-short, signed-dollar-ledger-preserving completed operational graph. The mapping must record finite total variation, nondecreasing executed-dollar measures, original initial benchmark state, per-asset terminal dollar closure, and recovery. No new price-potential inequality or terminal price assumption may be a field.

**Negative tests:** a path with infinitely many accumulating atom times; a purely singular-continuous nonatomic control; simultaneous edge atoms for which a convenient ordering would violate an intermediate share inventory. The latter must not be incorrectly declared admissible just because its terminal signed-dollar sum is zero.

### Gate B — physical price response on the completed graph

Derive the per-asset nonlinear coordinate increments from the primitive physical marginal settlement equation, including recovery over elapsed **physical** time and no recovery during instantaneous atom filling. Prove global composition across countable jumps and nonatomic segments, not merely individual pulses.

**Negative tests:** replacing an ordered physical pulse by the affine accounting interpolation; interpreting the measure ledger identity alone as a nonlinear price equation; admitting a discontinuous price leap without any physically feasible positive intermediate flow.

### Gate C — analytic endpoint identity without an extra hypothesis

For a globally absolutely continuous operational graph, show `J(u) = exp (rho * physicalTime u) * potential (coordinate ∘ prices u)` is locally absolutely continuous and satisfies the appropriate FTC endpoint identity. Alternatively, derive an **integral** aggregate potential identity, bypassing a.e. differentiation entirely, as is already achieved for `ContinuousWeakBVPriceSegment`; then prove it is induced by the original physical model. Do **not** infer endpoint monotonicity solely from an a.e. derivative sign for a generic BV function: a Cantor-type singular contribution is a counterexample to that inference.

### Gate D — attained-price localization

Derive continuity of each asset price on the **completed physical execution graph**, including internal values during jumps. Show each radial value from benchmark `F` to an observed terminal price is attained on that graph. Apply elasticity `e ≥ 1` (3.1) or `e ≥ 2` (3.2) **only on the actual model-attainable price set**, not globally on all positive prices. Existing continuous-segment localization is a reusable lemma, not the all-BV bridge.

### Gate E — full original theorem statements

State two top-level Lean theorems quantifying over exactly the M1–M5 admissible executions, parameters, horizons, and original positive threshold / coverage conventions; prove 3.1's no-full-decline and 3.2's crisis exclusion through Gates A–D. Review any finite-cardinality integer `k` representation against `k = ⌈αN⌉` and its boundary cases, including `k=N`, `δ>0`, and the original zero-net-terminal-dollar condition.

## Acceptance commands and reporting

```bash
cd formal/lean
lake exe cache get
lake build
cd ../..
python formal/check_proof_integrity.py
python scripts/check_hashes.py
```

Record exact branch SHA and CI run URL, theorem names and full statement signatures, permitted axioms (`propext`, `Classical.choice`, `Quot.sound`), absence of `sorry`/`admit`/custom `axiom`, and whether each Gate A–E is proved or merely assumed. A successful build of existing declarations does not change the original 0/16 full-result acceptance count. Do not change the manuscript, claim new original-result completion, or mark PR ready for review until faithful all-path equivalence is established.
