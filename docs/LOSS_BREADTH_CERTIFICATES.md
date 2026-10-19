# Internally certified loss–breadth paths (V14 research extension)

This directory's executable source is [loss_breadth_certified.py](../verification/loss_breadth_certified.py).
It rebuilds six **specified**, exactly dollar-closed, two-session constant-impact
candidate trajectories using rational time segments and outward-rounded integer
interval enclosures. These are **internal computer-assisted certificates**,
not externally peer-reviewed or Lean-formalized proofs and not optimality claims.

## Shared synthetic protocol

N=10, F=eta=1, rho=0.4, T=40 (two sessions of length 20),
uniform +/-25% rolling bands on **every** asset, gross execution
share-rate cap 0.285, gross initial sale shares per asset <2.
For each case, k target assets trade at exactly the same executed-dollar
rate q(t); the 10-k compensators trade at -k*q(t)/(10-k).
The edge dollar flows are paired, and the integral of q(t) vanishes
exactly, so every individual terminal signed executed-dollar ledger closes.

**These are not the same bands as the published older k=9
certificate**, which uses 3% target bands and a 25% compensator band.

## Reproduced results (lower thresholds are conservative)

| Case | Target coverage | Certified target ordinary drop > | Certified geometric-index drop > | Paired turnover M | Certified rate upper | M cap |
|---|---:|---:|---:|---:|---:|---:|
| P50-20 | 5/10 | 22.29% | 4.0% | 2.600 | 0.216130 | 3 |
| P60-20 | 6/10 | 20.90% | 5.0% | 2.880 | 0.257224 | 3 |
| P70-10 | 7/10 | 12.60% | 3.0% | 2.660 | 0.164249 | 3 |
| R80-10 | 8/10 | **10.80%** | 3.0% | 2.850337 | 0.272696 | 3 |
| R70-15.5 | 7/10 | 15.50% | 4.0% | 2.939070 | 0.277592 | 3 |
| R70-20-M5 | 7/10 | 20.20% | 6.0% | 4.599448 | 0.262743 | **5** |

The geometric-index price decline is
1-exp(-mean-log-loss); it is **not** target-asset ordinary price loss.
The original published k=9 certificate additionally establishes
a mean log loss >0.020 with target ordinary drop 5.91%.
Its bands and controls differ from those of this table.

## Reproduce (Python 3.11, no extra dependencies)

From repository root:

    python verification/loss_breadth_certified.py --out build/loss_breadth/certificates.json

Make the output directory beforehand; or simply run the command without
--out to check every witness and print the summary. The verifier constructs
all exact rational input segments internally; no unpublished optimizer state
is needed. For each segment it integrates the scalar ODE
Sdot=-(2/5)*(S-1)+q/S by directed integer floor/ceiling Taylor enclosures
at precision Q=10^24, with maximum grid step 1/4000 and a bounded
second-derivative remainder. Its bootstrap guarantees prices stay inside
the positive strip [3/5,8/5]. On a constant-dollar-rate segment
the autonomous scalar ODE has no interior extrema beyond its endpoint
hull. Dollar-rate share caps and cumulative sales use interval lower
price bounds. The geometric-index result is a rational product check,
with no floating-point logarithm in its proof-critical path.

Scope: These exact bounded-control verifications provide explicit existence
witnesses within the synthetic model. They do not prove that unlisted
loss/breadth targets are unreachable, that the resource budgets are
minimal, or that the model captures actual exchange price limits.
The code still needs independent external mathematics/code audit.
