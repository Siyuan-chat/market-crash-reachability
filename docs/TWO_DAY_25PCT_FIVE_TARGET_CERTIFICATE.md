# Two consecutive 25% lower-limit closes in a ten-asset model

**Research status (2026-10-22):** internally authored, outward-rounded **80,000-step interval certificate**; independently coded high-accuracy numerical ODE audit. External implementation and mathematical review are pending. This proves existence for five targets, **not** optimal coverage.

## Exact model and control

Let N=10, F=eta=1, rho=2/5, T=40, with two model sessions of length 20. All ten assets use the same symmetric **±25% rolling price band** referenced to each asset's preceding close. Initial prices equal F. Trades satisfy dX_i=S_i d(theta_i), dS_i=-(2/5)(S_i-1)dt+d(theta_i), dollar pairing, no short sales and X_i(40)=0 asset by asset.

Five identical target prices x(t) and five identical compensator prices y(t) are used. Define x as the continuous piecewise-linear interpolation of:

| t | x(t) |
|--:|:--|
| 0 | 1 |
| 5/2 | h |
| 35/2 | h |
| 20 | 3/4 |
| 24 | 187/200 |
| 36 | 187/200 |
| 40 | 9/16 |

The plateau h is the unique root in (1.15451858960596, 1.15451858960597) of

\[
32\,000\,000h^2-30\,800\,000h-7\,094\,049=0.
\]

Put u(t)=x(t)(x'(t)+(2/5)(x(t)-1)), and define the compensator price as the unique positive solution of

\[
y'=-(2/5)(y-1)-u/y,\qquad y(0)=1.
\]

Each of the five targets executes +u dollars per unit time, matched with -u dollars in its corresponding compensator. Reverse the transfer direction where u is negative. These trades are **absolutely continuous**; no pulse or instantaneous execution is used in this third construction.

## Exact dollar closure

A target's terminal dollar ledger is

\[
X_x(40)=[x(40)^2-1]/2+(2/5)\int_0^{40}x(t)[x(t)-1]dt.
\]

The integral is exactly computable over the six linear/constant stages; the stated quadratic equation is precisely X_x(40)=0. Hence terminal target dollar closure is **exact**, not numerical. Pairing and the five symmetric compensator flows then give X_y(40)=-X_x(40)=0 for each compensator.

## Computer-assisted admissibility

The outward-rounded fixed-point checker uses exact fractions to bracket h and a 1/2000-step interval Taylor/Euler enclosure to propagate y(t) across 80,000 steps, proving a positive bootstrap strip, price bands on **every intrastep interval**, sale-inventory requirements and a gross share-rate cap. An independent RK4 checker reproduces the trajectory without relying on the certificate integration routine.

Conservative interval enclosures:

| Property | Verified enclosure or cap |
|---|---:|
| y(20) | 1.1770660 < y(20) < 1.1792779 |
| y(40) | 1.2514766 < y(40) < 1.2535249 |
| y, first-session range | (0.7659099, 1.1797780) |
| y, second-session range | (1.0429619, 1.2540250) |
| Per-asset gross executed-share rate | < 0.285 |
| Cumulative sales per target | < 1.618 < 2 |
| Cumulative sales per compensator | < 1.673 < 2 |
| Paired-dollar turnover M | < 13.323 < 14 |
| Ten-asset geometric price index | G(40)/G(0) < 0.84 |

The five target assets therefore close exactly at the model's lower price limits on both sessions, x(20)=3/4 and x(40)=9/16. The cumulative ordinary target-asset fall equals **43.75%**, the ten-asset equally weighted geometric-index fall exceeds **16%**, and C_{0.5}(40)>-log(0.84)>0.174. These are **deterministic model conclusions**, not empirical crash explanations.

For orientation only, an independent numerical reconstruction gives y(20)≈1.1781530, y(40)≈1.2524942, G(40)/G(0)≈0.8393617 and M≈13.32217.

## Independent necessary obstruction k ≤ 7

This is a model-wide bound, not based on the candidate control. Let V(t)=sum_i S_i(t)^2. Paired-dollar trades leave V unchanged, and between executions

\[
\dot V=-2\rho(V-\sum_iS_i).
\]

As sum_i S_i ≤ sqrt(10V), a path starting at V(0)=10 satisfies V(t)≤10 throughout, also with flow-completed pulse controls.

Suppose k named targets close at 3/4 and 9/16 on the first and second sessions respectively. On the first day every price lies in [3/4,5/4], and

\[
s(s-1)\le s^2/2-15/32.
\]

Because each non-target also has S_i^2≥9/16 and V≤10,

\[
\sum_{i\in J}S_i(S_i-1)\le(35-3k)/16
\]

at every first-session time. During the second session every target lies in [9/16,15/16], so S_i(S_i-1)≤-15/256. Its exact terminal dollar closure implies

\[
\int_0^{40} S_i(S_i-1)\,dt
=\frac{1-(9/16)^2}{2\rho}=\frac{875}{1024}.
\]

Summing over k targets and both 20-unit sessions therefore gives

\[
875k/1024\le20\{(35-3k)/16-15k/256\},
\quad\text{or}\quad1183k\le8960.
\]

Hence k≤7. The coverage bound is **necessary**, not sufficient: attainability of six or seven consecutive lower closes remains unproved.

## Reproduction

From the repository root:

    python verification/two_day_25pct_five_assets.py --out data/two_day_25pct_five_assets_certificate.json
    python verification/audit_two_day_25pct.py

The interval checker uses standard-library exact rational and outward-rounded integer operations and refuses optimized Python with disabled assertions. Its generated JSON is evidence to audit, not a substitute for the constructive mathematical argument. This research branch preserves the V15 version currently under the author's review and the older V14 baseline.
