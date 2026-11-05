# Gate 2 / Construction III: second independent rational interval audit (2026-11-05)

**Result: PASS in a second internally developed interval implementation.** This is independent in arithmetic, transcendental-function enclosure, and inverse-root bracketing, **not** an external third-party review or a global Gate 2 clearance.

The independent executable proof script is `verify_c1_independent_rational.py`. It does **not** call/import the V17 `certify_five_targets.py` or `mpmath.iv`. Its intervals have exact-rational grid endpoints at 10^-65, with outward integer floor/ceiling rounding for each arithmetic operation. It bounds log using power-of-two scaling and `ln z=2 atanh((z-1)/(z+1))`, atan using a Machin identity and alternating Taylor series, and sqrt(3) using an exact integer square-root bracket. All transcendental series include explicit geometric absolute remainders. Both endpoint inverses are bounded by separate monotone bisections of the buyer/seller primitive on [0.5,1.34], not point estimates.

The executable checker verifies the 19 edge events between each of five targets and its own compensator; five compensator-only transfers of exact dollar amount 0.04; two-session rolling 25% price bands; all intermediate price positivity (prices along each individual flow-completed edge are monotone in the certified state domain); C1 one-direction activity; individual exact-dollar closure by opposite endpoint ledger signs and IVT; true gross seller-side share inventories; and the prescribed uniform-in-session time allocation under the gross share-rate cap.

Certified conservative displayed enclosures (use executable exact bounds, not rounded decimal display, as proof objects):

| Test | Independent enclosure / result |
|---|---|
| Root c | 0.76065368494358 < c < 0.76065368494359 |
| Left ledger | between 1.17277194227e-14 and 1.17277195023e-14, strictly >0 |
| Right ledger | between -3.94850867350e-14 and -3.94850866588e-14, strictly <0 |
| Total paired-dollar turnover | 11.26162582014 ... 11.26162582017, strictly <11.261627 |
| Maximum per-node gross share rate | <0.132717934375 <0.133 |
| Individual gross sale shares | all <2 with explicit min-price bounds |
| Five terminal compensator prices | each strictly between 1.2 and 1.23 |
| Targets day1/day2 | exactly 3/4, then exactly 9/16 |
| Geometric index | strictly <0.84, since (9/16)*1.23 <0.84² |

The local full-length source and rational-bound JSON were also checked and retained in the associated research checkpoint. A second algorithm verifying a preselected witness is evidence of an **independent internal cross-check**, not mathematical optimality, independent discovery, or external certification. Do **not** infer a largest possible number of two-session limit-down targets or reuse V16's seven-target upper bound.

**Gate impact:** Construction III's existing INTERNAL_INTERVAL status is strengthened to INTERNAL_INTERVAL_CROSSCHECK_2. Gate 2 is still OPEN pending Construction I/II specific numeric interval certificates and all Handoff mathematical acceptance requirements. Gate 1 unresolved tasks are not silently removed.
