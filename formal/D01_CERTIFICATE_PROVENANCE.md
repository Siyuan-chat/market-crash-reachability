# Proposition 7.6 certificate provenance

The manuscript and original numerical certificate are unchanged by D01.
The original outward-rounded fixed-point generator is
`verification/certify_streak_interval.py` (SHA-256
`a72d17e4c489ebf2ed6744e30cf550a7638c450451847612c00969a4a20029a2`).
Its original JSON certificate is `data/certificates/final_interval_certificate.json`
(SHA-256 `354c7797c1e25ebee143d04d11e23ec92cb93214b7333eed7fcd91dd0493c18f`).

The exact plateau is isolated as a real root of
`101600000000*h^2 - 97138000000*h - 6646157699`, strictly between
`1.02020225507905` and `1.02020225507908`. No decimal approximation is substituted for that root.
The integer interval scale is `10^32`, the time step `1/2000`, and the original
price replay has 80,000 steps and 801 checkpoint pairs.

`MarketCrash/RationalIntervalChecker.lean` checks the original price replay by
Lean kernel reduction. `IntervalODEEnclosure.lean` supplies the actual ODE
existence, positivity, outward enclosure and same-trajectory microstep soundness.
The final resource argument combines 798 coarse endpoint/FTC certificates with
the final 200 dense microsteps. Its retained terminal resource data starts at step
79,800, with the original step-40,000 row retained separately as the
second-session reference. The local derivative estimate is proved from the actual AE ODE on a
previously established coarse box, so the refinement does not assume its own
conclusion.

The actual paired-dollar integral is bounded analytically by 2.984. Actual
gross sales are bounded by 2 using the same trajectory and its proved positive
floor. The uniform gross-rate cap 0.284481 implies the numbered result
`v_used < 0.285`. These proofs do not assert the proof outline's stronger strict
supremum `<0.284481` or compensator-sales `<1.880` as Lean-certified results.
The original numerical regression retains those stronger assertions unchanged.

The input reproduction tool is provenance, not an axiom or proof oracle.
All concrete constants used in the theorem are checked by the Lean kernel;
no generated JSON validity predicate is assumed by the public theorem.

Status: final reproduction tool and official full-build/axiom-audit/CI evidence
are recorded after the source freeze in `WHOLE_PAPER_LEAN_COMPLETION.md`.

From the repository root, reproduce the exact committed Lean input tables with
Python 3.11 (standard library only):

```text
python formal/tools/reproduce_certificate_inputs.py --project . --out build/formal/reproduced-certificate-inputs
```

The tool checks the original JSON identity, all 801 committed checkpoint pairs,
the retained 201-row terminal Lean fragment, and the exact step-40,000 reference row. The default reads the official modules
under `formal/lean/MarketCrash`; it does not require any Working source.
The original regression command is `python scripts/run_checks.py full` in the
project's scientific Python environment. Exact output digests and full theorem
acceptance are recorded in the single completion matrix.

A separate SHA-256 acceptance gate was cancelled by the latest user instruction;
the historical input digests above identify the original certificate sources.
