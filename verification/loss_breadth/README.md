# Loss–breadth reachability: fixed controls and interval checker

This directory records two sets of **research-only, internally interval-checked**
constructive controls in an abstract 10-asset market. It is not a calibration of any
real exchange, an optimal policy, or an externally/formally certified interval theorem.
Published V13 proofs and certificates are unchanged.

## Model

Initial and fundamental prices F=1, impact g(S)=1, recovery rho=2/5, two
20-unit sessions (T=40); **uniform symmetric +/-25% rolling bands for every
asset in every session**. Each asset's terminal signed dollar ledger integrates
to zero exactly; matched paired-dollar flow is conserved at every instant.
Gross per-asset executed-share rate <0.285 and per-asset gross shares sold <2.

Primary fixed budget: paired dollar turnover M<3. Resource sensitivity separately
increases **only** turnover to M<4, M<5 or M<7. Never combine the relaxed
witnesses with fixed M<3 matrix success counts. The original 90%-coverage,
5.91% ordinary-loss witness in Section 7 had *different*, asymmetric target
(+/-3%) and receiving asset (+/-25%) bands; compare its endpoints only with
that protocol caveat.

## Verify, no optimization software required

```sh
python verification/loss_breadth/verify_all.py
```

This uses **only Python's standard library**, exact fraction controls and
integer outward-rounding interval updates. It checks prices over entire
constant-flow segments (scalar autonomous monotonicity), strict rolling bands
including the second-day reset, gross share-rate cap, cumulative sales,
matched dollar turnover, terminal dollar closure and exact rational
geometric-index inequalities. Controls and scripts have SHA-256 hashes in
`SHA256SUMS.json`; `verified_results_manifest.json` gives a compact index
of results, thresholds and independently reconstructed numerical quantities.

Optional independent floating-point reconstruction (not a rigorous independent
proof, requires SciPy and NumPy):

```sh
python verification/loss_breadth/verify_all.py --audit
```

The proof-critical checker was originally written as a separate research
exploration, and has **not** been externally audited or Lean-formalized.
Re-executing it establishes deterministic reproducibility under the stated
scalar ODE comparison and directed-rounding assumptions; do not claim proof of
optimality or of nonreachability for unfilled matrix cells.

## Evidence classes

`OLD` in the 24-cell matrix = one published original k=9, d=5.91%
path qualifies for smaller breadth/loss targets under a weaker uniform-band
model; no new certificate for that old path is included here.

`P3` = Phase-3 internally interval-checked controls give a witness for the
cell; all rows need positive market-average log loss to qualify as systemic,
not merely falling target prices.

`OPEN` means current evidence does **not** determine feasibility under M<3,
never mathematical impossibility.

### Provenance

The two source research packages were produced on 2026-10-18. The original
phase-3 certificate suite and phase-4 checker are preserved with only the
following small operational changes: output paths use this directory instead
of /mnt/data; a no-op NumPy import was removed from the proof-critical
phase-4 checker; the compact exact controls were extracted from the preserved
phase-4 certificate JSON outputs. The phase-4 checker still contains an
optional legacy CLI referencing optimizer inputs; `verify_all.py` instead
loads its exact rational controls and calls `verify()` directly.
All candidate paths were rechecked in October 2026 against the source
packages before inclusion. Their numerical endpoints in the comparison table
are *illustrative*, not interval-certified point estimates.

**Proof-critical execution:** invoke the documented `verify_all.py` runner with an unoptimized Python interpreter. The runner refuses `python -O` or `PYTHONOPTIMIZE` so that its interval-certifier modules' assertions cannot be bypassed by the normal reproduction workflow. The hashed original proof-critical modules and exact controls remain byte-for-byte unchanged.
