# Uniform rolling-band loss–breadth witnesses

**Scope:** A separate set of hypothetical ten-asset, two-session mathematical
market experiments. This directory is deliberately separate from the original
nine-target, 3%/25%-band certificate and its historical proof files.

The interval checker covers 12 constructed controls from the Phase 3/Phase 4
research. For each, it verifies full-time positive-price/rate/band envelopes,
gross sale-share budget, exactly closing executed-dollar flow in each group,
strict terminal target-price and geometric-market-index inequalities, and the
gross paired-dollar turnover cap. It uses only Python 3.11 standard-library
integer/fraction arithmetic in the proof-critical path.

The 12 cases include two **relaxed-resource** families. Such cases cannot be
used as feasible evidence under the original budget M<3.

## Reproduce

From repository root:

    python verification/loss_breadth/certify_loss_breadth.py
    python verification/loss_breadth/check_paper_sync.py

This writes outward-rounded interval records, exact rational schedules and
summary tables to build/loss_breadth/. Github Actions also publishes these
generated JSON outputs as a build artifact.

Optional, with scipy installed:

    python verification/loss_breadth/independent_ode_audit.py

This independent numerical integration is not a second interval proof.
It uses DOP853/Radau and checks the results inside the exact enclosures.

## Exact controls and provenance

- Phase 3: all 7 control schedules are visible directly in
  certify_loss_breadth.py as finite-decimal rational segment parameters.
- Phase 4: five longer (80- or 160-bin) exact rational schedules are stored
  compactly as a base64/zlib-encoded JSON array in phase4_schedules.b64.
  This is lossless source storage rather than a solver-generated optimum.
  Each q12 integer is an **exact** dollar rate in units 10^-12; the final
  bin is adjusted exactly so each target executed-dollar ledger closes.
  The checker expands and exports the readable decoded_phase4_schedules.json.
- The search/optimizer histories used to discover these schedules are not
  needed for mathematical verification; the verifier starts from *frozen
  deterministic controls*, and failure of a search would not prove exclusion.
- Original research package snapshots: Phase 3 and Phase 4, 18 October 2026,
  archived separately; this repository path is the curated repeatable source.

## Auditing limitations

The scalar equation on each constant-rate interval is

    dS/dt = -(2/5)*(S-1) + q/S.

The checker propagates fixed-point integer enclosures with scale 10^25,
time step at most 1/4000, directional floor/ceil rounding, case-specific
whole-strip bounds on |S'|, |f_S| and |S''|, and an inductively verified
bootstrap strip S in [3/5,8/5]. Solutions of a scalar autonomous ODE are
monotone on a constant-control interval, so its endpoint-hull bounds
apply to the entire trading interval. Reference prices for day two are
the interval-enclosed day-one closes. Each group is homogeneous and
the complete paired-dollar transaction graph supports one-directional
cross-group dollar flow. The gross per-share cap is checked **before netting**.

These are internally reviewed computer-assisted existence witnesses,
not Lean-verified or externally audited certificates. The software
cannot establish global optimality, impossibility of excluded targets,
or empirically likely exchange-wide crashes.
