# V20 Lean workflow dependency repair — 2026-11-06

Status: **PR validation pending; not a new mathematical formalization claim**.

## Failure mechanism

GitHub Actions run `42054219531` failed at `lake exe cache get` before the Lean kernel build: the pinned Mathlib (commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`) attempted to retrieve `leantar 0.1.15` as a release archive. Its `curl -L` download returned only **92 bytes** but still exited successfully, and `tar` failed with “This does not look like a tar archive”. This is an external binary distribution/download failure, not a proof counterexample.

Direct source inspection of pinned Mathlib `Cache/IO.lean` shows `validateLeanTar` checks `leantar --version` from `PATH` and accepts **exactly 0.1.15**, avoiding the broken archive download. GitHub source tag `digama0/leangz@v0.1.15` has a `leantar` Cargo binary and a committed `Cargo.lock`.

## Repair and acceptance

- In existing `.github/workflows/lean.yml`, compile the exact `v0.1.15` `leantar` binary with `cargo install --git ... --tag v0.1.15 --locked --bin leantar` and add its install bin directory to `GITHUB_PATH`.
- Verify the version output is exactly the required version before attempting `lake exe cache get`.
- Keep `lake exe cache get`, `lake build` and `python formal/check_proof_integrity.py` as **mandatory** steps, with `set -euo pipefail`; a failure stays RED.
- No change to Lean 4.19.0, pinned Mathlib revision, `formal/lean` source, historical certificates, theorem statements or standard-axiom checks.
- Record this workflow-only SHA-256 override in `release/SHA256SUMS_V20_LEAN_WORKFLOW_R1`, verified by `scripts/check_revision_hashes.py`, without editing the original `release/SHA256SUMS` or historic V14 overlay.

Success requires the actual remote Lean workflow to compile its existing modules **and** pass the axiom/integrity audit. If `cargo` installation or upstream Mathlib cache is unavailable, document the external blocker, **not** a false green workflow. This installation fix does not close the old-model paper-to-Lean Issues #5/#8/#40–44 or establish Gate 3 acceptance.
