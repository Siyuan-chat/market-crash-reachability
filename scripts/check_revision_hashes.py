"""Verify the frozen release SHA-256 manifest plus a pinned working-revision overlay.

The immutable original manifest release/SHA256SUMS remains byte-for-byte
unchanged. A working manuscript necessarily changes README/version/source
files, so the new revision is pinned *separately* in
release/SHA256SUMS_V14_R1. The overlay may only replace these explicitly
reviewed manuscript/editorial and test workflow paths. It must not override
the frozen model, data, interval certificates, historical Lean proofs,
earlier PDFs, or original release metadata.

Without the revision overlay, verify the historical manifest normally.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "release/SHA256SUMS"
REVISION = ROOT / "release/SHA256SUMS_V14_R1"

# Independently pinned CURRENT editorial updates. Do not rewrite V14-R1's
# historic overlay: it records the V14 baseline and remains immutable.
CURRENT_EDITORIAL = ROOT / "release/SHA256SUMS_V20_EDITORIAL_R1"
# The original Lean CI workflow was pinned in the V12 release manifest.
# A separate one-file manifest records this *runner-only* installation repair.
LEAN_CI_WORKFLOW = ROOT / "release/SHA256SUMS_V20_LEAN_WORKFLOW_R1"
LEAN_CI_WORKFLOW_FILES = {".github/workflows/lean.yml"}
CURRENT_EDITORIAL_FILES = {
    "README.md",
    "docs/VERSIONS.md",
    "scripts/check_documentation.py",
    "submission/README.md",
    "scripts/check_revision_hashes.py",
}

# This explicit whitelist prevents a later revision from silently masking
# changed historical certificate, data or Lean files behind an overlay.
# Current-repository navigation and documentation QA are deliberately
# allowed editorial paths; no mathematical source, certificate, archived
# figure or formal Lean proof is added to this exception list.
REVISION_FILES = {
    ".github/workflows/tests.yml",
    ".github/workflows/v14.yml",
    "README.md",
    "REPRODUCE.md",
    "CONTRIBUTING.md",
    "docs/REPOSITORY_STRUCTURE.md",
    "docs/STATUS.md",
    "docs/RESEARCH_OVERVIEW.md",
    "docs/REPRODUCIBILITY.md",
    "scripts/check_documentation.py",
    "submission/README.md",
    "data/twin_ten_asset_benchmarks.json",
    "docs/TWIN_TEN_ASSET_REVISION_V1.md",
    "docs/VERSIONS.md",
    "scripts/build_v14_resource_bound.py",
    "scripts/check_revision_hashes.py",
    "scripts/check_v14_resource_bound.py",
    "submission/v14-turnover-dissipation/README.md",
    "submission/v14-turnover-dissipation/main.tex",
    "submission/v14-turnover-dissipation/shared.tex",
    "submission/v14-turnover-dissipation/twin_conservation_figure.tex",
    "verification/twin_ten_asset_benchmarks.py",
}


def read_manifest(path: Path) -> dict[str, str]:
    entries = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line:
            continue
        parts = line.split("  ", 1)
        if len(parts) != 2 or not re.fullmatch(r"[0-9a-f]{64}", parts[0]):
            raise AssertionError(f"Invalid digest record in {path}: {line!r}")
        digest, name = parts
        if name in entries:
            raise AssertionError(f"Duplicate digest path: {name}")
        loc = (ROOT / name).resolve()
        if not loc.is_relative_to(ROOT) or not loc.is_file():
            raise AssertionError(f"Digest path absent or unsafe: {name}")
        entries[name] = digest
    return entries


# Separate pin for a mechanical entrypoint-import reduction.  The frozen
# release manifest and its original formal proof files remain unchanged.
LEAN_IMPORT_PRUNE = ROOT / "release/SHA256SUMS_LEAN_IMPORT_PRUNE"
LEAN_ENTRY = "formal/lean/MarketCrash.lean"
EXPECTED_LEAN_IMPORTS = (
    "MarketCrash.MarketCut",
    "MarketCrash.RollingRate",
    "MarketCrash.OriginalDollarTurnover",
    "MarketCrash.OriginalSecondSession",
    "MarketCrash.ThreePulseUniform",
    "MarketCrash.QuadraticRateAttainment",
    "MarketCrash.OriginalABC",
    "MarketCrash.OriginalCertificateAssembly",
)


def read_lean_import_prune() -> dict[str, str]:
    if not LEAN_IMPORT_PRUNE.exists():
        return {}
    entries = read_manifest(LEAN_IMPORT_PRUNE)
    if set(entries) != {LEAN_ENTRY}:
        raise AssertionError("Lean import overlay must contain only the aggregate entrypoint")
    expected = "".join("import " + module + "\n" for module in EXPECTED_LEAN_IMPORTS)
    actual = (ROOT / LEAN_ENTRY).read_text(encoding="utf-8")
    if actual != expected:
        raise AssertionError("Lean entrypoint must contain only the eight validated imports")
    return entries


def main() -> None:
    frozen = read_manifest(BASE)
    if REVISION.exists():
        overlay = read_manifest(REVISION)
        if set(overlay) != REVISION_FILES:
            raise AssertionError(
                f"Revision manifest paths differ: missing={sorted(REVISION_FILES - set(overlay))}, "
                f"unexpected={sorted(set(overlay) - REVISION_FILES)}"
            )
        if overlay.get("README.md") == frozen["README.md"]:
            raise AssertionError("The revision must pin a new README checksum")
        if overlay.get("docs/VERSIONS.md") == frozen["docs/VERSIONS.md"]:
            raise AssertionError("The revision must pin new version information")
    else:
        overlay = {}

    # The V20 editorial layer may override only these five already whitelisted
    # documentation/checker paths. Never allow model, data, theorem, certificate,
    # prior manuscript or proof files into this overlay.
    if not CURRENT_EDITORIAL.is_file():
        raise AssertionError("Current editorial manifest is required")
    editorial = read_manifest(CURRENT_EDITORIAL)
    if set(editorial) != CURRENT_EDITORIAL_FILES:
        raise AssertionError(
            f"Current editorial manifest paths differ: "
            f"missing={sorted(CURRENT_EDITORIAL_FILES - set(editorial))}, "
            f"unexpected={sorted(set(editorial) - CURRENT_EDITORIAL_FILES)}"
        )
    if not CURRENT_EDITORIAL_FILES <= REVISION_FILES:
        raise AssertionError("Current editorial manifest has unreviewed paths")
    lean_import_prune = read_lean_import_prune()
    # Do not alter the frozen release manifest to modernize CI. The new layer
    # may override exactly the historical workflow YAML, never a Lean proof.
    if not LEAN_CI_WORKFLOW.is_file():
        raise AssertionError("Pinned Lean CI workflow manifest is required")
    lean_ci = read_manifest(LEAN_CI_WORKFLOW)
    if set(lean_ci) != LEAN_CI_WORKFLOW_FILES:
        raise AssertionError("Lean CI overlay may pin only the lean.yml workflow")

    mistakes = []
    for name, expected in {**frozen, **overlay, **lean_import_prune, **editorial, **lean_ci}.items():
        found = sha256((ROOT / name).read_bytes()).hexdigest()
        if found != expected:
            mistakes.append((name, expected, found))
    if mistakes:
        for name, expected, found in mistakes:
            print(f"MISMATCH {name}: expected={expected}, actual={found}")
        raise AssertionError(f"{len(mistakes)} SHA-256 mismatch(es)")

    print(f"PASS: {len(frozen)} frozen baseline paths, "
          f"{len(overlay)} separately pinned working-revision files "
          f"({len(frozen.keys() | overlay.keys())} distinct tracked files)")
    print(f"Current V20 editorial overlay: {len(editorial)} whitelisted paths")
    print(f"Pinned Lean CI workflow: {len(lean_ci)} YAML file; Lean source unmodified")
    print("Original release/SHA256SUMS unchanged; no certificate hashes overridden")
    print(f"Lean entrypoint import-only overlay: {len(lean_import_prune)} pinned file(s)")


if __name__ == "__main__":
    main()
