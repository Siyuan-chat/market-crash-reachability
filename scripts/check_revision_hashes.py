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

# This explicit whitelist prevents a later revision from silently masking
# changed historical certificate, data or Lean files behind an overlay.
REVISION_FILES = {
    ".github/workflows/tests.yml",
    ".github/workflows/v14.yml",
    "README.md",
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

    mistakes = []
    for name, expected in {**frozen, **overlay}.items():
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
    print("Original release/SHA256SUMS unchanged; no certificate hashes overridden")


if __name__ == "__main__":
    main()
