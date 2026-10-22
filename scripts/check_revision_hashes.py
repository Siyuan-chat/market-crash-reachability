"""Verify historical SHA-256 evidence plus an explicit V16 documentation overlay.

The original release/SHA256SUMS and release/SHA256SUMS_V14_R1 stay
unchanged; their historical checks are not rebaselined to new manuscript
content. release/SHA256SUMS_V16_DOCS contains only five allowed
current-documentation/integrity-checker overrides. It cannot mask edits
to mathematical models, certificates, data, archived PDFs, or Lean proofs.
"""
from __future__ import annotations

from hashlib import sha256
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "release/SHA256SUMS"
REVISION = ROOT / "release/SHA256SUMS_V14_R1"
V16_DOCS = ROOT / "release/SHA256SUMS_V16_DOCS"
PINNED_V14_OVERLAY_SHA256 = "ec9e4ba2b8c21c60425bc9a8139a15b02b6ea9f10aec73897fc4ae703f55ed47"
V16_DOC_FILES = {
    "README.md",
    "docs/VERSIONS.md",
    "submission/README.md",
    "scripts/check_documentation.py",
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
        if sha256(REVISION.read_bytes()).hexdigest() != PINNED_V14_OVERLAY_SHA256:
            raise AssertionError("Historical V14-R1 manifest changed unexpectedly")
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

    if V16_DOCS.exists():
        if not REVISION.exists():
            raise AssertionError("V16 docs require the pinned V14-R1 historical overlay")
        v16_docs = read_manifest(V16_DOCS)
        if set(v16_docs) != V16_DOC_FILES:
            raise AssertionError(
                f"V16 docs manifest paths differ: "
                f"missing={sorted(V16_DOC_FILES - set(v16_docs))}, "
                f"unexpected={sorted(set(v16_docs) - V16_DOC_FILES)}"
            )
        for name in V16_DOC_FILES:
            if name not in overlay or overlay[name] == v16_docs[name]:
                raise AssertionError("V16 documentation must override an actual V14-R1 record: " + name)
    elif (ROOT / "submission/v16-three-certified-constructions/main.tex").exists():
        raise AssertionError("V16 working manuscript requires a separate V16 docs hash manifest")
    else:
        v16_docs = {}

    lean_import_prune = read_lean_import_prune()

    mistakes = []
    for name, expected in {**frozen, **overlay, **v16_docs, **lean_import_prune}.items():
        found = sha256((ROOT / name).read_bytes()).hexdigest()
        if found != expected:
            mistakes.append((name, expected, found))
    if mistakes:
        for name, expected, found in mistakes:
            print(f"MISMATCH {name}: expected={expected}, actual={found}")
        raise AssertionError(f"{len(mistakes)} SHA-256 mismatch(es)")

    print(f"PASS: {len(frozen)} frozen baseline paths, "
          f"{len(overlay)} pinned V14-R1 files and {len(v16_docs)} V16 documentation overrides "
          f"({len(frozen.keys() | overlay.keys() | v16_docs.keys())} distinct tracked files)")
    print("Frozen release and historical V14-R1 hash manifests verified unchanged; no certificate hashes overridden")
    print(f"Lean entrypoint import-only overlay: {len(lean_import_prune)} pinned file(s)")


if __name__ == "__main__":
    main()
