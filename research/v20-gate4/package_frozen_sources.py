#!/usr/bin/env python3
"""Freeze V20 Gate 3 manuscript sources for reproducible Gate 4 bilingual work.

Uses only Python stdlib and byte-for-byte source hashes; does not rebuild
mathematics or issue a scientific acceptance claim.
"""
from __future__ import annotations
import csv
import hashlib
import json
import subprocess
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
V20 = Path("submission/v20-gate3-activity-recovery")
MASTER = Path("submission/v16-three-certified-constructions/references.bib")
REGISTRY = Path("research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv")
MANUSCRIPT_SHA256 = "9d36ab61019bcb395073918c133bfc4a4cf23c32b99efd9a84c021fb7d092baa"
BIBLIOGRAPHY_SHA256 = "555df0a2e0bb6a3749cf64a144626b8f3d086c3a5d95e97ce5d31551701de0f2"
OUTPUT = ROOT / "build/v20-gate4-source-freeze"
OUTPUT.mkdir(parents=True, exist_ok=True)

def hexdigest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main() -> None:
    source = ROOT / V20 / "main.tex"
    references = ROOT / MASTER
    if hexdigest(source) != MANUSCRIPT_SHA256:
        raise AssertionError("English LaTeX source differs from frozen Gate 3 edition")
    if hexdigest(references) != BIBLIOGRAPHY_SHA256:
        raise AssertionError("The historical 33-reference V16 master differs")
    with (ROOT / REGISTRY).open(encoding="utf-8-sig", newline="") as stream:
        reader = csv.DictReader(stream)
        rows = list(reader)
    if len(rows) != 43 or len({r["ID"] for r in rows}) != 43:
        raise AssertionError("Exactly 43 original scientific obligations required")
    figures = sorted((ROOT / V20 / "figures").glob("*.pdf"))
    if len(figures) != 6:
        raise AssertionError("Exactly six scientific PDF figure assets required")
    for p in figures:
        if not p.read_bytes().startswith(b"%PDF-"):
            raise AssertionError(f"Broken figure: {p}")
    files = [
        V20 / "main.tex",
        V20 / "shared.tex",
        V20 / "README.md",
        MASTER,
        REGISTRY,
        Path("research/v20-gate3/GATE3_SCIENTIFIC_CONTENT_ACCEPTANCE_2026-11-10.md"),
        Path("research/v20-gate3/GATE3_SCIENTIFIC_SOURCE_PROOF_REVIEW_2026-11-10.md"),
    ] + [p.relative_to(ROOT) for p in figures]
    source_sha = subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    report = {
        "status": "FROZEN_FOR_GATE4_TRANSLATION_NOT_GATE4_ACCEPTED",
        "source_commit": source_sha,
        "english_main_sha256": MANUSCRIPT_SHA256,
        "original_v16_bib_sha256": BIBLIOGRAPHY_SHA256,
        "original_reference_count": 33,
        "research_item_count": len(rows),
        "figure_count": len(figures),
        "files": [{"path": str(p), "bytes": (ROOT/p).stat().st_size,
                   "sha256": hexdigest(ROOT/p)} for p in files],
    }
    (OUTPUT/"source_manifest.json").write_text(
        json.dumps(report, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8")
    archive = OUTPUT / "v20_gate4_source_snapshot.zip"
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in files:
            info = zipfile.ZipInfo(p.as_posix(), date_time=(2026, 11, 11, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(info, (ROOT/p).read_bytes())
        info = zipfile.ZipInfo("source_manifest.json", date_time=(2026, 11, 11, 0, 0, 0))
        info.compress_type = zipfile.ZIP_DEFLATED
        z.writestr(info, (OUTPUT/"source_manifest.json").read_bytes())
    with zipfile.ZipFile(archive) as z:
        assert z.testzip() is None
    print(json.dumps({"archive":str(archive),"sha256":hexdigest(archive),
                      "source_commit":source_sha,"files":len(files),
                      "research_items":len(rows)},indent=2))

if __name__ == "__main__":
    main()
