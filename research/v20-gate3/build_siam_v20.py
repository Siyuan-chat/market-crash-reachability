#!/usr/bin/env python3
"""Build the V20 *working draft* against the real SIAM class and 33-source V16 bibliography.

This is a formatting/citation reproducibility check, not a Gate 3 mathematical
acceptance test and not permission to release or replace the historical PDFs.
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
V20 = ROOT / "submission/v20-gate3-activity-recovery"
V16_BIB = ROOT / "submission/v16-three-certified-constructions/references.bib"
SIAM_ZIP = ROOT / "third_party/siam/siamonline_250211_complete.zip"
BUILD = ROOT / "build/v20-gate3-siam"
WORK = BUILD / "work"
VALID_SIAM_ZIP_SHA256 = {
    "45477e268578328bfaeb56f53f319a0d6e8b88e5394da29413e15c076a6a40ab",
    "2d74fc697977dbbd1283ec814eb57777be701c76a9325fbdf754ba9abf7a3e98",
}

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(command: list[str], stem: str, cwd: Path) -> None:
    log_path = BUILD / f"{stem}.txt"
    with log_path.open("w", encoding="utf-8") as log:
        result = subprocess.run(command, cwd=cwd, stdout=log,
                                stderr=subprocess.STDOUT, timeout=300)
    if result.returncode:
        tail = log_path.read_text(errors="replace").splitlines()[-24:]
        print("\n".join(tail), file=sys.stderr)
        raise RuntimeError(f"{' '.join(command)} failed: {log_path}")

def main() -> None:
    for binary in ("pdflatex", "bibtex"):
        if not shutil.which(binary):
            raise SystemExit(f"{binary} unavailable (install TeX Live first)")
    if not SIAM_ZIP.is_file() or sha(SIAM_ZIP) not in VALID_SIAM_ZIP_SHA256:
        raise SystemExit("SIAM complete template ZIP missing or digest mismatch")
    if not V16_BIB.is_file():
        raise SystemExit("GitHub V16 33-entry bibliography missing")
    # Exact source-identity check: the full 33-entry master must be the
    # frozen V16 bibliography, not merely any file with 33 keys.
    expected_bib_sha256 = "555df0a2e0bb6a3749cf64a144626b8f3d086c3a5d95e97ce5d31551701de0f2"
    if sha(V16_BIB) != expected_bib_sha256:
        raise SystemExit("V16 reference master changed; review source identity")
    bib = V16_BIB.read_text(encoding="utf-8")
    keys = set(re.findall(r"(?m)^@\w+\{([^,\s]+),", bib))
    if len(keys) != 33:
        raise SystemExit(f"Original V16 references must contain 33 entries; saw {len(keys)}")
    tex = (V20 / "main.tex").read_text(encoding="utf-8")
    cites = set()
    for expr in re.findall(r"\\cite(?:t|p|alt|alp|author|year|yearpar)?(?:\[[^]]*\]){0,2}\{([^}]+)\}", tex):
        cites.update(k.strip() for k in expr.split(","))
    missing = sorted(cites - keys)
    if missing:
        raise SystemExit(f"Missing references in original V16 bibliography: {missing}")
    if "\\IfFileExists{siamonline250211.cls}" not in tex:
        raise SystemExit("The V20 draft no longer declares its SIAM mode")
    if not V20.joinpath("shared.tex").is_file():
        raise SystemExit("Missing V20 shared author macros")
    BUILD.mkdir(parents=True, exist_ok=True)
    if WORK.exists():
        shutil.rmtree(WORK)
    w = WORK / "v20-gate3-activity-recovery"
    w.mkdir(parents=True)
    for source in ("main.tex", "shared.tex"):
        shutil.copyfile(V20 / source, w / source)
    shutil.copytree(V20 / "figures", w / "figures")
    (WORK / "v16-three-certified-constructions").mkdir()
    shutil.copyfile(V16_BIB, WORK / "v16-three-certified-constructions/references.bib")
    with zipfile.ZipFile(SIAM_ZIP) as z:
        for item in ("siamonline250211.cls", "siamplain.bst"):
            (w / item).write_bytes(z.read(item))
    run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
         "-file-line-error", "-halt-on-error", "main.tex"], "pdflatex-1", w)
    run(["bibtex", "main"], "bibtex", w)
    for num in range(2, 7):
        run(["pdflatex", "-no-shell-escape", "-interaction=nonstopmode",
             "-file-line-error", "-halt-on-error", "main.tex"],
            f"pdflatex-{num}", w)
        text = (w / "main.log").read_text(errors="replace")
        unresolved = bool(re.search(
            r"There were undefined references|Citation .* undefined|"
            r"Label\(s\) may have changed|Rerun to get cross-references right",
            text))
        if not unresolved and num >= 3:
            break
    else:
        raise RuntimeError("SIAM refs did not converge after 6 passes")
    text = (w / "main.log").read_text(errors="replace")
    for issue in (r"Overfull \\hbox", r"Overfull \\vbox", r"Missing character:",
                  r"There were undefined references", r"Citation .* undefined"):
        if re.search(issue, text):
            raise RuntimeError(f"SIAM PDF log contains issue {issue!r}; see {w/'main.log'}")
    pdf = w / "main.pdf"
    if not pdf.is_file() or pdf.stat().st_size < 50000:
        raise RuntimeError("No substantive SIAM PDF produced")
    shutil.copyfile(pdf, BUILD / "main.pdf")
    shutil.copyfile(w / "main.bbl", BUILD / "main.bbl")
    shutil.copyfile(w / "main.log", BUILD / "main.log")
    pdfinfo = shutil.which("pdfinfo")
    pages = None
    if pdfinfo:
        meta = subprocess.check_output([pdfinfo, str(pdf)], text=True)
        match = re.search(r"(?m)^Pages:\s*(\d+)", meta)
        if match:
            pages = int(match.group(1))
    result = {
        "status": "SIAM_V20_WORKING_DRAFT_BUILD_ONLY",
        "template_sha256": sha(SIAM_ZIP),
        "v20_main_sha256": sha(V20 / "main.tex"),
        "v16_bib_sha256": sha(V16_BIB),
        "v16_entry_count": len(keys),
        "cited_reference_count": len(cites),
        "siam_class_used": True,
        "pdf_sha256": sha(pdf),
        "pdf_size": pdf.stat().st_size,
        "pages": pages,
        "passes": num,
        "no_unresolved_references": True,
        "no_overfull_boxes": True,
        "gate3_accepted": False,
    }
    (BUILD / "build_report.json").write_text(
        json.dumps(result, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(json.dumps(result, indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
