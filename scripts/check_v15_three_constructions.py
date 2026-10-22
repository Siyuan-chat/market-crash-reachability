"""Editorial and reference-integrity checks for the V15 focused working draft."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "submission/v15-three-constructions/main.tex"
BIB = ROOT / "submission/v15-three-constructions/references.bib"

def main() -> None:
    tex = SRC.read_text(encoding="utf-8")
    bib = BIB.read_text(encoding="utf-8")
    core = tex.split(r"\appendix", 1)[0]
    assert r"\end{document}" in tex
    assert tex.count(r"\begin{proof}") == tex.count(r"\end{proof}")
    assert "Proof sketch" not in tex
    for title in ("Construction I", "Construction II", "Construction III"):
        assert core.count(title) >= 1, title
    for stale in ("A1--A2", "B1--B2", "R70-20-M5", "P60-20"):
        assert stale not in core, stale
    for label in (
        "thm:barrier1", "thm:barrier2", "thm:ABC", "thm:critical",
        "thm:resource", "thm:quadratic-rate",
        "thm:finite-rate-construct", "thm:sublinear-severe",
        "eq:target-twoday", "eq:two-day-resource-target",
        "eq:two-day-index-target",
    ):
        assert r"\label{" + label + "}" in tex, label
    assert r"S_i(40)=\left(\frac34\right)^2F=\frac9{16}F" in core
    assert "Neither proves existence" in core
    assert "Theorem" in core and "uniform finite" in core
    labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    refs = set(re.findall(r"\\(?:ref|eqref|autoref)\{([^}]+)\}", tex))
    missing = refs - labels
    assert not missing, f"Unresolved LaTeX references: {sorted(missing)}"
    keys = set(re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", bib))
    cited = set()
    for raw in re.findall(r"\\cite[pt]?(?:\[[^\]]*\])?\{([^}]+)\}", tex):
        cited.update(x.strip() for x in raw.split(","))
    assert cited <= keys, f"Unresolved citations: {sorted(cited-keys)}"
    assert tex.count(r"\begin{equation}") == tex.count(r"\end{equation}")
    assert tex.count(r"\begin{figure}") == tex.count(r"\end{figure}")
    print(f"PASS V15 editorial source: {len(core.splitlines())} main lines, "
          f"{len(tex.splitlines())} total lines, "
          f"{len(labels)} labels, {len(cited)} cited keys.")
    print("NOTE: exact two-session 25% consecutive-limit witness remains UNPROVED.")

if __name__ == "__main__":
    main()
