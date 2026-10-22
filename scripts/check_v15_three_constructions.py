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
    abstract = tex.split(r"\begin{abstract}", 1)[1].split(r"\end{abstract}", 1)[0].strip()
    introduction = tex.split(r"\section{Introduction}\label{sec:intro}", 1)[1].split(
        r"\section{Model and Systemic Drawdown Criterion}", 1)[0].strip()
    introduction_prose = re.sub(
        r"\\begin\{equation\}[\s\S]*?\\end\{equation\}", "", introduction)
    introduction_prose = re.sub(r"\\cite[pt]?\{[^{}]+\}", "", introduction_prose)
    intro_words = len(introduction_prose.split())
    abstract_words = len(abstract.split())
    assert 450 <= intro_words <= 530, ("Introduction misses ~500-word target", intro_words)
    assert 125 <= abstract_words <= 155, ("Abstract misses concise target", abstract_words)
    assert "?" not in abstract, "Abstract must be declarative"
    assert r"\bibliographystyle{unsrtnat}" in tex, "Reference order style changed"
    assert introduction.index("Gennotte and Leland") < introduction.index(
        "We therefore consider a deliberately minimal market"), "Literature must precede model"
    assert introduction.index("We therefore consider a deliberately minimal market") < introduction.index(
        "The key mathematical tool"), "Model motivation must precede mathematical tool"
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
    print(f"PASS V15 abstract {abstract_words} words; introduction {intro_words} words")
    print(f"PASS V15 editorial source: {len(core.splitlines())} main lines, "
          f"{len(tex.splitlines())} total lines, "
          f"{len(labels)} labels, {len(cited)} cited keys.")
    print("NOTE: exact two-session 25% consecutive-limit witness remains UNPROVED.")

if __name__ == "__main__":
    main()
