"""Static mathematical-claim and editorial audit for independent V16 manuscript."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/"submission/v16-three-certified-constructions/main.tex"
BIB=ROOT/"submission/v16-three-certified-constructions/references.bib"

def main():
    tex=SRC.read_text(encoding="utf-8")
    bib=BIB.read_text(encoding="utf-8")
    main=tex.split(r"\appendix",1)[0]
    abstract=tex.split(r"\begin{abstract}",1)[1].split(r"\end{abstract}",1)[0].strip()
    intro=tex.split(r"\section{Introduction}\label{sec:intro}",1)[1].split(
        r"\section{Model and Systemic Drawdown Criterion}",1)[0].strip()
    intro_no_display=re.sub(r"\\begin\{equation\}[\s\S]*?\\end\{equation\}","",intro)
    intro_no_cites=re.sub(r"\\cite[pt]?\{[^}]+\}","",intro_no_display)
    assert 450<=len(intro_no_cites.split())<=530
    assert 125<=len(abstract.split())<=155
    assert "?" not in abstract
    assert not re.search(r"(?<!\\)%",abstract)
    assert r"50\%" in abstract and r"43.75\%" in abstract
    assert r"\pm25\%" in abstract
    assert "two successive lower-limit closes for five assets" in abstract
    assert "maximal attainable coverage is unresolved" in abstract
    assert intro.index("Gennotte and Leland")<intro.index(
        "To isolate that question, we construct a deliberately minimal market")
    assert intro.index("To isolate that question, we construct a deliberately minimal market")<intro.index(
        "The main mathematical tool")
    assert re.search(r"^\\bibliographystyle\{unsrtnat\}\s*$",tex,re.MULTILINE)
    assert r"\end{document}" in tex
    assert tex.count(r"\begin{proof}") == tex.count(r"\end{proof}")
    assert "Proof sketch" not in tex
    for title in ("Construction I","Construction II","Construction III"):
        assert title in main,title
    for label in (
        "thm:barrier1","thm:barrier2","thm:ABC","thm:critical",
        "thm:resource","thm:quadratic-rate","thm:sublinear-severe",
        "prop:five-two-day-limits","prop:two-day-coverage-obstruction",
        "eq:target-twoday","eq:two-day-knots","eq:two-day-plateau-root",
        "eq:two-day-compensator","eq:two-day-y-certified","app:two-day-cert"):
        assert r"\label{"+label+"}" in tex,label
    for old in ("Neither proves existence","the existence proposition and",
                "R70-20-M5","P60-20","A1--A2","B1--B2"):
        assert old not in main,old
    assert "1183k\\le8960" in main
    assert r"1.15451858960596<h<1.15451858960597" in main
    assert r"0.7659099&<y(t)<1.1797780" in main
    assert r"\Cris_{1/2}(40)>-\log(0.84)>0.174" in main
    assert r"\bar v" in main and r"M<14" in main
    original_figure=(SRC.parent/"twin_conservation_figure.tex").read_text(encoding="utf-8")
    assert r"\\input{twin_conservation_figure.tex}" in intro
    assert "fig:conservation-geometry" in original_figure
    assert r"\\input{two_day_streak_figure.tex}" in main
    assert (ROOT/"scripts/generate_v16_path_figure.py").exists()
    assert (ROOT/"verification/audit_two_day_25pct_squared_interval.py").exists()
    assert r"\\label{eq:independent-squared-endpoint}" in tex
    assert "The second idealized ten-asset family" not in tex
    assert "For the $N=12$" not in tex
    labels=set(re.findall(r"\\label\{([^}]+)\}",tex))
    labels.update(re.findall(r"\\label\{([^}]+)\}",original_figure))
    labels.add("fig:two-day-price-rate")
    refs=set(re.findall(r"\\(?:ref|eqref|autoref)\{([^}]+)\}",tex))
    assert not (refs-labels),("missing labels",sorted(refs-labels))
    bkeys=set(re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,",bib))
    cited=set()
    for raw in re.findall(r"\\cite[pt]?(?:\[[^\]]*\])?\{([^}]+)\}",tex):
        cited.update(z.strip() for z in raw.split(","))
    assert cited<=bkeys,("unknown citations",sorted(cited-bkeys))
    assert len(cited)>=30,("unexpectedly pruned literature",len(cited))
    assert tex.count(r"\begin{equation}")==tex.count(r"\end{equation}")
    assert tex.count(r"\begin{figure}")==tex.count(r"\end{figure}")
    print(f"PASS V16 abstract={len(abstract.split())} words; introduction={len(intro_no_cites.split())} words")
    print(f"PASS three constructive claims, labels={len(labels)}, citations={len(cited)}")

if __name__=="__main__":
    main()
