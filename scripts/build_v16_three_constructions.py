"""Build the V16 working draft from author sources without changing published PDFs."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, tempfile, zipfile

ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/"submission/v16-three-certified-constructions"
PREV=ROOT/"submission/siam-language-revision"
OUT=ROOT/"build/v16-three-certified-constructions"
ZIP=ROOT/"third_party/siam/siamonline_250211_complete.zip"
ALLOWED={
    "45477e268578328bfaeb56f53f319a0d6e8b88e5394da29413e15c076a6a40ab",
    "2d74fc697977dbbd1283ec814eb57777be701c76a9325fbdf754ba9abf7a3e98",
}

def check_first_appearance_numbering(aux_file: Path, bbl_file: Path) -> dict:
    """BibTeX item order must equal first occurrence of each citation in LaTeX."""
    aux = aux_file.read_text(encoding="utf-8", errors="replace")
    bbl = bbl_file.read_text(encoding="utf-8", errors="replace")
    assert r"\bibstyle{unsrtnat}" in aux, "An unsorted numeric bibliography is required."
    citations = []
    seen = set()
    for grouped in re.findall(r"\\citation\{([^{}]+)\}", aux):
        for raw in grouped.split(","):
            key = raw.strip()
            if not key or key == "*" or key in seen:
                continue
            seen.add(key)
            citations.append(key)
    items = re.findall(r"\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}", bbl)
    if not citations or not items:
        raise RuntimeError("Missing resolved references in LaTeX auxiliary files")
    if citations != items:
        difference = next((idx for idx, (a, b) in enumerate(zip(citations, items), 1)
                           if a != b), None)
        raise RuntimeError("Bibliography is not numbered by first citation order: "
                           f"first difference at {difference}; "
                           f"citations={citations}, bibitems={items}")
    return {"numbering": "first-citation-order", "entries": len(items),
            "first_five": items[:5]}


def main():
    subprocess.run(["python",str(ROOT/"scripts/check_v16_three_constructions.py")],cwd=ROOT,check=True)
    subprocess.run(["python",str(ROOT/"verification/two_day_25pct_five_assets.py")],
                   cwd=ROOT,check=True)
    subprocess.run(["python",str(ROOT/"verification/audit_two_day_25pct.py")],
                   cwd=ROOT,check=True)
    subprocess.run(["python",str(ROOT/"verification/audit_two_day_25pct_squared_interval.py")],
                   cwd=ROOT,check=True)
    assert hashlib.sha256(ZIP.read_bytes()).hexdigest() in ALLOWED, "Unrecognized SIAM template"
    pdflatex=shutil.which("pdflatex")
    bibtex=shutil.which("bibtex")
    if not pdflatex or not bibtex:
        raise SystemExit("pdfLaTeX and BibTeX are required to build V16")
    OUT.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="v16-",dir=OUT) as tmp:
        work=Path(tmp)
        for filename in ("main.tex","shared.tex","references.bib","twin_conservation_figure.tex"):
            shutil.copyfile(SRC/filename,work/filename)
        shutil.copytree(PREV/"figures",work/"figures")
        subprocess.run(["python",str(ROOT/"scripts/generate_v16_path_figure.py"),
                        "--out",str(work/"two_day_streak_figure.tex")],
                       cwd=ROOT,check=True)
        # The copied figures resolve locally; neither the old source nor its PDFs change.
        with zipfile.ZipFile(ZIP) as z:
            for name in ("siamonline250211.cls","siamplain.bst"):
                (work/name).write_bytes(z.read(name))
        passes=[]
        for iteration in range(6):
            proc=subprocess.run([pdflatex,"-no-shell-escape","-interaction=nonstopmode",
                "-halt-on-error","main.tex"],cwd=work,capture_output=True,text=True)
            (OUT/f"pdflatex-{iteration+1}.txt").write_text(proc.stdout+proc.stderr)
            if proc.returncode:
                raise SystemExit(f"V16 pdfLaTeX pass {iteration+1} failed")
            if iteration==0:
                b=subprocess.run([bibtex,"main"],cwd=work,capture_output=True,text=True)
                (OUT/"bibtex.txt").write_text(b.stdout+b.stderr)
                if b.returncode:
                    raise SystemExit("V16 BibTeX failed; see build/v16-three-certified-constructions/bibtex.txt")
            log=(work/"main.log").read_text(errors="replace")
            rerun=bool(re.search(r"Label\(s\) may have changed|Rerun to get|There were undefined references|Citation .* undefined",log))
            passes.append({"pass":iteration+1,"rerun_needed":rerun})
            if iteration>=2 and not rerun:
                break
        else:
            raise SystemExit("V16 references did not converge")
        bibliography_audit=check_first_appearance_numbering(work/"main.aux", work/"main.bbl")
        problems=re.findall(r"Overfull \\hbox[^\n]*|Overfull \\vbox[^\n]*|Package natbib Warning: Author undefined[^\n]*|Missing character:[^\n]*|LaTeX Warning: (?:Citation|Reference) [^\n]*undefined",log)
        for suffix in (".pdf",".log",".aux",".bbl"):
            file=work/("main"+suffix)
            if file.is_file():
                shutil.copyfile(file,OUT/file.name)
        pdf_text_run = subprocess.run(
            ["pdftotext", "-f", "1", "-l", "1", str(OUT/"main.pdf"), "-"],
            capture_output=True, text=True, check=True)
        pdf_first_page = re.sub(r"\s+", " ", pdf_text_run.stdout)
        for phrase in (
            "nine assets incur arbitrarily severe logarithmic losses",
            "two successive lower-limit closes for five assets",
            "the maximal attainable coverage is unresolved",
            "Elasticity barriers, a sharp full-coverage horizon bound",
        ):
            if phrase not in pdf_first_page:
                raise SystemExit("V16 abstract appears truncated in the rendered PDF: "+phrase)
        summary={"passes":passes, "problems":problems, "bibliography":bibliography_audit,
            "abstract_pdf_complete": True,
            "pdf_sha256":hashlib.sha256((OUT/"main.pdf").read_bytes()).hexdigest(),
            "pdf_size":(OUT/"main.pdf").stat().st_size}
        (OUT/"build_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
        if problems:
            raise SystemExit("V16 layout/citation problems: "+repr(problems))
        print("PASS: V16 source/PDF compiled; see build/v16-three-certified-constructions/main.pdf")

if __name__=="__main__":
    main()
