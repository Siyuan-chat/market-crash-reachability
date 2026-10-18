"""Build the V14 draft from author sources without changing published PDFs."""
from pathlib import Path
import hashlib, json, re, shutil, subprocess, tempfile, zipfile

ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/"submission/v14-turnover-dissipation"
PREV=ROOT/"submission/siam-language-revision"
OUT=ROOT/"build/v14-turnover-dissipation"
ZIP=ROOT/"third_party/siam/siamonline_250211_complete.zip"
ALLOWED={
    "45477e268578328bfaeb56f53f319a0d6e8b88e5394da29413e15c076a6a40ab",
    "2d74fc697977dbbd1283ec814eb57777be701c76a9325fbdf754ba9abf7a3e98",
}

def main():
    subprocess.run(["python",str(ROOT/"scripts/check_v14_resource_bound.py")],cwd=ROOT,check=True)
    assert hashlib.sha256(ZIP.read_bytes()).hexdigest() in ALLOWED, "Unrecognized SIAM template"
    pdflatex=shutil.which("pdflatex")
    bibtex=shutil.which("bibtex")
    if not pdflatex or not bibtex:
        raise SystemExit("pdfLaTeX and BibTeX are required to build V14")
    OUT.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="v14-",dir=OUT) as tmp:
        work=Path(tmp)
        for filename in ("main.tex","shared.tex","references.bib"):
            shutil.copyfile(SRC/filename,work/filename)
        shutil.copytree(PREV/"figures",work/"figures")
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
                raise SystemExit(f"V14 pdfLaTeX pass {iteration+1} failed")
            if iteration==0:
                b=subprocess.run([bibtex,"main"],cwd=work,capture_output=True,text=True)
                (OUT/"bibtex.txt").write_text(b.stdout+b.stderr)
                if b.returncode:
                    raise SystemExit("V14 BibTeX failed; see build/v14-turnover-dissipation/bibtex.txt")
            log=(work/"main.log").read_text(errors="replace")
            rerun=bool(re.search(r"Label\(s\) may have changed|Rerun to get|There were undefined references|Citation .* undefined",log))
            passes.append({"pass":iteration+1,"rerun_needed":rerun})
            if iteration>=2 and not rerun:
                break
        else:
            raise SystemExit("V14 references did not converge")
        problems=re.findall(r"Overfull \\hbox[^\n]*|Overfull \\vbox[^\n]*|Package natbib Warning: Author undefined[^\n]*|Missing character:[^\n]*|LaTeX Warning: (?:Citation|Reference) [^\n]*undefined",log)
        for suffix in (".pdf",".log",".aux",".bbl"):
            file=work/("main"+suffix)
            if file.is_file():
                shutil.copyfile(file,OUT/file.name)
        summary={"passes":passes, "problems":problems,
            "pdf_sha256":hashlib.sha256((OUT/"main.pdf").read_bytes()).hexdigest(),
            "pdf_size":(OUT/"main.pdf").stat().st_size}
        (OUT/"build_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
        if problems:
            raise SystemExit("V14 layout/citation problems: "+repr(problems))
        print("PASS: V14 source/PDF compiled; see build/v14-turnover-dissipation/main.pdf")

if __name__=="__main__":
    main()
