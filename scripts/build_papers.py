"""Compile isolated source copies, preserving the supplied V12 Final PDFs."""
from pathlib import Path
import shutil, subprocess, argparse, tempfile, re, json
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser()
parser.add_argument('--tectonic',help='Optional portable Tectonic executable; produces an alternate-engine comparison build')
parser.add_argument('--pdflatex',help='Optional path to a portable pdfLaTeX executable')
parser.add_argument('--output-root',default='release/rebuilt',help='Output directory, relative to the repository or absolute')
args=parser.parse_args()
if args.tectonic and args.pdflatex: parser.error('Choose one TeX engine')
pdflatex=str(Path(args.pdflatex).resolve()) if args.pdflatex else shutil.which('pdflatex')
if not args.tectonic and not pdflatex: raise SystemExit('pdflatex is required; install a TeX distribution or supply --pdflatex/--tectonic.')
output=Path(args.output_root)
if not output.is_absolute(): output=ROOT/output
workspace=ROOT/'build/latex_workspaces'; workspace.mkdir(parents=True,exist_ok=True)
for directory,source in [('paper','main.tex'),('supplementary','supplementary.tex')]:
    out=output/directory
    work=Path(tempfile.mkdtemp(prefix=directory+'-',dir=workspace))
    shutil.copytree(ROOT/directory,work,dirs_exist_ok=True)
    passes=[]
    for iteration in range(5):
        with (work/f'compile-{iteration+1}.txt').open('w',encoding='utf-8') as log:
            command=[str(Path(args.tectonic).resolve()),'--untrusted','--reruns','2','--keep-intermediates','--keep-logs',source] if args.tectonic else [pdflatex,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error',source]
            result=subprocess.run(command,cwd=work,stdout=log,stderr=subprocess.STDOUT)
        if result.returncode: raise SystemExit(f'Compilation failed; evidence preserved: {work}')
        engine_log=(work/Path(source).with_suffix('.log')).read_text(errors='replace')
        rerun=bool(re.search(r'Label\(s\) may have changed|Rerun to get|There were undefined references|Citation .* undefined',engine_log))
        passes.append({'pass':iteration+1,'exit_code':result.returncode,'rerun_required':rerun})
        if iteration>=1 and not rerun: break
    else: raise SystemExit(f'Cross-references did not stabilize after five passes: {work}')
    result_pdf=work/Path(source).with_suffix('.pdf')
    assert result_pdf.is_file() and result_pdf.stat().st_size>0,result_pdf
    shutil.copytree(work,out,dirs_exist_ok=True)
    (out/'build_passes.json').write_text(json.dumps(passes,indent=2)+'\n',encoding='utf-8')
    print('Built',out/result_pdf.name)
