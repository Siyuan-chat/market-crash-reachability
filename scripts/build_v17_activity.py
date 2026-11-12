#!/usr/bin/env python3
"""V17 independent SIAM build. Historical V16 files are never changed."""
from pathlib import Path
import tempfile,shutil,subprocess,hashlib,json,re,zipfile,sys
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'submission/v17-activity-driven-recovery'
ZIP=ROOT/'third_party/siam/siamonline_250211_complete.zip'
OUT=ROOT/'build/v17-activity-driven-recovery'
def run(cmd,cwd,logname):
    p=subprocess.run(cmd,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (OUT/logname).write_text(p.stdout,encoding='utf-8')
    if p.returncode:raise RuntimeError(f'Command {cmd} failed; see {OUT/logname}\n'+p.stdout[-2500:])
    return p.stdout

def bibliography_audit(aux,bbl):
    assert r'\bibstyle{unsrtnat}' in aux
    keys=[]
    for group in re.findall(r'\\citation\{([^{}]+)\}',aux):
        for key in group.split(','):
            if key not in keys:keys.append(key)
    items=re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^{}]+)\}',bbl)
    if keys!=items:raise RuntimeError(f'First-citation bibliography mismatch: {keys} != {items}')
    return {'first_citation_order':True,'references':len(items)}

def main():
    OUT.mkdir(parents=True,exist_ok=True)
    run([sys.executable,str(ROOT/'verification/activity_driven/test_activity.py')],ROOT,'test_activity.log')
    run([sys.executable,str(ROOT/'verification/activity_driven/certify_five_targets.py')],ROOT,'certificate.log')
    run([sys.executable,str(ROOT/'scripts/check_v17_activity.py')],ROOT,'source_check.log')
    if not ZIP.exists():raise RuntimeError('Required unchanged SIAM style ZIP absent: '+str(ZIP))
    if not shutil.which('pdflatex') or not shutil.which('bibtex'):
        raise RuntimeError('pdflatex and bibtex are required for the strict V17 build')
    with tempfile.TemporaryDirectory(prefix='v17-',dir=OUT) as tmp:
        w=Path(tmp)
        for name in ('main.tex','shared.tex','references.bib'):shutil.copyfile(SRC/name,w/name)
        with zipfile.ZipFile(ZIP) as z:
            for name in ('siamonline250211.cls','siamplain.bst'):(w/name).write_bytes(z.read(name))
        for j in range(5):
            run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','main.tex'],w,f'pdflatex-{j+1}.log')
            if j==0:run(['bibtex','main'],w,'bibtex.log')
        log=(w/'main.log').read_text(errors='replace')
        bad=re.findall(r'Overfull \\hbox[^\n]*|Overfull \\vbox[^\n]*|LaTeX Warning: (?:Citation|Reference) [^\n]*undefined|Package natbib Warning: Author undefined[^\n]*',log)
        if bad:raise RuntimeError('LaTeX layout/citation problems: '+repr(bad))
        result=bibliography_audit((w/'main.aux').read_text(),(w/'main.bbl').read_text())
        for suffix in ('.pdf','.log','.aux','.bbl'):
            shutil.copyfile(w/('main'+suffix),OUT/('main'+suffix))
        pdf=OUT/'main.pdf'
        assert pdf.stat().st_size>20000
        result.update(pdf_sha256=hashlib.sha256(pdf.read_bytes()).hexdigest(),bytes=pdf.stat().st_size,layout_warnings=bad)
        (OUT/'build_summary.json').write_text(json.dumps(result,indent=2)+'\n')
        print('PASS strict SIAM V17 build',result)
if __name__=='__main__':main()
