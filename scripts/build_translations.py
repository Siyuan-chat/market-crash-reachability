"""Build the canonical English sources and four draft translations in a fresh tree."""
from pathlib import Path
import subprocess,shutil,argparse,tempfile,re,json,hashlib
ROOT=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser();parser.add_argument('--lualatex',default='lualatex');parser.add_argument('--pdflatex',default='pdflatex');args=parser.parse_args()
def executable(name):
    p=Path(name)
    found=str(p.resolve()) if p.is_file() else shutil.which(name)
    if not found:raise SystemExit('Missing compiler: '+name)
    return found
lua=executable(args.lualatex);pdf=executable(args.pdflatex)
out=ROOT/'build/translations';out.mkdir(parents=True,exist_ok=True)
scratch=Path(tempfile.mkdtemp(prefix='source-',dir=out))
for name in ('paper','supplementary'):
    (scratch/name).mkdir()
    shutil.copytree(ROOT/name/'figures',scratch/name/'figures')
    for p in (ROOT/name).iterdir():
        if p.suffix in ('.tex','.bbl','.bib'):shutil.copyfile(p,scratch/name/p.name)
jobs=[('en','main',scratch/'paper',pdf),('en','supplementary',scratch/'supplementary',pdf)]
for lang in ('zh-CN','ja'):
    folder=scratch/'translations'/lang;folder.mkdir(parents=True)
    for stem in ('main','supplementary'):shutil.copyfile(ROOT/'translations'/lang/(stem+'.tex'),folder/(stem+'.tex'))
    shutil.copyfile(ROOT/'paper/main.bbl',folder/'main.bbl')
    jobs.extend((lang,stem,folder,lua) for stem in ('main','supplementary'))
summary=[]
for lang,stem,folder,engine in jobs:
    dest=out/lang;dest.mkdir(exist_ok=True)
    passes=[]
    for iteration in range(5):
        logfile=dest/f'{stem}-pass-{iteration+1}.txt'
        with logfile.open('w',encoding='utf-8') as stream:
            process=subprocess.run([engine,'-no-shell-escape','-interaction=nonstopmode','-halt-on-error',stem+'.tex'],cwd=folder,stdout=stream,stderr=subprocess.STDOUT)
        if process.returncode:raise SystemExit(f'Build failed: {lang}/{stem}; inspect {logfile}')
        log=(folder/(stem+'.log')).read_text(errors='replace')
        rerun=bool(re.search(r'Label\(s\) may have changed|Rerun to get|There were undefined references|Citation .* undefined',log))
        passes.append({'pass':iteration+1,'rerun_required':rerun})
        if iteration>=1 and not rerun:break
    else:raise SystemExit('Unstable cross-references: '+lang+'/'+stem)
    if 'Missing character:' in log:raise SystemExit('Missing glyphs: '+lang+'/'+stem+'; inspect final log')
    for extension in ('.pdf','.aux','.log'):
        shutil.copyfile(folder/(stem+extension),dest/(stem+extension))
    row={'language':lang,'document':stem,'passes':passes,'pdf_sha256':hashlib.sha256((dest/(stem+'.pdf')).read_bytes()).hexdigest(),'overfull_warnings':re.findall(r'Overfull[^\n]*',log),'underfull_count':log.count('Underfull'),'missing_glyphs':False}
    summary.append(row);print(lang,stem,'PASS',len(passes),'passes; overfull',len(row['overfull_warnings']),flush=True)
(out/'build_summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8',newline='\n')
