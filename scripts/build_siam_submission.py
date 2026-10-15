"""Generate a format-only SIAM review edition from the locked English baseline."""
from pathlib import Path
import argparse, hashlib, json, re, shutil, subprocess, tempfile, zipfile

ROOT = Path(__file__).resolve().parents[1]
TITLE = 'When Can Markets Crash Without News?'
TEMPLATE_SHA256 = '45477e268578328bfaeb56f53f319a0d6e8b88e5394da29413e15c076a6a40ab'
ORIGINAL_TEMPLATE_SHA256 = '2d74fc697977dbbd1283ec814eb57777be701c76a9325fbdf754ba9abf7a3e98'
LAYOUT_REPLACEMENTS = [(
    '101600000000h^2-97138000000h-6646157699=0,\n'
    r'\quad1.02020225507905<h<1.02020225507908.',
    '\\begin{aligned}\n&101600000000h^2-97138000000h-6646157699=0,\\\\\n'
    '&1.02020225507905<h<1.02020225507908.\n\\end{aligned}'
), ('Direct integration also gives', r'\linebreak Direct integration also gives')]

def sources():
    main = (ROOT / 'paper/main.tex').read_text(encoding='utf-8')
    supplement = (ROOT / 'supplementary/supplementary.tex').read_text(encoding='utf-8')
    macros = main[main.index(r'\newcommand{\R}'):main.index(r'\title{')]
    shared = r'''% SIAM format only; mathematical source remains English V12 Final.
\usepackage{microtype,xurl}
\usepackage{amsfonts,amssymb,mathtools,bm}
\usepackage{graphicx,booktabs,enumitem,float,tabularx,placeins}
\graphicspath{{../../paper/}{../../supplementary/}}
\usepackage[numbers,sort&compress]{natbib}
\newsiamremark{assumption}{Assumption}
\newsiamremark{remark}{Remark}
\headers{When Can Markets Crash Without News?}{Siyuan Ye}
\title{When Can Markets Crash Without News?}
\author{Siyuan Ye\thanks{Independent Researcher.}}
\hypersetup{pdftitle={When Can Markets Crash Without News?},pdfauthor={Siyuan Ye}}
\setlength{\emergencystretch}{1em}
% The unmodified online class's two-line running head exceeds its 10pt preset.
\setlength{\headheight}{14pt}
''' + macros
    body = main[main.index(r'\begin{abstract}'):main.index(r'\end{document}')]
    body = body.replace(r'\begin{abstract}\noindent', r'\begin{abstract}')
    body = re.sub(r'\\noindent\\textbf\{Keywords:\} (.*?)\\par',
                  lambda m: r'\begin{keywords}' + m[1] + r'\end{keywords}', body)
    body = re.sub(r'\\noindent\\textbf\{MSC 2020:\} ([^\n]+)',
                  lambda m: r'\begin{MSCcodes}' + m[1] + r'\end{MSCcodes}', body)
    body = body.replace(r'\bibliographystyle{siam}', r'\bibliographystyle{siamplain}')
    for old, new in LAYOUT_REPLACEMENTS:
        assert body.count(old) == 1, 'Layout replacement no longer matches baseline'
        body = body.replace(old, new)
    article = '\\documentclass[review,hidelinks,onefignum,onetabnum]{siamonline250211}\n'
    article += '\\input{shared}\n\\begin{document}\n\\maketitle\n' + body + '\\end{document}\n'
    sb = supplement[supplement.index(r'\section*'):supplement.index(r'\end{document}')]
    sb = sb.replace(r'\section*', r'\section')
    supp = '\\documentclass[review,supplement,hidelinks,onefignum,onetabnum]{siamonline250211}\n'
    supp += '\\input{shared}\n\\begin{document}\n\\maketitle\n' + sb + '\\end{document}\n'
    return {'main.tex': article, 'supplementary.tex': supp, 'shared.tex': shared}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--template-zip', type=Path, help='Optional local copy of the official template ZIP')
    parser.add_argument('--pdflatex', default='pdflatex')
    parser.add_argument('--bibtex', default='bibtex')
    parser.add_argument('--update-edition', action='store_true', help='Refresh committed author-owned SIAM sources and PDFs after a successful build')
    args = parser.parse_args()
    baseline = json.loads((ROOT / 'docs/PHASE2_BASELINE.json').read_text())
    for name, digest in baseline['sha256'].items():
        assert hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest, name
    out = ROOT / 'build/siam'; out.mkdir(parents=True, exist_ok=True)
    archive_path = args.template_zip or ROOT/'third_party/siam/siamonline_250211_complete.zip'
    assert hashlib.sha256(archive_path.read_bytes()).hexdigest() in {TEMPLATE_SHA256, ORIGINAL_TEMPLATE_SHA256}, 'Unexpected SIAM template archive; do not silently update'
    work = Path(tempfile.mkdtemp(prefix='source-', dir=out))
    generated = sources()
    with zipfile.ZipFile(archive_path) as archive:
        for name in ('siamonline250211.cls', 'siamplain.bst'):
            (work / name).write_bytes(archive.read(name))
    for name, text in generated.items():
        (work / name).write_bytes(text.encode('utf-8'))
    shutil.copyfile(ROOT / 'paper/references.bib', work / 'references.bib')
    # Keep original figure names: main and supplement share no differing basename.
    (work / 'figures').mkdir()
    seen = {}
    for folder in ('paper', 'supplementary'):
        for file in (ROOT / folder / 'figures').iterdir():
            if file.name in seen:
                assert seen[file.name] == file.read_bytes(), file.name
            seen[file.name] = file.read_bytes()
            shutil.copyfile(file, work / 'figures' / file.name)
    summary = []
    for stem in ('main', 'supplementary'):
        for iteration in range(6):
            with (out / f'{stem}-pass-{iteration+1}.txt').open('w', encoding='utf-8') as stream:
                result = subprocess.run([str(Path(args.pdflatex).resolve()) if Path(args.pdflatex).is_file() else args.pdflatex,
                    '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error', stem+'.tex'], cwd=work, stdout=stream, stderr=subprocess.STDOUT)
            if result.returncode:
                raise SystemExit(f'Build failed: {stem}; see {out}; source {work}')
            if stem == 'main' and iteration == 0:
                with (out / 'bibtex.txt').open('w', encoding='utf-8') as stream:
                    result = subprocess.run([str(Path(args.bibtex).resolve()) if Path(args.bibtex).is_file() else args.bibtex, 'main'], cwd=work, stdout=stream, stderr=subprocess.STDOUT)
                if result.returncode: raise SystemExit('BibTeX failed; see build/siam/bibtex.txt')
            log = (work / (stem+'.log')).read_text(errors='replace')
            pending = re.search(r'Label\(s\) may have changed|Rerun to get|There were undefined references|Citation .* undefined', log)
            if iteration >= 2 and not pending: break
        else: raise SystemExit('Unstable references: '+stem)
        for suffix in ('.pdf', '.log', '.aux', '.bbl'):
            path = work / (stem+suffix)
            if path.exists(): shutil.copyfile(path, out / path.name)
        summary.append({'document': stem, 'passes': iteration+1,
            'overfull': re.findall(r'Overfull[^\n]*', log),
            'missing_characters': log.count('Missing character:'),
            'pdf_sha256': hashlib.sha256((out/(stem+'.pdf')).read_bytes()).hexdigest()})
        print(stem, 'built', 'overfull:', len(summary[-1]['overfull']), flush=True)
    (out / 'build_summary.json').write_bytes((json.dumps(summary, indent=2)+'\n').encode())
    assert all(not row['overfull'] and not row['missing_characters'] for row in summary), 'Resolve missing glyphs or overfull boxes; see build/siam/build_summary.json'
    # Export author-owned sources only. SIAM's class/style remain local dependencies.
    exported = out / 'author-sources'; exported.mkdir(exist_ok=True)
    for name in (*generated, 'references.bib', 'main.bbl'):
        shutil.copyfile(work / name, exported / name)
    shutil.copytree(work / 'figures', exported / 'figures', dirs_exist_ok=True)
    if args.update_edition:
        edition = ROOT / 'submission/siam'; edition.mkdir(parents=True, exist_ok=True)
        for name in (*generated, 'references.bib', 'main.bbl'):
            shutil.copyfile(work / name, edition / name)
        shutil.copyfile(out / 'main.pdf', edition / 'manuscript.pdf')
        shutil.copyfile(out / 'supplementary.pdf', edition / 'supplementary.pdf')
    print('Generated sources:', exported)

if __name__ == '__main__':
    main()
