"""Check protected mathematical structure, not translation quality or theorem truth."""
from pathlib import Path
import argparse,re,json,hashlib,collections
ROOT=Path(__file__).resolve().parents[1]
MATH=re.compile(r'\\begin\{(equation\*?|align\*?|gather\*?|multline\*?|eqnarray\*?)\}.*?\\end\{\1\}|\\\[.*?\\\]|\\\(.*?\\\)|(?<!\\)\$(?:\\.|[^$])*?(?<!\\)\$',re.S)
REF=re.compile(r'\\(label|ref|eqref|cite|citep|citet)(?:\[[^\]]*\])*\{([^}]+)\}')
ENV=re.compile(r'\\begin\{(theorem|proposition|lemma|corollary|assumption|definition|remark)\}')
FIG=re.compile(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}')
def strip_comments(s):return re.sub(r'(?<!\\)%[^\n]*','',s)
def body(s,kind):
    s=strip_comments(s)
    marker=r'\begin{abstract}' if kind=='main' else r'\section*'
    return s[s.index(marker):s.index(r'\end{document}')]
def normalize(s):return re.sub(r'\s+','',strip_comments(s))
def units(s):return [m.group(0) for m in MATH.finditer(s)]
def plain_numbers(s):
    plain=MATH.sub('',s)
    plain=re.sub(r'\\(?:label|ref|eqref|cite|citep|citet|includegraphics|path|url)(?:\[[^\]]*\])*\{[^}]*\}','',plain)
    return re.findall(r'(?<![A-Za-z0-9_])\d+(?:\.\d+)*(?:[eE][-+]?\d+)?',plain)
def prose_lines(s):
    s=MATH.sub('',s)
    s=re.sub(r'\\(?:label|ref|eqref|cite|citep|citet|includegraphics|path|url)(?:\[[^\]]*\])*\{[^}]*\}','',s)
    return [x.strip() for x in s.splitlines() if len(re.findall(r'\b[A-Za-z]{2,}\b',x))>=8]
def labels_from_aux(path):
    return dict(re.findall(r'\\newlabel\{([^{}]+)\}\{\{([^{}]*)\}',path.read_text(errors='replace')))
def main():
    parser=argparse.ArgumentParser();parser.add_argument('--out',default='build/translations/consistency.json')
    parser.add_argument('--aux-root',help='Optional build/translations directory with en, zh-CN and ja aux subdirectories')
    args=parser.parse_args();report={'canonical_commit':'e5339a47f29ccb669d1f228ca930a1c1146200bf','documents':[]};failed=False
    baseline=json.loads((ROOT/'docs/PHASE2_BASELINE.json').read_text())
    for name,digest in baseline['sha256'].items():
        assert hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==digest,'Canonical baseline changed: '+name
    for kind,source in [('main',ROOT/'paper/main.tex'),('supplementary',ROOT/'supplementary/supplementary.tex')]:
        original=body(source.read_text(encoding='utf-8'),kind);expected=units(original)
        for lang in ('zh-CN','ja'):
            path=ROOT/'translations'/lang/(kind+'.tex')
            if not path.exists():report['documents'].append({'language':lang,'document':kind,'status':'MISSING'});failed=True;continue
            translated=body(path.read_text(encoding='utf-8'),kind);actual=units(translated)
            diffs=[{'index':i,'original':a,'translation':b} for i,(a,b) in enumerate(zip(expected,actual)) if normalize(a)!=normalize(b)]
            refs_equal=REF.findall(original)==REF.findall(translated)
            source_figs=[Path(x).name for x in FIG.findall(original)];target_figs=[Path(x).name for x in FIG.findall(translated)]
            unchanged=[line for line in prose_lines(original) if line in translated]
            numbers_equal=plain_numbers(original)==plain_numbers(translated)
            row={'language':lang,'document':kind,'math_units_original':len(expected),'math_units_translation':len(actual),'math_differences':diffs,'reference_and_label_order_equal':refs_equal,'theorem_environment_order_equal':ENV.findall(original)==ENV.findall(translated),'figures_equal':source_figs==target_figs,'table_count_equal':original.count(r'\begin{table}')==translated.count(r'\begin{table}'),'table_cell_separators_equal':len(re.findall(r'(?<!\\)&',original))==len(re.findall(r'(?<!\\)&',translated)),'plain_numeric_sequence_equal':numbers_equal,'scientific_identifiers_equal':re.findall(r'(?<![A-Za-z0-9])(?:M[0-9]+|[0-9]{2}[A-Z][0-9]{2})(?![A-Za-z0-9])',original)==re.findall(r'(?<![A-Za-z0-9])(?:M[0-9]+|[0-9]{2}[A-Z][0-9]{2})(?![A-Za-z0-9])',translated),'unchanged_english_prose_lines':unchanged}
            if not numbers_equal:row['plain_numeric_sequences']={'source':plain_numbers(original),'translation':plain_numbers(translated)}
            if args.aux_root:
                root=Path(args.aux_root);root=root if root.is_absolute() else ROOT/root
                ea=labels_from_aux(root/'en'/(kind+'.aux'));ta=labels_from_aux(root/lang/(kind+'.aux'))
                row['compiled_label_numbers_equal']=ea==ta
                if ea!=ta:row['compiled_label_differences']={k:[ea.get(k),ta.get(k)] for k in ea.keys()|ta.keys() if ea.get(k)!=ta.get(k)}
            row['status']='PASS' if len(expected)==len(actual) and not diffs and refs_equal and row['theorem_environment_order_equal'] and row['figures_equal'] and row['table_count_equal'] and row['table_cell_separators_equal'] and numbers_equal and row['scientific_identifiers_equal'] and not unchanged and row.get('compiled_label_numbers_equal',True) else 'FAIL'
            failed|=row['status']!='PASS';report['documents'].append(row)
    report['status']='FAIL' if failed else 'PASS'
    out=Path(args.out);out=out if out.is_absolute() else ROOT/out;out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n',encoding='utf-8',newline='\n')
    for row in report['documents']:print(row['language'],row['document'],row['status'],'math:',row.get('math_units_translation'), 'diffs:',len(row.get('math_differences',[])),'plain numbers:',row.get('plain_numeric_sequence_equal'),'unchanged prose:',len(row.get('unchanged_english_prose_lines',[])))
    print('Evidence:',out)
    raise SystemExit(1 if failed else 0)
if __name__=='__main__':main()
