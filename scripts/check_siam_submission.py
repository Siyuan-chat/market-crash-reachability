"""Verify that the SIAM edition changes formatting, not mathematical/prose content."""
from pathlib import Path
import argparse, importlib.util, json, re
import build_siam_submission as builder

ROOT = Path(__file__).resolve().parents[1]

def normalized(text):
    return re.sub(r'\s+', '', text)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiled', action='store_true')
    args = parser.parse_args()
    generated = builder.sources()
    rows = []
    for kind, source in [('main', ROOT/'paper/main.tex'), ('supplementary', ROOT/'supplementary/supplementary.tex')]:
        canonical = source.read_text(encoding='utf-8')
        formatted = generated[kind+'.tex']
        marker = r'\begin{abstract}' if kind == 'main' else r'\section'
        target = formatted[formatted.index(marker):formatted.index(r'\end{document}')]
        if kind == 'main':
            target = target.replace(r'\begin{abstract}', r'\begin{abstract}\noindent')
            target = re.sub(r'\\begin\{keywords\}(.*?)\\end\{keywords\}', lambda m:r'\noindent\textbf{Keywords:} '+m[1]+r'\par', target, flags=re.S)
            target = re.sub(r'\\begin\{MSCcodes\}(.*?)\\end\{MSCcodes\}', lambda m:r'\noindent\textbf{MSC 2020:} '+m[1], target, flags=re.S)
            target = target.replace(r'\bibliographystyle{siamplain}', r'\bibliographystyle{siam}')
            for old, new in builder.LAYOUT_REPLACEMENTS:
                assert target.count(new) == 1
                target = target.replace(new, old)
        else:
            target = target.replace(r'\section{', r'\section*{')
        original = canonical[canonical.index(marker):canonical.index(r'\end{document}')]
        assert normalized(target) == normalized(original), kind+': non-format content changed'
        for name, text in generated.items():
            assert (ROOT/'submission/siam'/name).read_text(encoding='utf-8') == text, name+': generated snapshot stale'
        rows.append({'document': kind, 'all_body_prose_and_math_equal_after_explicit_layout_reversal': True})
    assert (ROOT/'submission/siam/references.bib').read_bytes() == (ROOT/'paper/references.bib').read_bytes()
    if args.compiled:
        spec = importlib.util.spec_from_file_location('translation_check', ROOT/'scripts/check_translation_consistency.py')
        helper = importlib.util.module_from_spec(spec); spec.loader.exec_module(helper)
        for row in rows:
            stem = row['document']
            canonical = ROOT/'build/siam-baseline'/('paper' if stem=='main' else 'supplementary')/(stem+'.aux')
            before = helper.labels_from_aux(canonical)
            after = helper.labels_from_aux(ROOT/'build/siam'/(stem+'.aux'))
            # SIAM loads cleveref and creates companion metadata labels. They are
            # not new manuscript labels and must refer to an existing label.
            extras = set(after) - set(before)
            assert all(k.endswith('@cref') and k[:-5] in before for k in extras), extras
            after = {k:v for k,v in after.items() if not k.endswith('@cref')}
            assert set(before) == set(after), stem+': label set changed'
            if stem == 'main': assert before == after, 'Main theorem/equation/figure/table numbers changed'
            row['compiled_labels'] = [{'label': k, 'canonical': before[k], 'siam': after[k]} for k in before]
    out = ROOT/'build/siam'; out.mkdir(parents=True, exist_ok=True)
    (out/'content_consistency.json').write_bytes((json.dumps({'status':'PASS','documents':rows},indent=2)+'\n').encode())
    print('PASS: all prose and mathematics preserved; committed SIAM sources match generator')
    if args.compiled: print('PASS: main numbering unchanged; supplement numbering mapping recorded')

if __name__ == '__main__':
    main()
