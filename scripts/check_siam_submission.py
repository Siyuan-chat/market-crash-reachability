"""Verify that the SIAM edition changes formatting, not mathematical/prose content."""
from pathlib import Path
import argparse, importlib.util, json, re
import build_siam_submission as builder
from siam_editorial import editorial_changes, bibliography

ROOT = Path(__file__).resolve().parents[1]

def normalized(text):
    return re.sub(r'\s+', '', text)


def compiled_figure_widths(paths, metrics):
    """Measure actual pdfLaTeX placement, rather than assuming TeX scaling."""
    import math
    import io
    import pikepdf
    import pymupdf
    lookup = {r['output']: r for r in metrics['figures']}
    records = []
    for path in paths:
        with pikepdf.open(path) as pdf:
            for number, page in enumerate(pdf.pages, 1):
                state, stack = (1., 0., 0., 1.), []
                for instruction in pikepdf.parse_content_stream(page):
                    op, values = str(instruction.operator), instruction.operands
                    if op == 'q': stack.append(state)
                    elif op == 'Q': state = stack.pop()
                    elif op == 'cm':
                        a,b,c,d = state
                        u,v,w,x = map(float, values[:4])
                        state = (a*u+c*v, b*u+d*v, a*w+c*x, b*w+d*x)
                    elif op == 'Do':
                        obj = page.Resources.XObject[values[0]]
                        name = Path(str(obj.get('/PTEX.FileName', ''))).name
                        assert name in lookup, 'Unexpected top-level graphic: '+name
                        assert list(obj.get('/Matrix', [1,0,0,1,0,0])) == [1,0,0,1,0,0], 'Review transformed Form'
                        a,b,c,d = state
                        assert abs(a*c+b*d) < 1e-7, 'Review skewed figure placement'
                        scale = min(math.hypot(a,b), math.hypot(c,d))
                        # Read the actual embedded Form (and nested resources),
                        # not a minimum inferred from an external figure file.
                        box = list(map(float, obj.BBox))
                        isolated = pikepdf.Pdf.new()
                        blank = isolated.add_blank_page(page_size=(box[2]-box[0], box[3]-box[1]))
                        blank.Resources = pikepdf.Dictionary(XObject=pikepdf.Dictionary(Audit=isolated.copy_foreign(obj)))
                        blank.Contents = isolated.make_stream(b'/Audit Do')
                        stream = io.BytesIO()
                        isolated.save(stream)
                        with pymupdf.open(stream=stream.getvalue(), filetype='pdf') as form:
                            strokes = [r['width'] for r in form[0].get_drawings() if 's' in r['type'] and r.get('stroke_opacity',1)>0]
                        assert strokes and min(strokes) > 0, 'Missing/zero-width embedded strokes'
                        minimum = min(strokes)*scale
                        assert minimum >= 1.02-1e-4, 'Compiled figure below final-size minimum: '+name
                        records.append({'pdf':path.name,'page':number,'figure':name,'actual_min_linewidth_pt':minimum})
    assert len(records) == len(lookup) and {r['figure'] for r in records} == set(lookup), 'Missing/duplicate embedded figures'
    return records

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
        # Only explicitly enumerated editorial prose may differ; math, captions,
        # theorem statements and all remaining body text retain the strict check.
        target = editorial_changes(target, kind, reverse=True)
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
        rows.append({'document': kind, 'all_body_prose_and_math_equal_after_explicit_editorial_and_layout_reversal': True})
    assert (ROOT/'submission/siam/references.bib').read_text(encoding='utf-8') == bibliography((ROOT/'paper/references.bib').read_text(encoding='utf-8'))
    for name in ('main.tex','supplementary.tex'):
        text = generated[name]
        labels = re.findall(r'\\label\{(fig:[^}]+)\}', text)
        prose = re.sub(r'\\begin\{figure\}.*?\\end\{figure\}', '', text, flags=re.S)
        assert all(r'\ref{'+label+'}' in prose for label in labels), 'Figure missing body callout'
    if args.compiled:
        from prepare_siam_figures import prepare_figures
        figure_metrics = prepare_figures(ROOT, ROOT/'submission/siam/figures', generated['main.tex'], generated['supplementary.tex'], check=True)
        committed_figures = compiled_figure_widths([ROOT/'submission/siam/manuscript.pdf', ROOT/'submission/siam/supplementary.pdf'], figure_metrics)
        built_figures = compiled_figure_widths([ROOT/'build/siam/main.pdf', ROOT/'build/siam/supplementary.pdf'], figure_metrics)
        # Regression control: the locked original PDFs contain the same figure
        # names but thin strokes, so names/scaling alone must not let them pass.
        try:
            compiled_figure_widths([ROOT/'paper/manuscript.pdf', ROOT/'supplementary/supplementary.pdf'], figure_metrics)
        except AssertionError as error:
            assert 'below final-size minimum' in str(error), str(error)
        else: raise AssertionError('Original thin-line negative control incorrectly accepted')
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
    report = {'status':'PASS','documents':rows,'explicit_editorial_changes':['figure callouts','code/data availability'], 'bibliography_changes':'journal fields only'}
    if args.compiled:
        report['derived_figures'] = figure_metrics
        report['compiled_figure_widths'] = {'committed':committed_figures,'rebuilt':built_figures}
        report['original_thin_line_negative_control_rejected'] = True
    (out/'content_consistency.json').write_bytes((json.dumps(report,indent=2)+'\n').encode())
    print('PASS: mathematical content and all prose outside explicit editorial changes preserved; generated snapshots current')
    if args.compiled: print('PASS: main numbering unchanged; supplement numbering mapping recorded')

if __name__ == '__main__':
    main()
