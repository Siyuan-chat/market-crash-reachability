"""Derive SIAM figures by changing PDF line-width operands only.

The canonical PDFs are never overwritten. Unsupported content fails closed.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

import pikepdf
import pymupdf

TEXT_WIDTH_PT = 6.151 * 72
MIN_STROKE_PT = 1.02


def _sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def _instructions(owner):
    result = list(pikepdf.parse_content_stream(owner))
    if any(not isinstance(x, pikepdf.ContentStreamInstruction) for x in result):
        raise ValueError('Inline images are unsupported; refusing to rewrite')
    return result


def _streams(pdf):
    """Visit every page and recursively reachable Form exactly once."""
    seen = set()

    def visit(owner, resources, label):
        yield label, owner
        for name, obj in resources.get('/XObject', {}).items():
            if obj.get('/Subtype') != '/Form':
                continue
            key = obj.objgen
            if key in seen:
                continue
            seen.add(key)
            yield from visit(obj, obj.get('/Resources', resources), label + '/' + str(name))

    for i, page in enumerate(pdf.pages):
        yield from visit(page, page.get('/Resources', {}), f'page-{i}')


def _rewrite(source, destination, factor, source_minimum):
    with pikepdf.open(source) as pdf:
        for _, owner in _streams(pdf):
            changed = []
            for instruction in _instructions(owner):
                operands, operator = instruction.operands, instruction.operator
                if str(operator) == 'w':
                    if len(operands) != 1 or float(operands[0]) < 0:
                        raise ValueError('Invalid w operand')
                    # Matplotlib emits w=0 for fill-only background patches.
                    # Replace even unused hairline state; visible source hairlines
                    # already fail the source drawing check below.
                    operands = [max(float(operands[0]), source_minimum * factor)]
                changed.append(pikepdf.ContentStreamInstruction(operands, operator))
            data = pikepdf.unparse_content_stream(changed)
            if isinstance(owner, pikepdf.Page):
                owner.Contents = pdf.make_stream(data)
            else:
                owner.write(data)
        pdf.save(destination, deterministic_id=True)


def _verify_tokens(source, destination):
    with pikepdf.open(source) as a, pikepdf.open(destination) as b:
        aa, bb = list(_streams(a)), list(_streams(b))
        assert [x[0] for x in aa] == [x[0] for x in bb], 'Form structure changed'
        count = 0
        for (label, x), (_, y) in zip(aa, bb):
            xx, yy = _instructions(x), _instructions(y)
            assert len(xx) == len(yy), label
            for old, new in zip(xx, yy):
                assert old.operator == new.operator, label
                if str(old.operator) == 'w':
                    assert len(new.operands) == 1 and float(new.operands[0]) > 0, label
                    count += 1
                else:
                    # Canonical serialization compares nested operands, strings and names.
                    assert pikepdf.unparse_content_stream([old]) == pikepdf.unparse_content_stream([new]), label
        return count


def _visible_widths(page):
    return [float(d['width']) for d in page.get_drawings()
            if 's' in d['type'] and d.get('stroke_opacity', 1) > 0]


def _verify_geometry(source, destination, scale):
    with pymupdf.open(source) as a, pymupdf.open(destination) as b:
        assert len(a) == len(b) == 1, 'Expected single-page figure'
        x, y = a[0], b[0]
        assert x.rect == y.rect and x.mediabox == y.mediabox, 'Page geometry changed'
        assert x.get_text('rawdict') == y.get_text('rawdict'), 'Text changed'
        assert x.get_image_info(hashes=True) == y.get_image_info(hashes=True), 'Images changed'
        old, new = x.get_drawings(), y.get_drawings()
        assert len(old) == len(new), 'Drawing count changed'
        for before, after in zip(old, new):
            before = dict(before)
            after = dict(after)
            before.pop('width', None)
            after.pop('width', None)
            assert before == after, 'Path coordinates, bounding rectangles, color or drawing state changed'
        widths = _visible_widths(y)
        assert widths and min(widths) * scale >= MIN_STROKE_PT - 1e-6, 'Final embedded stroke below minimum'
        return min(widths) * scale


def _manifest(root, main_tex, supplementary_tex):
    entries = []
    for folder, tex in [('paper', main_tex), ('supplementary', supplementary_tex)]:
        text = Path(tex).read_text(encoding='utf-8') if isinstance(tex, Path) else str(tex)
        text = re.sub(r'(?<!\\)%[^\n]*', '', text)
        matches = list(re.finditer(r'\\includegraphics\[([^]]*)\]\{([^}]+)\}', text))
        assert len(matches) == text.count(r'\includegraphics'), 'Unsupported includegraphics syntax'
        for match in matches:
            width = re.fullmatch(r'\s*width\s*=\s*([0-9.]+)\\(?:line|text)width\s*', match[1])
            assert width, f'Unsupported graphics dimensions: {match[0]}'
            relative = Path(match[2])
            assert relative.parent == Path('figures') and relative.suffix == '.pdf', relative
            entries.append((root / folder / relative, float(width[1])))
    assert len(entries) == 24 and len({p.name for p, _ in entries}) == 24, 'Expected 24 unique figures'
    return entries


def prepare_figures(root, output, main_tex, supplementary_tex, *, check=False):
    """Write derived PDFs directly into output and return/write auditable metrics.

    TeX arguments are source strings or pathlib.Path objects. check=True performs
    all source/token/geometry/minimum-width checks without regenerating PDFs.
    """
    root, output = Path(root), Path(output)
    output.mkdir(parents=True, exist_ok=True)
    records = []
    for source, coefficient in _manifest(root, main_tex, supplementary_tex):
        destination = output / source.name
        assert source.resolve() != destination.resolve(), 'Cannot overwrite canonical figure'
        source_hash = _sha(source)
        with pymupdf.open(source) as pdf:
            assert len(pdf) == 1
            scale = TEXT_WIDTH_PT * coefficient / pdf[0].rect.width
            widths = _visible_widths(pdf[0])
            assert widths and min(widths) > 0, 'Hairline or missing visible strokes'
            # A small serialization margin ensures the requested threshold survives PDF decimal rounding.
            factor = max(1., (MIN_STROKE_PT + 0.0001) / (min(widths) * scale))
        if not check:
            _rewrite(source, destination, factor, min(widths))
        token_count = _verify_tokens(source, destination)
        minimum = _verify_geometry(source, destination, scale)
        assert _sha(source) == source_hash, 'Canonical figure changed'
        records.append(dict(source=source.relative_to(root).as_posix(), output=destination.name,
                            source_sha256=source_hash, derived_sha256=_sha(destination),
                            width_coefficient=coefficient, embedding_scale=scale,
                            linewidth_floor_pdf_units=min(widths) * factor, final_min_linewidth_pt=minimum,
                            verified_w_operators=token_count, passed=True))
    metrics = dict(textwidth_in=6.151, target_min_linewidth_pt=MIN_STROKE_PT,
                   figure_count=len(records), all_passed=True, figures=records,
                   verification='Recursive PDF tokens: only w operands may differ; PyMuPDF paths, bounds, text, images and colors identical')
    if not check:
        (output / 'figure-metrics.json').write_text(json.dumps(metrics, indent=2) + '\n', encoding='utf-8')
    return metrics


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    metrics = prepare_figures(args.root, args.output, args.root / 'paper/main.tex',
                              args.root / 'supplementary/supplementary.tex', check=args.check)
    print(json.dumps(dict(figure_count=metrics['figure_count'], all_passed=metrics['all_passed'])))
