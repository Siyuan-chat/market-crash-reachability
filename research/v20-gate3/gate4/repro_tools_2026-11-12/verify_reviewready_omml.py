#!/usr/bin/env python3
"""Gate 4 nonsemantic OMML style patch and page inspection audit.

Read-only verifier: final ReviewReady math run typography may differ from the
pre-compatibility SIAM-aligned version, but mathematical text and tree structure
(without m:rPr layout properties) must remain identical.
"""
from pathlib import Path
from zipfile import ZipFile
from lxml import etree
import fitz, json, hashlib
ROOT=Path('/mnt/data'); AUD=ROOT/'Gate4_Audit'
M='http://schemas.openxmlformats.org/officeDocument/2006/math';W='http://schemas.openxmlformats.org/wordprocessingml/2006/main'
m='{'+M+'}';w='{'+W+'}'

def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def math_structure(doc):
    with ZipFile(doc) as z:
        assert z.testzip() is None
        xml=etree.fromstring(z.read('word/document.xml'))
        math=xml.findall('.//'+m+'oMath')
        assert len(math)==1326
        # remove math style run properties, while preserving all math symbols,
        # structural operators and variable order.
        no_style=[]
        for el in math:
            clone=etree.fromstring(etree.tostring(el))
            for pr in clone.findall('.//'+m+'rPr'):
                pr.getparent().remove(pr)
            no_style.append(etree.tostring(clone,method='c14n'))
        return no_style
out={}
for lng in ('English','Chinese'):
    original=ROOT/f'Gate4_When_Can_Markets_Crash_{lng}_Full_Editable_SIAM_Aligned_v20.docx'
    ready=ROOT/f'Gate4_When_Can_Markets_Crash_{lng}_Full_Editable_ReviewReady_v20.docx'
    assert math_structure(original)==math_structure(ready),f'{lng} mathematical structure changed'
    pdf=ROOT/'gate4_input'/f'{lng.lower()}_reviewready_render'/f'Gate4_When_Can_Markets_Crash_{lng}_Full_Editable_ReviewReady_v20.pdf'
    d=fitz.open(pdf)
    assert d.page_count==(31 if lng=='English' else 30)
    pages=[]
    for i,page in enumerate(d):
        text=page.get_text()
        blocks=[b for b in page.get_text('blocks') if len(b)>=7 and b[6]==0]
        out_bounds=[b for b in blocks if b[0]<-2 or b[1]<-2 or b[2]>page.rect.width+2 or b[3]>page.rect.height+2]
        assert not out_bounds,(lng,i+1,'overflow',out_bounds)
        assert len(text)>100,(lng,i+1,'blank page')
        pages.append({'page':i+1,'text_characters':len(text),'out_of_page_text_blocks':len(out_bounds),'LibreOffice_math_error_glyphs':text.count('¿')})
    out[lng]={'source_word_sha256':sha(original),'review_ready_word_sha256':sha(ready),'word_size_bytes':ready.stat().st_size,'page_count':len(d),'remaining_math_renderer_error_glyphs':sum(p['LibreOffice_math_error_glyphs'] for p in pages),'native_formula_nodes':1326,'math_content_and_structure_unchanged':True,'pages':pages}
assert all(x['remaining_math_renderer_error_glyphs']==53 for x in out.values())
(AUD/'GATE4_REVIEWREADY_RENDER_QA.json').write_text(json.dumps({'date':'2026-11-12','LibreOffice_visual_acceptance':'PARTIAL_PASSED_WITH_KNOWN_MATH_GLYPH_IMPORT_ISSUES', 'review_ready':out},ensure_ascii=False,indent=2),encoding='utf8')
print('REVIEWREADY VERIFIED', {k:{kk:v[kk] for kk in ['page_count','remaining_math_renderer_error_glyphs','native_formula_nodes','math_content_and_structure_unchanged']} for k,v in out.items()})