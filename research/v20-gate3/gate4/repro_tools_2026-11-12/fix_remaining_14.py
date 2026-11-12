#!/usr/bin/env python3
"""Gate 4: scope-limited LibreOffice equation-import compatibility patch.

- Style only literal interval delimiters, signs in three six-sign sequence displays,
  0+ one-sided limit sign, and standalone comparator formulas as normal math glyphs.
- For the single triangular-reachability aligned derivation, replace an OMML
  2x2 matrix (whose second row LibreOffice omitted) with a two-line native
  OMML equation-array containing the same mathematical tokens in the same order.
- Keep every m:oMath, every m:t token, all nonmath paragraphs and pictures.
"""
from zipfile import ZipFile, ZIP_DEFLATED
from lxml import etree
from copy import deepcopy
from collections import Counter
from pathlib import Path
import hashlib, sys
M='http://schemas.openxmlformats.org/officeDocument/2006/math';W='http://schemas.openxmlformats.org/wordprocessingml/2006/main'
N={'m':M,'w':W}; q=lambda x:'{'+M+'}'+x

def allmathtexts(root): return [x.text for x in root.xpath('//m:oMath//m:t',namespaces=N)]
def normal(r,c,why):
    rp=r.find(q('rPr'))
    if rp is None:rp=etree.Element(q('rPr'));r.insert(0,rp)
    if rp.find(q('nor')) is None:
        rp.insert(0,etree.Element(q('nor'))); c[why]+=1

def fix(src,dst):
    with ZipFile(src) as z: parts={i.filename:z.read(i.filename) for i in z.infolist()}
    root=etree.fromstring(parts['word/document.xml']);original=allmathtexts(root)
    before_math_count=len(root.xpath('//m:oMath',namespaces=N))
    c=Counter()
    for r in root.xpath('//m:oMath//m:r',namespaces=N):
        texts=r.findall(q('t'))
        if len(texts)==1 and (texts[0].text or '') in '()[]':
            normal(r,c,'standalone_interval_delimiter')
    for d in root.xpath('//m:oMath//m:d',namespaces=N):
        tokens=[x.text for x in d.xpath('.//m:t',namespaces=N)]
        if len(tokens)==11 and tokens.count(',')==5 and tokens.count('+')+tokens.count('−')==6:
            for r in d.xpath('.//m:r',namespaces=N):
                t=r.find(q('t'))
                if t is not None and (t.text or '') in ('+','−'):
                    normal(r,c,'three_edge_sign_lists')
        if ''.join(tokens)=='0+':
            for r in d.xpath('.//m:r',namespaces=N):
                t=r.find(q('t'))
                if t is not None and t.text=='+':normal(r,c,'one_sided_limit_plus')
    for om in root.xpath('//m:oMath',namespaces=N):
        children=[el for el in om if el.tag==q('r')]
        if children:
            r=children[0];t=r.find(q('t'))
            if t is not None and t.text in ('<','>') and ''.join(x.text or '' for x in om.xpath('.//m:t',namespaces=N)) in ('<1/4','<r/2'):
                normal(r,c,'initial_comparison')
    # Repair one 2-row aligned display whose second row was entirely hidden by LibreOffice.
    formulas=[]
    for om in root.xpath('//m:oMath',namespaces=N):
        mat=om.find(q('m'))
        if mat is None:continue
        rows=mat.findall(q('mr'))
        if len(rows)!=2:continue
        text=''.join(x.text or '' for x in om.xpath('.//m:t',namespaces=N))
        if not (text.startswith('w6z=') and 'Kz2j' in text and text.endswith('z3.')):continue
        arr=etree.Element(q('eqArr'))
        prop=etree.SubElement(arr,q('eqArrPr'))
        etree.SubElement(prop,q('baseJc'),attrib={q('val'):'center'})
        for row in rows:
            e=etree.SubElement(arr,q('e'))
            for cell in row.findall(q('e')):
                for child in cell:e.append(deepcopy(child))
        om.replace(mat,arr)
        c['aligned_derivation_matrix_to_equation_array']+=1
        formulas.append(text)
    assert c['aligned_derivation_matrix_to_equation_array']==1,c
    assert allmathtexts(root)==original, 'Math tokens altered'
    assert len(root.xpath('//m:oMath',namespaces=N))==before_math_count, 'OMML math count altered'
    assert c['initial_comparison']==2,c
    parts['word/document.xml']=etree.tostring(root,encoding='UTF-8',xml_declaration=True,standalone=True)
    with ZipFile(dst,'w',ZIP_DEFLATED,compresslevel=7) as z:
        for k,v in parts.items():z.writestr(k,v)
    assert ZipFile(dst).testzip() is None
    return {'source':str(src),'out':str(dst),'math_objects':before_math_count,'math_token_count':len(original),'changes':dict(c),'sha256':hashlib.sha256(Path(dst).read_bytes()).hexdigest()}
if __name__=='__main__':print(fix(Path(sys.argv[1]),Path(sys.argv[2])))