#!/usr/bin/env python3
"""Non-destructive minimal repair of English editable review: authentic captions/references heading."""
from zipfile import ZipFile,ZIP_DEFLATED
from pathlib import Path
from lxml import etree
from copy import deepcopy
import hashlib
base=Path('/mnt/data/gate4_input/extracted/english_siam/When_Can_Markets_Crash_English_Editable_Review_v20.docx')
out=Path('/mnt/data/Gate4_When_Can_Markets_Crash_English_Editable_Review_v20_Checked.docx')
W='http://schemas.openxmlformats.org/wordprocessingml/2006/main';M='http://schemas.openxmlformats.org/officeDocument/2006/math'
Q=lambda x:'{'+W+'}'+x
with ZipFile(base) as z: parts={x.filename:z.read(x.filename) for x in z.infolist()}
root=etree.fromstring(parts['word/document.xml'])
pars=root.findall('.//'+Q('p'))
assert len(pars)==386,len(pars)
text_prefix={176:'Figure 1. ',178:'Figure 2. ',180:'Figure 3. ',182:'Figure 4. ',183:'Table 1. ',212:'Table 2. ',239:'Figure 5. ',241:'Figure 6. '}
for i,prefix in text_prefix.items():
 p=pars[i];r=etree.Element(Q('r'))
 t=etree.SubElement(r,Q('t'));t.set('{http://www.w3.org/XML/1998/namespace}space','preserve');t.text=prefix
 ind=1 if p.find(Q('pPr')) is not None else 0
 p.insert(ind,r)
# Insert bibliography heading immediately before 16 original bibliography paragraphs
bibliography_p=pars[370]
parent=bibliography_p.getparent()
assert parent.tag==Q('body')
refs=etree.Element(Q('p'));ppr=etree.SubElement(refs,Q('pPr'));etree.SubElement(ppr,Q('pStyle')).set(Q('val'),'Heading1')
r=etree.SubElement(refs,Q('r'));t=etree.SubElement(r,Q('t'));t.text='References'
parent.insert(parent.index(bibliography_p),refs)
parts['word/document.xml']=etree.tostring(root,encoding='UTF-8',xml_declaration=True,standalone=True)
with ZipFile(out,'w',ZIP_DEFLATED,compresslevel=7) as z:
 for k,v in parts.items():z.writestr(k,v)
print(out, 'bytes',out.stat().st_size,'sha',hashlib.sha256(out.read_bytes()).hexdigest())