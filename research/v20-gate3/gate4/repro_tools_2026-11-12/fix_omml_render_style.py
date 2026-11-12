#!/usr/bin/env python3
"""Modify ONLY presentation properties m:nor to render sign-only math scripts in LibreOffice.
The mathematical node sequence, equation data m:t, and structure apart from run typography remain intact.
"""
from lxml import etree
from zipfile import ZipFile,ZIP_DEFLATED
from pathlib import Path
from copy import deepcopy
from collections import Counter
import hashlib,sys
M='http://schemas.openxmlformats.org/officeDocument/2006/math'; W='http://schemas.openxmlformats.org/wordprocessingml/2006/main'; q=lambda x:'{'+M+'}'+x

def patch(src,dst):
 with ZipFile(src) as z:parts={x.filename:z.read(x.filename) for x in z.infolist()}
 root=etree.fromstring(parts['word/document.xml'])
 before=[(x.tag,x.text) for x in root.iter() if x.tag==q('t')]
 changed=Counter()
 # Only standalone math signs rendered as red invalid-token errors by LibreOffice import.
 for script in root.xpath('//m:sub | //m:sup',namespaces={'m':M}):
  for r in script.xpath('.//m:r',namespaces={'m':M}):
   texts=list(r.iter(q('t')))
   if not texts:continue
   if ''.join(t.text or '' for t in texts).strip() not in ('+','−','-','±','∓'):continue
   prop=r.find(q('rPr'))
   if prop is None:prop=etree.Element(q('rPr'));r.insert(0,prop)
   if prop.find(q('nor')) is None:
    prop.insert(0,etree.Element(q('nor')))
    changed['sign_only_sub_or_sup']+=1
 # Punctuation embedded as terminal math tokens can produce LO parser red error glyphs
 for om in root.xpath('//m:oMath',namespaces={'m':M}):
  for r in om.xpath('.//m:r',namespaces={'m':M}):
   texts=list(r.iter(q('t')))
   if len(texts)!=1 or (texts[0].text or '') not in ('.',';',':'):continue
   if any(y.tag==q('sub') for y in r.iterancestors()):continue
   prop=r.find(q('rPr'))
   if prop is None:prop=etree.Element(q('rPr'));r.insert(0,prop)
   if prop.find(q('nor')) is None:
    prop.insert(0,etree.Element(q('nor')))
    changed['math_punctuation']+=1
 # Fix math relation symbols at start of aligned right-hand cells: LO treats them as invalid unary operators.
 for row in root.xpath('//m:mr',namespaces={'m':M}):
  cells=row.findall(q('e'))
  if len(cells)<2:continue
  for cell in cells[1:]:
   child_elems=[el for el in cell if el.tag!=q('ePr')]
   if not child_elems:continue
   el=child_elems[0]
   if el.tag!=q('r'):continue
   texts=list(el.iter(q('t')))
   if not texts or (texts[0].text or '').strip() not in ('=','≤','≥','<','>','≈','→','⇒','≡'):continue
   prop=el.find(q('rPr'))
   if prop is None:prop=etree.Element(q('rPr'));el.insert(0,prop)
   if prop.find(q('nor')) is None:
    prop.insert(0,etree.Element(q('nor')))
    changed['leading_matrix_relation']+=1
 after=[(x.tag,x.text) for x in root.iter() if x.tag==q('t')]
 assert before==after,'Math text changed'
 parts['word/document.xml']=etree.tostring(root,encoding='UTF-8',xml_declaration=True,standalone=True)
 with ZipFile(dst,'w',ZIP_DEFLATED,compresslevel=7) as z:
  for k,v in parts.items():z.writestr(k,v)
 print(dst,changed,'sha256',hashlib.sha256(Path(dst).read_bytes()).hexdigest())

if __name__=='__main__':patch(sys.argv[1],sys.argv[2])