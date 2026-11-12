#!/usr/bin/env python3
"""Correct Word (EN+ZH) bib/citation numbering against genuine frozen SIAM main.bbl.
Non-destructive: input DOCX artifacts untouched, emits separate SIAM-numbered versions.
"""
from pathlib import Path
from zipfile import ZipFile,ZIP_DEFLATED
from lxml import etree
import re,hashlib,sys

OLD_TO_NEW={1:10,2:15,3:11,4:6,5:8,6:5,7:14,8:1,9:9,10:12,11:3,12:7,13:4,14:2,15:16,16:13}
assert sorted(OLD_TO_NEW.values())==list(range(1,17))
ROOT=Path('/mnt/data');W='http://schemas.openxmlformats.org/wordprocessingml/2006/main';w='{'+W+'}'
SOURCES={
 'EN':ROOT/'Gate4_When_Can_Markets_Crash_English_Editable_Review_v20_Checked.docx',
 'ZH':ROOT/'Gate4_When_Can_Markets_Crash_Chinese_Full_Editable_Review_v20.docx'}
for lang,src in SOURCES.items():
 dest=ROOT/f'Gate4_When_Can_Markets_Crash_{"English" if lang=="EN" else "Chinese"}_Full_Editable_SIAM_Aligned_v20.docx'
 with ZipFile(src) as z:parts={i.filename:z.read(i.filename) for i in z.infolist()}
 root=etree.fromstring(parts['word/document.xml']);ps=root.findall('.//'+w+'p')
 assert len(ps)==387,(lang,len(ps))
 # 16 bibliography paragraphs after new heading at index 370
 bib=ps[371:387]
 assert len(bib)==16
 # Replace in-text citations only, not equation numbers.
 citations_old=[]
 for i,p in enumerate(ps[:370]):
  for t in p.iter(w+'t'):
   if t.text and re.search(r'\[\d+\]',t.text):
    citations_old.extend(int(x) for x in re.findall(r'\[(\d+)\]',t.text))
    t.text=re.sub(r'\[(\d+)\]',lambda m:f'[{OLD_TO_NEW[int(m.group(1))]}]',t.text)
 assert set(citations_old)==set(range(1,17)),(lang,citations_old)
 parent=bib[0].getparent();at=parent.index(bib[0]);assert all(p.getparent()==parent for p in bib)
 for p in bib:parent.remove(p)
 for old,p in enumerate(bib,1):
  t=next(p.iter(w+'t'))
  assert re.fullmatch(r'\['+str(old)+r'\]',t.text or ''),(lang,old,t.text)
  t.text=f'[{OLD_TO_NEW[old]}]'
  if old==16:
   # Ensure completeness with the SIAM .bbl, which explicitly states the access month.
   all_t=list(p.iter(w+'t'))
   all_t[-1].text=(all_t[-1].text or '') + ' Accessed October 2026.'
 for new,old in enumerate(sorted(OLD_TO_NEW,key=lambda k:OLD_TO_NEW[k]),1):
  assert OLD_TO_NEW[old]==new
  parent.insert(at+new-1,bib[old-1])
 parts['word/document.xml']=etree.tostring(root,encoding='UTF-8',xml_declaration=True,standalone=True)
 with ZipFile(dest,'w',ZIP_DEFLATED,compresslevel=7) as z:
  for k,v in parts.items():z.writestr(k,v)
 with ZipFile(dest) as z:assert z.testzip() is None
 print(lang,'OUT',dest,'size',dest.stat().st_size,'sha256',hashlib.sha256(dest.read_bytes()).hexdigest())
 print('REN NUMBER',[(k,OLD_TO_NEW[k]) for k in sorted(OLD_TO_NEW)])