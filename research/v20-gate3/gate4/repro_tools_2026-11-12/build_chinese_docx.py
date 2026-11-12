#!/usr/bin/env python3
"""Gate 4 bilingual manuscript: preserve literal Word OMML and figure XML, replace only ordinary prose.
Source English Word and translations are strictly pinned; no repair or alteration of scientific claims.
"""
from pathlib import Path
from zipfile import ZipFile, ZIP_DEFLATED
from lxml import etree
from copy import deepcopy
import json,re,hashlib,sys
BASE=Path('/mnt/data/gate4_input')
ORIGIN=BASE/'extracted/english_siam/When_Can_Markets_Crash_English_Editable_Review_v20.docx'
DEST=Path('/mnt/data/Gate4_When_Can_Markets_Crash_Chinese_Full_Editable_Review_v20.docx')
W='http://schemas.openxmlformats.org/wordprocessingml/2006/main';M='http://schemas.openxmlformats.org/officeDocument/2006/math';XML='http://www.w3.org/XML/1998/namespace'
q=lambda ns,x:'{'+ns+'}'+x
ns={'w':W,'m':M}
paras=json.loads((BASE/'docx_paras.json').read_text('utf8'))
zh={}
for l in (BASE/'translations.psv').read_text('utf8').splitlines():
 a,b=l.split('|',1);idx=int(a)
 if idx in zh:raise ValueError(f'dup {idx}')
 zh[idx]=b.replace('\\n','\n')
assert len(zh)==259
for idx,s in zh.items():
 refs=[int(x) for x in re.findall(r'⟦M(\d+)⟧',s)]
 imgs=[int(x) for x in re.findall(r'⟦IMG(\d+)⟧',s)]
 assert sorted(refs)==list(range(paras[idx]['math_count'])),(idx,refs)
 assert sorted(imgs)==list(range(paras[idx]['image_count'])),(idx,imgs)
with ZipFile(ORIGIN) as z: parts={x.filename:z.read(x.filename) for x in z.infolist()}
root=etree.fromstring(parts['word/document.xml'])
pnodes=root.find(q(W,'body')).xpath('.//w:p',namespaces=ns)
assert len(pnodes)==len(paras)
math_signature_original=[hashlib.sha256(etree.tostring(e)).hexdigest() for e in root.xpath('//m:oMath',namespaces=ns)]
images_orig=len(root.xpath('//w:drawing',namespaces=ns))

def rec(x,mobjs,imobjs):
 if x.tag in (q(M,'oMath'),q(M,'oMathPara')):
  mobjs.append(deepcopy(x));return
 if x.tag in (q(W,'drawing'),q(W,'pict')):
  # preservation only the drawing/pict inside a new run
  imobjs.append(deepcopy(x));return
 if x.tag==q(W,'pPr'):return
 for c in x:rec(c,mobjs,imobjs)

def new_run(s,style=None):
 run=etree.Element(q(W,'r'))
 props=etree.SubElement(run,q(W,'rPr'))
 rfonts=etree.SubElement(props,q(W,'rFonts'))
 rfonts.set(q(W,'ascii'),'Liberation Serif')
 rfonts.set(q(W,'hAnsi'),'Liberation Serif')
 rfonts.set(q(W,'eastAsia'),'Noto Serif CJK SC')
 etree.SubElement(props,q(W,'lang')).set(q(W,'eastAsia'),'zh-CN')
 if style=='bold':etree.SubElement(props,q(W,'b'))
 elif style=='italic':etree.SubElement(props,q(W,'i'))
 for j,line in enumerate(s.split('\n')):
  if j:etree.SubElement(run,q(W,'br'))
  if not line:continue
  t=etree.SubElement(run,q(W,'t'))
  t.set(q(XML,'space'),'preserve');t.text=line
 return run

for i,s in zh.items():
 p=pnodes[i]
 mobj=[];imobj=[];rec(p,mobj,imobj)
 assert len(mobj)==paras[i]['math_count'],(i,len(mobj),paras[i]['math_count'])
 assert len(imobj)==paras[i]['image_count'],(i,len(imobj))
 pnew=etree.Element(q(W,'p'))
 ppr=p.find(q(W,'pPr'))
 if ppr is not None:pnew.append(deepcopy(ppr))
 matches=list(re.finditer(r'⟦(M|IMG)(\d+)⟧',s))
 # To preserve bold theorem labels and proof labels, apply only to literal prefix before first math object.
 is_theorem=bool(re.match(r'^(定理|引理|命题|推论|定义)\s*[A-Z0-9]',s))
 is_proof=s.startswith('证明。')
 def write_text(txt,first):
  if not txt:return
  if first and is_theorem:
   mm=re.match(r'^(?:定理|引理|命题|推论|定义)\s*[A-Za-z]?\d+(?:\.\d+)?',txt)
   if mm:
    pnew.append(new_run(txt[:mm.end()],'bold'));txt=txt[mm.end():]
  if first and is_proof and txt.startswith('证明。'):
   pnew.append(new_run('证明。','italic'));txt=txt[3:]
  if txt:pnew.append(new_run(txt))
 start=0
 for j,mat in enumerate(matches):
  write_text(s[start:mat.start()],j==0)
  typ,num=mat.group(1),int(mat.group(2))
  if typ=='M':pnew.append(deepcopy(mobj[num]))
  else:
   r=etree.Element(q(W,'r'))
   r.append(deepcopy(imobj[num]))
   pnew.append(r)
  start=mat.end()
 write_text(s[start:],len(matches)==0)
 parent=p.getparent()
 parent.replace(p,pnew)

new_sigs=[hashlib.sha256(etree.tostring(e)).hexdigest() for e in root.xpath('//m:oMath',namespaces=ns)]
assert len(new_sigs)==len(math_signature_original)==1326,(len(new_sigs),len(math_signature_original))
assert sorted(new_sigs)==sorted(math_signature_original),'Math XML changed'
assert len(root.xpath('//w:drawing',namespaces=ns))==images_orig==6
assert len(root.xpath('//w:tbl',namespaces=ns))==2
# Add bibliographic section heading without altering the pinned paragraph map.
orig_bib=pnodes[370]
bibheading=etree.Element(q(W,'p'))
pp=etree.SubElement(bibheading,q(W,'pPr'))
etree.SubElement(pp,q(W,'pStyle')).set(q(W,'val'),'Heading1')
bibheading.append(new_run('参考文献'))
orig_bib.getparent().insert(orig_bib.getparent().index(orig_bib),bibheading)
parts['word/document.xml']=etree.tostring(root,encoding='UTF-8',xml_declaration=True,standalone=True)
# Translate review headers, page labels and author affiliation; leave bibliography unchanged.
head=etree.fromstring(parts['word/header1.xml'])
for t in head.iter(q(W,'t')):
 if 'English manuscript' in (t.text or ''):
  t.text='市场为何会在没有消息的情况下崩盘？ ｜ 中文审阅稿'
parts['word/header1.xml']=etree.tostring(head,encoding='UTF-8',xml_declaration=True,standalone=True)
foot=etree.fromstring(parts['word/footer1.xml'])
for t in foot.iter(q(W,'t')):
 if t.text=='Page ':t.text='第 '
for f in foot.iter(q(W,'fldSimple')):
 if f.get(q(W,'instr'))=='PAGE':
  p=f.getparent();idx=p.index(f)
  rr=etree.Element(q(W,'r'))
  tt=etree.SubElement(rr,q(W,'t'));tt.text=' 页'
  p.insert(idx+1,rr)
parts['word/footer1.xml']=etree.tostring(foot,encoding='UTF-8',xml_declaration=True,standalone=True)
ff=etree.fromstring(parts['word/footnotes.xml'])
for fn in ff.iter(q(W,'footnote')):
 if fn.get(q(W,'id'))=='20':
  ps=fn.findall('.//'+q(W,'p'))
  for pr in ps:
   ts=list(pr.iter(q(W,'t')))
   if ts:
    ts[0].text=' 独立研究者。'
    for t in ts[1:]:t.text=''
parts['word/footnotes.xml']=etree.tostring(ff,encoding='UTF-8',xml_declaration=True,standalone=True)

with ZipFile(DEST,'w',ZIP_DEFLATED,compresslevel=7) as z:
 for k,v in parts.items():z.writestr(k,v)
with ZipFile(DEST) as z:
 assert z.testzip() is None
assert len(re.findall(r'⟦M\d+⟧',parts['word/document.xml'].decode('utf8')))==0
print('OUTPUT',DEST,'bytes',DEST.stat().st_size,'translated paras',len(zh),'original OMML',len(new_sigs),'figures',images_orig)
print('SHA-256',hashlib.sha256(DEST.read_bytes()).hexdigest())