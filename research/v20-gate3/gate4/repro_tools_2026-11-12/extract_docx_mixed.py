from lxml import etree
from pathlib import Path
from zipfile import ZipFile
from copy import deepcopy
import json, sys, re
p=Path('/mnt/data/gate4_input/extracted/english_siam/When_Can_Markets_Crash_English_Editable_Review_v20.docx')
W='http://schemas.openxmlformats.org/wordprocessingml/2006/main';M='http://schemas.openxmlformats.org/officeDocument/2006/math';A='http://schemas.openxmlformats.org/drawingml/2006/main'
with ZipFile(p) as z: xml=z.read('word/document.xml')
root=etree.fromstring(xml)
ns={'w':W,'m':M,'a':A}
body=root.find('{'+W+'}body')
allpars=body.xpath('.//w:p',namespaces=ns)

def rec_elem(x,out):
 if x.tag in ('{'+M+'}oMath','{'+M+'}oMathPara'):
  out.append(('M',str(len([t for t in out if t[0]=='M']))));return
 if x.tag in ('{'+W+'}drawing','{'+W+'}pict'):
  out.append(('IMG',str(len([t for t in out if t[0]=='IMG']))));return
 if x.tag in ('{'+W+'}t','{'+W+'}instrText'):
  out.append(('T',x.text or ''));return
 if x.tag=='{'+W+'}tab':out.append(('T','\t'));return
 if x.tag=='{'+W+'}br':out.append(('T','\n'));return
 for c in x:
  if c.tag=='{'+W+'}pPr':continue
  rec_elem(c,out)

def compact(out):
 s=''
 for ty,t in out:
  if ty=='T':s+=t
  elif ty=='M':s+=f'⟦M{t}⟧'
  elif ty=='IMG':s+=f'⟦IMG{t}⟧'
 return s
ps=[]
for i,par in enumerate(allpars):
 out=[];rec_elem(par,out)
 sty=par.find('.//{'+W+'}pStyle')
 style=sty.get('{'+W+'}val') if sty is not None else ''
 text=compact(out)
 ps.append({'idx':i,'style':style,'text':text,'len':len(text),'math_count':len([a for a in out if a[0]=='M']),'image_count':len([a for a in out if a[0]=='IMG'])})
Path('/mnt/data/gate4_input/docx_paras.json').write_text(json.dumps(ps,indent=2,ensure_ascii=False),encoding='utf8')
print('all',len(ps),'nonempty',sum(bool(x['text'].strip()) for x in ps),'math',sum(x['math_count'] for x in ps),'imgs',sum(x['image_count'] for x in ps))
for x in ps[:45]:print(f"P{x['idx']:03} {x['style']:<16} m={x['math_count']:2} im={x['image_count']} {x['text'][:500]}")