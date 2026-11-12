#!/usr/bin/env python3
import fitz,json,hashlib,zipfile
from lxml import etree
from pathlib import Path
from collections import Counter
from PIL import Image,ImageOps,ImageDraw
ROOT=Path('/mnt/data')
OUT=ROOT/'gate4_followup'
M='http://schemas.openxmlformats.org/officeDocument/2006/math';W='http://schemas.openxmlformats.org/wordprocessingml/2006/main'; ns={'m':M,'w':W};
m='{'+M+'}';w='{'+W+'}'

def doc_info(path):
 with zipfile.ZipFile(path) as z:
  assert z.testzip() is None
  parts={p:z.read(p) for p in z.namelist() if p.startswith('word/media/')}
  xml=etree.fromstring(z.read('word/document.xml'))
  math=xml.xpath('//m:oMath',namespaces=ns)
  tokens=[el.text or '' for el in xml.xpath('//m:oMath//m:t',namespaces=ns)]
  paras=xml.xpath('.//w:body//w:p',namespaces=ns)
  word_text=[el.text for el in xml.xpath('//w:body//w:t',namespaces=ns)]
  return dict(sha256=hashlib.sha256(path.read_bytes()).hexdigest(),math_count=len(math),tokens=tokens,paragraph_count=len(paras),word_text=word_text,media_sha={p:hashlib.sha256(b).hexdigest() for p,b in parts.items()},eqarr_count=len(xml.xpath('//m:eqArr',namespaces=ns)),matrix_count=len(xml.xpath('//m:m',namespaces=ns)))

def pdf_info(pdf):
 d=fitz.open(pdf);pages=[]; all_glyphs=0
 for page in d:
  s=page.get_text()
  oob=[(b[0],b[1],b[2],b[3]) for b in page.get_text('blocks') if len(b)>=7 and b[6]==0 and (b[0]<-2 or b[1]<-2 or b[2]>page.rect.width+2 or b[3]>page.rect.height+2)]
  bad=s.count('¿');all_glyphs+=bad
  pages.append(dict(page=page.number+1,text_chars=len(s),bad_glyphs=bad,out_of_bounds=oob))
 assert all(p['text_chars']>100 for p in pages)
 assert not any(p['out_of_bounds'] for p in pages)
 return dict(page_count=len(d),bad_glyphs=all_glyphs,pages=pages)

result={}
for lang in ['English','Chinese']:
 old=ROOT/f'Gate4_When_Can_Markets_Crash_{lang}_Full_Editable_ReviewReady_v20.docx'
 new=ROOT/f'Gate4_When_Can_Markets_Crash_{lang}_Full_Editable_RenderVerified_v20.docx'
 p=OUT/f'{lang.lower()}_rendered'/f'Gate4_When_Can_Markets_Crash_{lang}_Full_Editable_RenderVerified_v20.pdf'
 a=doc_info(old);b=doc_info(new);c=pdf_info(p)
 assert a['math_count']==b['math_count']==1326
 assert len(a['tokens'])==len(b['tokens'])==9716
 assert a['tokens']==b['tokens']
 assert a['word_text']==b['word_text']
 assert a['paragraph_count']==b['paragraph_count']
 assert a['media_sha']==b['media_sha']
 assert b['eqarr_count']==a['eqarr_count']+1 and b['matrix_count']==a['matrix_count']-1
 assert c['bad_glyphs']==0
 assert c['page_count']==31
 result[lang]={'old_sha256':a['sha256'],'repaired_sha256':b['sha256'],'OMML_nodes':b['math_count'],'math_text_tokens':len(b['tokens']),'all_math_text_identical':True,'all_nonmath_word_text_identical':True,'media_files_identical':True,'paragraphs':b['paragraph_count'],'eqarr_count_change':1,'matrix_count_change':-1,**c}
 # Contact sheet thumbnails for 31-pages visual QA
 files=list(sorted((OUT/f'{lang.lower()}_rendered').glob('page-*.png'),key=lambda x:int(x.stem.split('-')[-1])))
 assert len(files)==31
 tw,th=248,352;cols=5;rows=(len(files)+cols-1)//cols
 sheet=Image.new('RGB',(cols*tw,rows*(th+22)),(245,246,248)); dr=ImageDraw.Draw(sheet)
 for idx,f in enumerate(files):
  im=Image.open(f).convert('RGB');im.thumbnail((tw-8,th))
  x=(idx%cols)*tw+(tw-im.width)//2;y=(idx//cols)*(th+22)
  sheet.paste(im,(x,y))
  dr.text(((idx%cols)*tw+10,y+th),f'{lang} page {idx+1}',fill=(0,0,0))
 sheet.save(OUT/f'{lang.lower()}_all_pages_contact.png')
(OUT/'GATE4_FOLLOWUP_RENDER_QA_2026-11-12.json').write_text(json.dumps(result,ensure_ascii=False,indent=2),encoding='utf8')
print(json.dumps({k:{kk:v[kk] for kk in ['old_sha256','repaired_sha256','OMML_nodes','math_text_tokens','paragraphs','page_count','bad_glyphs']} for k,v in result.items()},indent=2))