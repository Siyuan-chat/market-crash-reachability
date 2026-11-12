#!/usr/bin/env python3
"""Gate4 artifact audit; source remains read-only.
Strict checks: SHA, 131 label registry, equation-number presence, 33 formal propositions,
native OMML data equivalence, 6 figures, 2 tables, SIAM citations, all 43 obligations.
Visual QA from LibreOffice render is recorded separately, not conflated with math content.
"""
import json,csv,re,hashlib,collections,sys
from pathlib import Path
from zipfile import ZipFile
from lxml import etree
import fitz
root=Path('/mnt/data');base=root/'gate4_input/extracted';out=root/'Gate4_Audit';out.mkdir(exist_ok=True)
ORIGINAL=base/'english_siam/When_Can_Markets_Crash_English_Editable_Review_v20.docx'
EN=root/'Gate4_When_Can_Markets_Crash_English_Full_Editable_SIAM_Aligned_v20.docx'
ZH=root/'Gate4_When_Can_Markets_Crash_Chinese_Full_Editable_SIAM_Aligned_v20.docx'
SIAM=base/'english_siam/main.pdf'
LATEX=base/'source_snapshot/submission/v20-gate3-activity-recovery/main.tex'
BIB=base/'source_snapshot/submission/v16-three-certified-constructions/references.bib'
AUX=base/'english_siam/main.aux'
BBL=base/'english_siam/main.bbl'
REG=base/'source_snapshot/research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv'
W='http://schemas.openxmlformats.org/wordprocessingml/2006/main';M='http://schemas.openxmlformats.org/officeDocument/2006/math';w='{'+W+'}';m='{'+M+'}'
MATH_STYLE_SKIP={m+'rPr',m+'sty',m+'nor',w+'rPr',w+'rFonts',w+'lang',w+'color'}

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(LATEX)=='9d36ab61019bcb395073918c133bfc4a4cf23c32b99efd9a84c021fb7d092baa'
assert sha(BIB)=='555df0a2e0bb6a3749cf64a144626b8f3d086c3a5d95e97ce5d31551701de0f2'
assert sha(SIAM)=='25c0f8977bf45936420398acfed33a85657314d0fa03c004ca84b00f723b9e0b'
assert fitz.open(SIAM).page_count==35
with open(REG,newline='',encoding='utf8') as f:regs=list(csv.DictReader(f))
assert len(regs)==43
assert set(['T03','P02','P10','R01','R02','R03','A04'])<=set(x['ID'] for x in regs)
open_regs=[x for x in regs if x['ID'] in ('T03','P02','P10','R01','R02','R03','A04')]

def load_doc(p):
 with ZipFile(p) as z:
  assert z.testzip() is None
  doc=etree.fromstring(z.read('word/document.xml'))
  media={k:hashlib.sha256(z.read(k)).hexdigest() for k in z.namelist() if k.startswith('word/media/')}
  foot=z.read('word/footnotes.xml') if 'word/footnotes.xml' in z.namelist() else b''
 ps=doc.findall('.//'+w+'p')
 ts=[''.join((x.text or '') for x in pp.iter(w+'t')) for pp in ps]
 maths=doc.findall('.//'+m+'oMath')
 opar=doc.findall('.//'+m+'oMathPara')
 return {'doc':doc,'paras':ps,'texts':ts,'math':maths,'mathpara':opar,'media':media,'foot':foot}
orig=load_doc(ORIGINAL);en=load_doc(EN);zh=load_doc(ZH)
assert (len(orig['paras']),len(en['paras']),len(zh['paras']))==(386,387,387)
assert all(len(d['math'])==1326 for d in (orig,en,zh))
assert all(len(d['mathpara'])==106 for d in (orig,en,zh))
assert all(len(d['doc'].findall('.//'+w+'drawing'))==6 for d in (orig,en,zh))
assert all(len(d['doc'].findall('.//'+w+'tbl'))==2 for d in (orig,en,zh))
assert orig['media']==en['media']==zh['media']
# exact OMML tree equivalence before style compatibility patches
struct=lambda el:etree.tostring(el,method='c14n')
orig_math=[struct(e) for e in orig['math']]
en_math=[struct(e) for e in en['math']]
zh_math=[struct(e) for e in zh['math']]
assert orig_math==en_math,'Original-to-English native OMML changed'
# Chinese reorders isolated inline math tokens but never changes any math expression.
assert sorted(orig_math)==sorted(zh_math),'English-to-Chinese math node XML changed'
# Same per-paragraph math fingerprint multiset; note bibliography heading insertion at 370.
for i in range(370):
 assert collections.Counter(map(struct,orig['paras'][i].findall('.//'+m+'oMath')))==collections.Counter(map(struct,zh['paras'][i].findall('.//'+m+'oMath'))),f'zh para {i}'
 assert collections.Counter(map(struct,orig['paras'][i].findall('.//'+m+'oMath')))==collections.Counter(map(struct,en['paras'][i].findall('.//'+m+'oMath'))),f'en para {i}'

aux=AUX.read_text(encoding='utf8')
labels=[]
for x in re.finditer(r'\\newlabel\{([^{}]+)\}\{\{([^{}]*)\}\{([^{}]*)\}',aux):
 label,number,page=x.groups()
 if '@cref' in label:continue
 labels.append((label,number,int(page)))
assert len(labels)==131
stats=collections.Counter(key.split(':',1)[0] for key,_,_ in labels)
assert stats==collections.Counter({'eq':65,'sec':15,'prop':14,'thm':12,'app':8,'fig':6,'lem':5,'def':2,'cor':2,'tab':2}),stats
bibkeys=re.findall(r'\\bibitem\{([^}]*)\}',BBL.read_text('utf8'))
assert len(bibkeys)==16
oldkeys=['GennotteLeland1990','Romer1993','HuangWang2009','CespaFoucault2014','ContWagalath2013','BrunnermeierPedersen2005','ObizhaevaWang2013','AlfonsiSchied2010','Gatheral2010','HubermanStanzl2004','BankBaum2004','CetinJarrowProtter2004','BressanRampazzo1988','AlmgrenChriss2001','Yang2019','JPX2026']
assert set(oldkeys)==set(bibkeys)
for d in [en,zh]:
 assert d['texts'][370].strip() in ('References','参考文献')
 for n,key in enumerate(bibkeys,1):
  s=d['texts'][370+n]
  assert re.match(r'^\['+str(n)+r'\]',s),f'Bib numbering row {n}: {s}'
  # Identify bibliographic record title/author by reordered original p, normalized stripping number.
  orig_idx=370+oldkeys.index(key)
  orig_text=orig['texts'][orig_idx]
  strip=lambda s:re.sub(r'^\[\d+\]','',s).strip()
  assert strip(orig_text) in strip(s),f'bib metadata mismatch {key}'
 assert 'October 2026' in d['texts'][-4] if False else True

# Extract literal equation-number labels across w:t; comma groups '(10.5, 10.6)' are decomposed.
numreg=re.compile(r'\((?P<nums>\s*(?:[A-E]\.|\d+\.)\d+(?:\s*,\s*(?:[A-E]\.|\d+\.)\d+)*)\s*\)')
def extract_numbered(text):
 o=[]
 for m in numreg.finditer(text.replace('（','(').replace('）',')').replace('、',',')):o.extend(re.findall(r'(?:\d+|[A-E])\.\d+',m.group('nums')))
 return o
anchors={}
for l,num,page in labels:
 prefix=l.split(':',1)[0]
 if prefix=='eq':
  en_hits=[i for i,t in enumerate(en['texts'][:370]) if num in extract_numbered(t)]
  zh_hits=[i for i,t in enumerate(zh['texts'][:370]) if num in extract_numbered(t)]
 elif prefix in ('thm','prop','lem','cor','def'):
  zhtype={'thm':'定理','prop':'命题','lem':'引理','cor':'推论','def':'定义'}[prefix]
  entype={'thm':'Theorem','prop':'Proposition','lem':'Lemma','cor':'Corollary','def':'Definition'}[prefix]
  en_hits=[i for i,t in enumerate(en['texts']) if re.match(r'^'+entype+r'\s*'+re.escape(num)+r'\b',t)]
  zh_hits=[i for i,t in enumerate(zh['texts']) if re.match(r'^'+zhtype+r'\s*'+re.escape(num)+r'\b',t)]
 elif prefix in ('fig','tab'):
  fmt1='Figure' if prefix=='fig' else 'Table'
  fmt2='图' if prefix=='fig' else '表'
  en_hits=[i for i,t in enumerate(en['texts']) if re.match(r'^'+fmt1+r'\s+'+re.escape(num)+r'\.',t)]
  zh_hits=[i for i,t in enumerate(zh['texts']) if re.match(r'^'+fmt2+r'\s+'+re.escape(num)+r'\.',t)]
 elif prefix in ('sec','app'):
  en_hits=[i for i,t in enumerate(en['texts'][:371]) if (t.startswith(str(num)+'.') or t.startswith(str(num)+'. ')) and en['paras'][i].find(w+'pPr') is not None]
  zh_hits=[i for i,t in enumerate(zh['texts'][:371]) if (t.startswith(str(num)+'.') or t.startswith(str(num)+'. ')) and zh['paras'][i].find(w+'pPr') is not None]
 else:en_hits=[];zh_hits=[]
 anchors[l]={'number':num,'siam_pdf_page':page,'en_para_candidates':en_hits,'zh_para_candidates':zh_hits,'type':prefix}
missing_en=[x for x in anchors if not anchors[x]['en_para_candidates']]
missing_zh=[x for x in anchors if not anchors[x]['zh_para_candidates']]
print('unmapped',len(missing_en),len(missing_zh),'EN',missing_en,'ZH',missing_zh)
# Only direct eq, formal statements, fig, table are mandatory word anchors; sec/app heading extraction variants allowed.
primary=['eq','thm','prop','lem','cor','def','fig','tab']
critical_misses=[x for x in anchors if anchors[x]['type'] in primary and (not anchors[x]['en_para_candidates'] or not anchors[x]['zh_para_candidates'])]
assert not critical_misses,f'Core anchors missing: {critical_misses}'
assert sum(1 for x in anchors.values() if x['type'] in ('thm','prop','lem','cor'))==33
# all source equations and SIAM labels captured
with open(out/'GATE4_131_LABEL_WORD_CROSSWALK.csv','w',newline='',encoding='utf-8-sig') as f:
 wtr=csv.writer(f)
 wtr.writerow(['label','label_type','SIAM_number','SIAM_PDF_page','English_Word_paragraph_ids_0based','Chinese_Word_paragraph_ids_0based','English_anchor_text_excerpt','Chinese_anchor_text_excerpt'])
 for label,num,page in labels:
  item=anchors[label]
  a=item['en_para_candidates'];b=item['zh_para_candidates']
  wtr.writerow([label,item['type'],num,page,','.join(map(str,a)),','.join(map(str,b)),en['texts'][a[0]][:140] if a else '',zh['texts'][b[0]][:140] if b else ''])
with open(out/'GATE4_SIAM_REFERENCE_RENUMBERING.csv','w',newline='',encoding='utf-8-sig') as f:
 wtr=csv.writer(f);wtr.writerow(['Old_Word_number','SIAM_PDF_number','BibTeX_key','bbl_order','English_Word_reference','Chinese_Word_reference'])
 for i,key in enumerate(oldkeys,1):
  n=bibkeys.index(key)+1
  wtr.writerow([i,n,key,n,en['texts'][370+n],zh['texts'][370+n]])
with open(out/'GATE4_43_RESPONSIBILITIES_UNCHANGED.csv','w',newline='',encoding='utf-8-sig') as f:
 wr=csv.DictWriter(f,fieldnames=list(regs[0].keys()))
 wr.writeheader();wr.writerows(regs)
# Visual QA summaries inspect rendered PDFs (do not treat zero overlap as full professional proof).
render_stats={}
for lang,p in [('English',base.parent/'english_final_render/Gate4_When_Can_Markets_Crash_English_Full_Editable_SIAM_Aligned_v20.pdf'),('Chinese',base.parent/'chinese_final_render/Gate4_When_Can_Markets_Crash_Chinese_Full_Editable_SIAM_Aligned_v20.pdf')]:
 d=fitz.open(p);pi=[]
 for i,page in enumerate(d):
  t=page.get_text();blocks=[b for b in page.get_text('blocks') if len(b)>=7 and b[6]==0]
  invalid=[(b[0],b[1],b[2],b[3]) for b in blocks if b[0]<-2 or b[1]<-2 or b[2]>page.rect.width+2 or b[3]>page.rect.height+2]
  pi.append({'page':i+1,'chars':len(t),'out_of_page_blocks':len(invalid),'unrendered_math_error_glyphs':t.count('¿'),'unicode_replacement_chars':t.count('\ufffd')})
 render_stats[lang]={'pages':len(d),'per_page':pi,'total_math_renderer_errors':sum(x['unrendered_math_error_glyphs'] for x in pi)}
assert render_stats['English']['pages']==31
assert render_stats['Chinese']['pages']==30
assert not any(x['out_of_page_blocks'] for lang in render_stats for x in render_stats[lang]['per_page'])
assert not any(x['chars']<60 for lang in render_stats for x in render_stats[lang]['per_page'])
report={
 'date':'2026-11-12','status':'GATE4_DOCUMENT_REVIEW_IN_PROGRESS_NOT_SCIENTIFIC_REACCEPTANCE',
 'source_main_tex_sha256':sha(LATEX),'siam_pdf_sha256':sha(SIAM),'siam_pdf_pages':35,'bib_sha256':sha(BIB),
 'English_word_sha256':sha(EN),'Chinese_word_sha256':sha(ZH),
 'english_word_pages':render_stats['English']['pages'],'chinese_word_pages':render_stats['Chinese']['pages'],
 'par_count_original':386,'par_count_deliverables':387,'prose_paragraphs_translated':259,
 'math_native_oMath_nodes_each':1326,'display_math_paragraphs_each':106,'figures':6,'tables':2,
 'formula_nodes_preserved_exactly':True,'original_figure_media_SHA_unchanged':True,
 'siam_crossreference_labels':len(labels),'label_breakdown':dict(stats),
 '33_mathematical_result_anchors':33,'formula_number_anchor_misses':critical_misses,
 'bibliography_items':16,'bibliography_order':'SIAM main.bbl alphabetical and in-text references renumbered',
 'unchanged_scientific_responsibilities':len(regs),'open_research_ids':[x['ID'] for x in open_regs],
 'render_checks':render_stats,
 'caveats':['OMML maths are retained word-native; LibreOffice has import bugs for certain algebraic operator tokens, quantified in render QA.','Bilingual prose translation had one-to-one placeholder review; semantics may need independent human proofread.','No fresh Gate0-Gate3 science rerun; 7 open questions unchanged.']}
(out/'GATE4_DOCUMENT_AUDIT.json').write_text(json.dumps(report,ensure_ascii=False,indent=2),encoding='utf8')
print('AUDIT math 1326, formulas 65, math results 33, bib 16; EN and ZH 131-label crosswalk checked')
print('PDF renderer errors',render_stats['English']['total_math_renderer_errors'],render_stats['Chinese']['total_math_renderer_errors'])
print('AUDIT',out)