"""Local acceptance utility: complete raster/text/geometry comparison, no source edits."""
from pathlib import Path
import argparse, hashlib, json, re, unicodedata
import pymupdf as fitz
import numpy as np
from PIL import Image

parser=argparse.ArgumentParser()
parser.add_argument('--repository',required=True)
parser.add_argument('--rebuilt',required=True)
parser.add_argument('--out',required=True)
args=parser.parse_args()
root=Path(args.repository).resolve(); rebuilt=Path(args.rebuilt).resolve();out=Path(args.out).resolve();out.mkdir(parents=True,exist_ok=True)
def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def normalize(text): return re.sub(r'\s+','',unicodedata.normalize('NFKC',text))
summary={}
for name,source,new in [('paper','paper/manuscript.pdf','paper/main.pdf'),('supplementary','supplementary/supplementary.pdf','supplementary/supplementary.pdf')]:
    original=root/source; current=rebuilt/new
    a=fitz.open(original);b=fitz.open(current)
    result={'original_sha256':digest(original),'rebuilt_sha256':digest(current),'original_metadata':a.metadata,'rebuilt_metadata':b.metadata,'original_pages':len(a),'rebuilt_pages':len(b),'raster_dpi':144,'pages':[]}
    assert len(a)==len(b),(name,len(a),len(b))
    for i,(pa,pb) in enumerate(zip(a,b)):
        x=pa.get_pixmap(matrix=fitz.Matrix(2,2),alpha=False);y=pb.get_pixmap(matrix=fitz.Matrix(2,2),alpha=False)
        xa=np.frombuffer(x.samples,dtype=np.uint8).reshape(x.height,x.width,3);ya=np.frombuffer(y.samples,dtype=np.uint8).reshape(y.height,y.width,3)
        assert xa.shape==ya.shape,(name,i,xa.shape,ya.shape)
        delta=np.abs(xa.astype(np.int16)-ya.astype(np.int16)); changed=np.max(delta,axis=2)>0
        row={'page':i+1,'page_size_equal':pa.rect==pb.rect,'raw_text_equal':pa.get_text()==pb.get_text(),'normalized_text_equal':normalize(pa.get_text())==normalize(pb.get_text()),'pixels_equal':not bool(changed.any()),'changed_pixel_fraction':float(changed.mean()),'pixel_fraction_difference_gt16':float((np.max(delta,axis=2)>16).mean()),'mean_absolute_channel_difference':float(delta.mean())}
        for field,pattern in [('numeric_sequence_equal',r'\d+(?:\.\d+)*'),('numeric_citations_equal',r'\[\d+(?:[,–-]\s*\d+)*\]'),('equation_numbers_equal',r'\((?:[A-Z]\.)?\d+(?:\.\d+)*\)')]:
            row[field]=re.findall(pattern,pa.get_text())==re.findall(pattern,pb.get_text())
        # Compare glyph sequence and bounding boxes; expose all non-matching pages for review.
        chars=lambda p:[(c['c'],c['bbox']) for block in p.get_text('rawdict')['blocks'] if 'lines' in block for line in block['lines'] for span in line['spans'] for c in span['chars']]
        ca,cb=chars(pa),chars(pb)
        row['character_sequence_equal']=[c[0] for c in ca]==[c[0] for c in cb]
        if row['character_sequence_equal']:
            row['maximum_character_bbox_delta_pt']=max((max(abs(u-v) for u,v in zip(aa[1],bb[1])) for aa,bb in zip(ca,cb)),default=0)
        result['pages'].append(row)
        if i in ([0,4,21,len(a)-1] if name=='paper' else [0,len(a)-1]) or not row['normalized_text_equal']:
            Image.fromarray(xa).save(out/f'{name}-original-{i+1:02d}.png')
            Image.fromarray(ya).save(out/f'{name}-pdflatex-{i+1:02d}.png')
        if changed.any():
            # 288-pixel thumbnails per page make the entire document reviewable in contact sheets.
            thumb=Image.fromarray(ya);thumb.thumbnail((288,373));thumb.save(out/f'{name}-thumb-{i+1:02d}.png')
    result['all_pages_normalized_text_equal']=all(p['normalized_text_equal'] for p in result['pages'])
    result['all_pages_pixel_equal']=all(p['pixels_equal'] for p in result['pages'])
    result['max_changed_pixel_fraction']=max(p['changed_pixel_fraction'] for p in result['pages'])
    result['all_page_sizes_equal']=all(p['page_size_equal'] for p in result['pages'])
    result['all_numeric_sequences_equal']=all(p['numeric_sequence_equal'] and p['numeric_citations_equal'] and p['equation_numbers_equal'] for p in result['pages'])
    summary[name]=result
    print(name,json.dumps({k:v for k,v in result.items() if k not in ('pages','original_metadata','rebuilt_metadata')}),flush=True)
(out/'comparison.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
