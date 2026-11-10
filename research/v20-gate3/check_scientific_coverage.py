#!/usr/bin/env python3
"""Gate 3 scientific *coverage and provenance* audit, NOT a theorem prover.

The human mathematical review lives in GATE3_SCIENTIFIC_ACCEPTANCE_AUDIT_ZH.md.
This script verifies that all asserted results have an actual local proof
environment and that 43 historic obligations, evidence qualifications, figures
and the original bibliography remain present. It is not a Lean proof.
"""
from __future__ import annotations
import csv
import re
from pathlib import Path
from collections import Counter

ROOT=Path(__file__).resolve().parents[2]
MAN=ROOT/'submission/v20-gate3-activity-recovery/main.tex'
REG=ROOT/'research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv'
FIG=MAN.parent/'figures'
BIB=ROOT/'submission/v16-three-certified-constructions/references.bib'
text=MAN.read_text(encoding='utf-8')
with REG.open(encoding='utf-8-sig',newline='') as fh:
    rr=csv.DictReader(fh)
    assert len(rr.fieldnames or [])==16
    rows=list(rr)
assert len(rows)==43 and len({r['ID'] for r in rows})==43
assert all(None not in r and None not in r.values() for r in rows)
expected={*(f'M{i:02d}' for i in range(1,4)),
          *(f'T{i:02d}' for i in range(1,10)),
          *(f'P{i:02d}' for i in range(1,13)), 'L01',
          *(f'I{i:02d}' for i in range(1,4)),
          *(f'R{i:02d}' for i in range(1,4)),
          *(f'A{i:02d}' for i in range(1,9)),
          *(f'F{i:02d}' for i in range(1,4)), 'B01'}
assert {r['ID'] for r in rows}==expected
for row in rows:
    assert row['Gate3 writing obligation'].strip(),row['ID']
    assert row['evidence level'].strip(),row['ID']
    assert row['assumption audit'].strip(),row['ID']
    assert row['blocks strong abstract claim'].strip(),row['ID']
    assert row['Gate3 manuscript state'] in {'drafted','partial','partial_open'},row['ID']
open_ids={'T03','P02','P10','R01','R02','R03','A04'}
assert open_ids <= {r['ID'] for r in rows if r['Gate3 manuscript state']!='drafted'}
result_re=re.compile(r'\\begin\{(theorem|proposition|lemma|corollary)\}(?:\[[^]]*\])?([\s\S]*?)\\end\{\1\}')
# Avoid accidentally treating a textual discussion heading as proof.
results=list(result_re.finditer(text))
assert len(results)>=33,len(results)
labels=[re.search(r'\\label\{([^}]+)\}',m.group(2)) for m in results]
assert all(labels), 'A mathematical result has no stable label'
for m in results:
    tail=text[m.end():].lstrip()
    assert tail.startswith(r'\begin{proof}'),('No adjacent proof',m.group(1),m.start())
    proof_end=tail.find(r'\end{proof}')
    assert proof_end>len(r'\begin{proof}'),('Empty proof',m.start())
all_labels=[x.group(1) for x in re.finditer(r'\\label\{([^}]+)\}',text)]
assert len(all_labels)==len(set(all_labels)), 'Duplicate TeX labels'
all_set=set(all_labels)
for ref in re.findall(r'\\(?:eqref|ref)\{([^}]+)\}',text):
    assert ref in all_set,('Dangling reference',ref)
for needed in ('thm:tenhalf','thm:nine','thm:nine-general','thm:two',
               'prop:time-change','thm:two-large-turnover','prop:two-critical-p',
               'cor:nearcritical-beyond','prop:two-day-rate-lower',
               'eq:open-all-bracket','eq:open-coverage-bracket',
               'eq:open-speed-bracket','sec:open-sharpness'):
    assert needed in all_set,('Required result/open boundary missing',needed)
figs=re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]+)\}',text)
assert len(figs)==6
for fig in figs:
    p=MAN.parent/fig
    assert p.is_file() and p.read_bytes().startswith(b'%PDF-'),fig
assert r'NUMERIC\_ONLY' in text,'Old floating-point I/II paths need evidence labels'
assert 'external certification is not claimed' in text.lower()
assert 'not third-party formal' in text.lower()
bibliography=BIB.read_text(encoding='utf-8')
keys=set(re.findall(r'(?m)^@\w+\{([^,]+),',bibliography))
assert len(keys)==33,len(keys)
cites=set()
for m in re.finditer(r'\\cite(?:p|t|alt|alp)?(?:\[[^]]*\])*\{([^}]+)\}',text):
    cites.update(x.strip() for x in m.group(1).split(','))
assert len(cites)>=16,len(cites)
assert cites<=keys,cites-keys
states=Counter(r['Gate3 manuscript state'] for r in rows)
print(f'PASS: {len(rows)} preserved IDs, {len(results)} proof-bearing results, '
      f'{len(figs)} source PDF figures, {len(keys)} original bibliography keys')
print('Authoring statuses:',dict(states))
print('SCOPE: structural/evidence coverage only, NOT mathematical or external peer review')
