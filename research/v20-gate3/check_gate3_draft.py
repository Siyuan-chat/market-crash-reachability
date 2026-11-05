#!/usr/bin/env python3
"""Gate 3 manuscript *coverage ledger* QA, not a mathematical proof.

Usage: python research/v20-gate3/check_gate3_draft.py
"""
from __future__ import annotations
import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
REG = ROOT / 'research/v20-gate3/GATE3_43_ITEM_CONTENT_REGISTER.csv'
MANUS = ROOT / 'submission/v20-gate3-activity-recovery/main.tex'
FIGS = ROOT / 'submission/v20-gate3-activity-recovery/figures'
rows = list(csv.DictReader(REG.open(encoding='utf-8-sig', newline='')))
expected = {
    *(f'M{i:02d}' for i in range(1, 4)),
    *(f'T{i:02d}' for i in range(1, 10)),
    *(f'P{i:02d}' for i in range(1, 13)),
    'L01',
    *(f'I{i:02d}' for i in range(1, 4)),
    *(f'R{i:02d}' for i in range(1, 4)),
    *(f'A{i:02d}' for i in range(1, 9)),
    *(f'F{i:02d}' for i in range(1, 4)),
    'B01',
}
assert len(expected) == 43
assert len(rows) == len(expected), f'Expected 43 rows, got {len(rows)}'
assert len({r['ID'] for r in rows}) == 43, 'duplicate IDs'
assert {r['ID'] for r in rows} == expected, 'missing/extra original items'
allowed = {'drafted', 'partial', 'partial_open', 'not_yet_drafted'}
assert all(r['Gate3 manuscript state'] in allowed for r in rows)
assert all(r['Gate3 manuscript state'] != 'not_yet_drafted' for r in rows), \
    'Round 2 should have no undrafted original items'
for row in rows:
    assert row['Gate3 writing obligation'].strip(), f"missing obligation: {row['ID']}"
    assert row['evidence level'].strip(), f"missing evidence level: {row['ID']}"
    assert row['assumption audit'].strip(), f"missing assumptions: {row['ID']}"
text = MANUS.read_text(encoding='utf-8')
assert r'\end{document}' in text
sections = re.findall(r'\\section\{([^}]*)\}', text)
assert len(sections) >= 12, len(sections)
for key in ('activity-driven', 'rolling', 'paired-dollar', 'inventory',
            'Nine', 'two-asset', 'finite', 'independent interval'):
    assert key.lower() in text.lower(), f'missing topic {key}'
figs = re.findall(r'\\includegraphics(?:\[[^]]*\])?\{([^}]*)\}', text)
assert len(figs) == 6, len(figs)
for f in figs:
    path = MANUS.parent / f
    assert path.is_file() and path.stat().st_size > 8000, f'missing figure {path}'
# Guard explicit numerical evidence qualifiers and avoid treating Gate3 as accepted.
assert r'NUMERIC\_ONLY' in text, 'floating-point evidence needs explicit label'
labels = set(re.findall(r'\\label\{([^}]+)\}', text))
for row in rows:
    fields = [x.strip() for x in row['Gate3 label/section'].split('/')]
    assert any(key in labels for key in fields), f"undocumented label for {row['ID']}: {fields}"
for needed in ('prop:hetero-two', 'prop:hetero-weighted', 'lem:one-sided-bv',
               'prop:rate-explicit', 'prop:rate-local-match',
               'lem:radial-general', 'lem:terminal-inventory',
               'cor:at-most-n-minus-one', 'tab:analytic-severity',
               'thm:nine-general', 'eq:nu-jacobian', 'eq:nu-compensator'):
    assert needed in labels, f'Round 2 result label missing: {needed}'
assert 'not third-party formal verification' in text.lower() or \
       'not third-party formal' in text.lower(), 'interval-scope qualifier missing'
assert 'GATE 3 WORKING DRAFT' in text[:400], 'WIP disclosure missing'
from collections import Counter
counts = Counter(r['Gate3 manuscript state'] for r in rows)
assert sum(counts.values()) == 43
print(f'PASS: 43 IDs; {len(sections)} sections; {len(figs)} original V19 PDF figures')
print('Status:', ', '.join(f'{k}={counts[k]}' for k in sorted(counts)))
print('SCOPE: coverage/paths only; NOT Gate 3 scientific acceptance or theorem verification')