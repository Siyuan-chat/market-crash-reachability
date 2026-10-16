"""Reject unfinished proofs and audit every declared project theorem with Lean."""
from pathlib import Path
import re
import subprocess
import json

ROOT = Path(__file__).resolve().parent
project = ROOT / 'lean'
names = []
for path in sorted((project / 'MarketCrash').rglob('*.lean')):
    if path.name == 'AxiomAudit.lean':
        continue
    source = path.read_text(encoding='utf-8')
    # Lean block comments use /- ... -/ (possibly nested).
    depth, cleaned, pos = 0, [], 0
    while pos < len(source):
        token = source[pos:pos + 2]
        if token == '/-':
            depth += 1
            pos += 2
        elif depth and token == '-/':
            depth -= 1
            pos += 2
        else:
            if not depth:
                cleaned.append(source[pos])
            pos += 1
    if depth:
        raise SystemExit('Unclosed Lean comment in ' + str(path))
    source = ''.join(cleaned)
    source = re.sub(r'--[^\n]*', '', source)
    if re.search(r'\b(sorry|admit|axiom)\b', source):
        raise SystemExit('Unproved declaration in ' + str(path))
    names.extend(re.findall(r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)', source, flags=re.M))
audit_header = 'import MarketCrash\n\n'
audit_path = project / 'MarketCrash/AxiomAudit.lean'
actual_audit = audit_path.read_text(encoding='utf-8')
listed = re.findall(
    r'^#print axioms MarketCrash\.([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)$',
    actual_audit, flags=re.M)
# Exact audited declarations with no duplicates or unrecognized audit code.
if (len(listed) != len(names) or sorted(listed) != sorted(names) or
    actual_audit != audit_header + ''.join(
        '#print axioms MarketCrash.' + name + '\n' for name in listed)):
    raise SystemExit('AxiomAudit.lean must cover every project theorem exactly once')
result = subprocess.run(['lake', 'env', 'lean', 'MarketCrash/AxiomAudit.lean'],
                        cwd=project, capture_output=True, text=True)
out = ROOT.parent / 'build/formal'
out.mkdir(parents=True, exist_ok=True)
(out / 'axioms.log').write_text(result.stdout + result.stderr, encoding='utf-8')
if result.returncode:
    raise SystemExit('Lean axiom audit failed; see build/formal/axioms.log')
rows = re.findall(
    r"'MarketCrash\.([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)' depends on axioms: \[([^]]*)\]",
    result.stdout)
if len(rows) != len(names):
    raise SystemExit('Incomplete axiom audit output')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, dependencies in rows:
    unexpected = set(filter(None, (part.strip() for part in dependencies.split(',')))) - allowed
    if unexpected:
        raise SystemExit(f'Unexpected axioms in {name}: {unexpected}')
(out / 'integrity.json').write_text(json.dumps({
    'status': 'PASS', 'theorem_count': len(names),
    'audited_theorems': names, 'permitted_foundational_axioms': sorted(allowed),
    'whole_paper_formalized': False,
}, indent=2) + '\n', encoding='utf-8')
print(f'PASS: {len(names)} theorems audited; no unfinished proofs or extra axioms')
