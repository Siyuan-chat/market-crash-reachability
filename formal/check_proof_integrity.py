"""Reject unfinished proofs and audit every declared project theorem with Lean."""
from pathlib import Path
import re
import subprocess
import json
from lean_declarations import relative_theorem_names, strip_lean_comments

ROOT = Path(__file__).resolve().parent
project = ROOT / 'lean'
names = []
for path in sorted((project / 'MarketCrash').rglob('*.lean')):
    if path.name == 'AxiomAudit.lean':
        continue
    source = path.read_text(encoding='utf-8')
    if re.search(r'\b(sorry|admit|axiom)\b', strip_lean_comments(source)):
        raise SystemExit('Unproved declaration in ' + str(path))
    names.extend(relative_theorem_names(source))

if len(set(names)) != len(names):
    raise SystemExit('Duplicate fully qualified project theorem names')

audit_header = 'import MarketCrash\n\n'
audit_path = project / 'MarketCrash/AxiomAudit.lean'
actual_audit = audit_path.read_text(encoding='utf-8')
listed = re.findall(
    r'^#print axioms MarketCrash\.(.+)$',
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
    r"^'MarketCrash\.(.+)' depends on axioms: \[([^]]*)\]$",
    result.stdout, flags=re.M)
rows += [(name, '') for name in re.findall(
    r"^'MarketCrash\.(.+)' does not depend on any axioms$",
    result.stdout, flags=re.M)]
if len(rows) != len(names) or sorted(name for name, _ in rows) != sorted(names):
    raise SystemExit('Incomplete axiom audit output')
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, dependencies in rows:
    unexpected = set(filter(None, (part.strip() for part in dependencies.split(',')))) - allowed
    if unexpected:
        raise SystemExit(f'Unexpected axioms in {name}: {unexpected}')

# Completion is about the original numbered results, not helper counts.
# Acceptance is recorded only after manuscript review and exact-SHA workflows
# in the existing authoritative matrix; this audit additionally requires each
# result's canonical proof family to be present in the audited environment.
original_results = {
    'Theorem 3.1': {'theorem_3_1_original'},
    'Theorem 3.2': {'theorem_3_2_original'},
    'Theorem 4.1': {'theorem_4_1_original'},
    'Proposition 4.2': {'proposition_4_2_original_uniform'},
    'Proposition 4.3': {'proposition_4_3_original'},
    'Theorem 4.4': {'theorem_4_4_original'},
    'Theorem 5.1': {'theorem_5_1_original'},
    'Proposition 6.1': {'proposition_6_1_rate_only', 'proposition_6_1_rate_band',
                        'proposition_6_1_hypothetical_reset'},
    'Theorem 6.2': {'theorem_6_2_original'},
    'Theorem 6.3': {'theorem_6_3_original'},
    'Proposition 7.1': {'proposition_7_1_original_endpoint', 'proposition_7_1_single_compensator'},
    'Proposition 7.2': {'proposition_7_2_single_session', 'proposition_7_2_rolling_streak',
                        'proposition_7_2_perpetual_and_integer'},
    'Theorem 7.3': {'theorem_7_3_original'},
    'Proposition 7.4': {'proposition_7_4_original'},
    'Proposition 7.5': {'proposition_7_5_ledger_derivative_bound', 'proposition_7_5_market_cut',
                        'proposition_7_5_empty_complement', 'proposition_7_5_rolling_constant_impact'},
    'Proposition 7.6': {'proposition_7_6_original'},
}
matrix_rows = []
matrix_text = (ROOT/'WHOLE_PAPER_LEAN_COMPLETION.md').read_text(encoding='utf-8')
for line in matrix_text.splitlines():
    cells = [cell.strip() for cell in line.split('|')]
    if len(cells) >= 5 and cells[1] in original_results:
        matrix_rows.append((cells[1], cells[3]))
whole_paper_formalized = (
    len(matrix_rows) == len(original_results) == 16
    and {label for label, _ in matrix_rows} == set(original_results)
    and all(status == '**PAPER_ACCEPTED**' for _, status in matrix_rows)
    and all(required <= set(names) for required in original_results.values()))
accepted_original_results = [label for label, status in matrix_rows if status == '**PAPER_ACCEPTED**']
advertised = re.search(r'当前验收 \*\*(\d+)/16\*\*', matrix_text)
if advertised is None or int(advertised.group(1)) != len(accepted_original_results):
    raise SystemExit('Original-result acceptance header and matrix disagree')
if len(accepted_original_results) == 16 and not whole_paper_formalized:
    raise SystemExit('Whole-paper acceptance lacks unique original results or canonical proofs')
(out / 'integrity.json').write_text(json.dumps({
    'status': 'PASS', 'theorem_count': len(names),
    'audited_theorems': names, 'permitted_foundational_axioms': sorted(allowed),
    'whole_paper_formalized': whole_paper_formalized,
    'original_result_count': len(original_results),
    'accepted_original_results': accepted_original_results,
}, indent=2) + '\n', encoding='utf-8')
print(f'PASS: {len(names)} theorems audited; no unfinished proofs or extra axioms')
