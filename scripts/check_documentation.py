"""Deterministic public-documentation checks; no network or LLM required."""
from pathlib import Path
from urllib.parse import unquote, urlsplit
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PRIMARY = ['README.md', 'REPRODUCE.md', 'docs/STATUS.md',
           'docs/RESEARCH_OVERVIEW.md', 'docs/RESULTS_AND_EVIDENCE.md',
           'docs/REPRODUCIBILITY.md', 'docs/VERSIONS.md', 'formal/README.md',
           'submission/README.md', 'submission/v14-turnover-dissipation/README.md']
# Historical technical records and manuscript disclosures are checked for links,
# but current-version/workflow rules apply only to the explicit primary set.
KNOWN_DOIS = {'10.5281/zenodo.' + x for x in
              ('23444647', '23428183', '23427879', '23438609', '23427880', '23478787')}
KNOWN_DOIS.add('10.2139/ssrn.7622079')

def check():
    errors = []
    files = subprocess.check_output(['git', 'ls-files', '--cached', '--others',
                                     '--exclude-standard'], cwd=ROOT, text=True).splitlines()
    checked = 0
    for name in sorted(set(files)):
        path = ROOT / name
        if path.suffix.lower() != '.md' or not path.is_file():
            continue
        source = path.read_text(encoding='utf-8')
        # Inline links/images and reference definitions; ignore fenced code.
        source = re.sub(r'(?ms)^\s*```.*?^\s*```[^\n]*', '', source)
        targets = re.findall(r'!?\[[^\]\n]*\]\(\s*(<[^>]+>|[^\s)]+)', source)
        targets += re.findall(r'(?m)^\s*\[[^\]]+\]:\s*(<[^>]+>|\S+)', source)
        for target in targets:
            target = target.strip('<>')
            if urlsplit(target).scheme or target.startswith('//'):
                continue
            asset = unquote(target.split('#', 1)[0].split('?', 1)[0])
            resolved = path.parent / asset if asset else path
            if not resolved.exists():
                errors.append(f'{name}: missing link target {target}')
            elif '#L' in target and resolved.is_file():
                line = re.fullmatch(r'L(\d+)(?:-L(\d+))?', target.split('#', 1)[1])
                if line:
                    last = int(line.group(2) or line.group(1))
                    if not 1 <= int(line.group(1)) <= last <= len(resolved.read_text(encoding='utf-8').splitlines()):
                        errors.append(f'{name}: invalid line anchor {target}')
            elif '#' in target and resolved.suffix.lower() == '.md':
                fragment = unquote(target.split('#', 1)[1])
                headings = re.findall(r'(?m)^#{1,6}\s+(.+?)\s*#*$', resolved.read_text(encoding='utf-8'))
                slugs = {re.sub(r'[^\w\s-]', '', h.lower()).replace(' ', '-') for h in headings}
                if fragment and fragment not in slugs:
                    errors.append(f'{name}: missing heading anchor {target}')
        checked += 1
    for name in PRIMARY:
        source = (ROOT / name).read_text(encoding='utf-8')
        for pattern in (r'(?i)current public English preprint: V13',
                        r'(?i)latest English preprint \(V13',
                        r'(?i)Unpublished draft; not the preferred citable preprint',
                        r'(?i)authoritative execution queue',
                        r'(?i)continue autonomously through this queue',
                        r'(?i)V14.{0,30}(?:is fully|entirely) Lean.formalized',
                        r"(?i)V14(?:'s)? (?:five )?additions (?:are |have been )Lean.formalized",
                        r'(?i)V14.{0,30}(?:journal.accepted|has a DOI)'):
            if re.search(pattern, source):
                errors.append(f'{name}: contradictory or operational text: {pattern}')
        for doi in re.findall(r'10\.\d{4,9}/[-._;()/:A-Za-z0-9]+', source):
            doi = doi.rstrip(').,;:')
            if doi not in KNOWN_DOIS:
                errors.append(f'{name}: unreviewed DOI {doi}')
        for command_path in re.findall(r'python\s+((?:scripts|verification|formal)/[\w/.-]+\.py)', source):
            if not (ROOT / command_path).is_file():
                errors.append(f'{name}: missing reproduction program {command_path}')
    readme = (ROOT / 'README.md').read_text(encoding='utf-8')
    for required in ('Latest GitHub manuscript: V14', 'not Lean-formalized',
                     'submission/v14-turnover-dissipation/manuscript.pdf'):
        if required not in readme:
            errors.append('README.md: missing required scope marker ' + required)
    citation = (ROOT / 'CITATION.cff').read_text(encoding='utf-8')
    for identity in ('1.0.0rc1+git.d6e2606', 'd6e2606590f955a6287c6945488a080e5acab004',
                     '10.5281/zenodo.23428183', '10.5281/zenodo.23444647'):
        if identity not in citation:
            errors.append('CITATION.cff: missing fixed identity ' + identity)
    for identity_pattern in (r'(?m)^doi: 10\.5281/zenodo\.23428183$',
                             r'(?m)^  doi: 10\.5281/zenodo\.23444647$'):
        if not re.search(identity_pattern, citation):
            errors.append('CITATION.cff: software/paper DOI role mismatch')
    for forbidden in ('AGENTS.md', 'formal/CODEX_EXECUTION_PLAN.md'):
        if (ROOT / forbidden).exists():
            errors.append('Obsolete tracked workflow file: ' + forbidden)
    for error in errors:
        print('FAIL:', error)
    print(f'Checked {checked} Markdown files and {len(PRIMARY)} authoritative documents; {len(errors)} error(s)')
    return bool(errors)

if __name__ == '__main__':
    raise SystemExit(check())
