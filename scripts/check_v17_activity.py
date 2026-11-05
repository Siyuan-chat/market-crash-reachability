#!/usr/bin/env python3
"""V17 source/evidence consistency check. Not a theorem prover."""
from pathlib import Path
import json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
SRC=ROOT/'submission/v17-activity-driven-recovery'
MAT=ROOT/'verification/activity_driven'
def main():
    tex=(SRC/'main.tex').read_text()
    bib=(SRC/'references.bib').read_text()
    labels=set(re.findall(r'\\label\{([^}]+)\}',tex))
    refs=set(re.findall(r'\\(?:eqref|ref|autoref)\{([^}]+)\}',tex))
    assert refs<=labels,('missing labels',sorted(refs-labels))
    bibkeys=set(re.findall(r'@\w+\s*\{\s*([^,\s]+)\s*,',bib))
    cited=set()
    for keys in re.findall(r'\\cite[pt]?\{([^}]+)\}',tex):
        cited.update(k.strip() for k in keys.split(','))
    assert cited<=bibkeys,('missing bibliography entries',sorted(cited-bibkeys))
    assert tex.count(r'\begin{proof}')==tex.count(r'\end{proof}')
    assert tex.count(r'\begin{theorem}')==tex.count(r'\end{theorem}')
    assert tex.count(r'\begin{equation}')==tex.count(r'\end{equation}')
    for key in ('thm:triangle','thm:floor','thm:aggregate','thm:lower','thm:kresource','thm:tenhalf','thm:nine','thm:two','lem:completion','lem:embed','app:smoothing','app:interval'):
        assert key in labels,key
    main=tex.split(r'\appendix',1)[0]
    assert r'\dd S_i=\frac{g(S_i)}{S_i}\dd X_i-\kappa(S_i-F)\dd A_i' in main
    assert r'\mathsf C_0' in main and r'\mathsf C_1' in main
    assert 'No earlier fixed-version manuscript' in main
    assert r'\delta' in main and 'independent of' in main
    assert 'internally' in main.lower()
    assert r'\bibliographystyle{unsrtnat}' in tex
    cert=json.loads((MAT/'five_target_certificate.json').read_text())
    assert cert['c_root_bracket']==['0.76065368494358','0.76065368494359']
    assert cert['max_paired_turnover_certified_upper']=='11.261627'
    assert cert['max_gross_share_rate_certified_upper']=='0.133'
    assert cert['root_sign_left'] and cert['root_sign_right']
    print('PASS V17 source, claim scope, bibliography, certificate schema')
    print('labels',len(labels),'cited references',len(cited))
if __name__=='__main__':main()
