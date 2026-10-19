"""Run deterministic interval certificates under the frozen synthetic model.

This is an internally authored computer-assisted proof checker, not independent
formal certification. The optional --audit uses SciPy for numerical crosschecks.
"""
from fractions import Fraction as Fr
from pathlib import Path
import hashlib,json,sys,argparse,time
ROOT=Path(__file__).resolve().parent
from phase3_certification_suite import construct_cases,test_case,Fr as Fr3
from phase4_interval_cert import verify as verify_phase4

def self_integrity():
    manifest=json.loads((ROOT/'SHA256SUMS.json').read_text())
    for rel,expected in manifest.items():
        content=(ROOT/rel).read_bytes()
        actual=hashlib.sha256(content).hexdigest()
        if actual!=expected:raise RuntimeError('fixed input/script sha mismatch: '+rel)
    print('PASS SHA256 inputs and immutable program hashes',len(manifest),flush=True)

def certify():
    self_integrity()
    specs=construct_cases()
    manifest=json.loads((ROOT/'verified_results_manifest.json').read_text())
    out=[]
    for spec in specs:
        result=test_case(spec);name=result['case'];prior=manifest[name]
        assert str(1-Fr(prior['certified_target_ordinary_drop_strict']))==str(spec['target_floor'])
        assert str(1-Fr(prior['certified_geometric_index_drop_strict']))==str(spec['index_floor'])
        assert abs(Fr(str(result['paired_dollar_turnover']))-Fr(prior['M']))<Fr(1,10**8)
        assert result['per_asset_gross_share_rate_upper']<float(Fr(285,1000))
        out.append(result)
    (ROOT/'phase3_certification_suite_results.json').write_text(json.dumps({'case_results':out},indent=2))
    from phase4_interval_cert import verify
    raw=json.loads((ROOT/'phase4_controls.json').read_text())
    for name,spec in sorted(raw.items()):
        inp={'case':name,'k':spec['k'],'m':spec['m'],'rates':[Fr(s) for s in spec['rates']],
             'dt':Fr(spec['dt']),'target_loss':Fr(spec['target_loss']),
             'index_loss':Fr(spec['index_loss']),'M_cap':Fr(spec['M_cap']),
             'source':'phase4_controls.json','scale':'exact'}
        assert len(inp['rates'])*inp['dt']==40
        assert sum(inp['rates'],Fr(0))==0,('terminal dollar closure',name)
        result=verify(inp)
        prior=manifest[name]
        assert Fr(result['target_loss_certified_strictly_greater_than'])==Fr(prior['certified_target_ordinary_drop_strict'])
        assert Fr(result['market_geometric_index_loss_strictly_greater_than'])==Fr(prior['certified_geometric_index_drop_strict'])
        assert abs(Fr(str(result['M_bound']))-Fr(prior['M']))<Fr(1,10**8)
        out_name='phase4_certificate_'+name+'.json'
        (ROOT/out_name).write_text(json.dumps(result,indent=2)+'\n')
        print('PASS phase4',name,out_name,flush=True)
    print('PASS all 12 internally interval-checked control candidates',flush=True)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--audit',action='store_true',help='run numerical crosschecks (SciPy required)')
    args=parser.parse_args()
    certify()
    if args.audit:
        from phase3_independent_suite_audit import audit as phase3_audit
        from phase4_independent_audit_all import audit as phase4_audit
        phase3_audit()
        for p in sorted(ROOT.glob('phase4_certificate_*.json')):phase4_audit(str(p))
