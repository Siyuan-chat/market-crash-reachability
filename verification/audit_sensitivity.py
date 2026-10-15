"""Independent audit of V9 sensitivity, without importing the certificate writer.

Certified yes/no fixed-path band conclusions are deduced from the *outward*
interval endpoints produced by certify_streak_interval.py. Alternative k cases
are ODE diagnostics only, not interval-validated proofs of path feasibility.
"""
from __future__ import annotations
import argparse, json
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'scripts'))
from sensitivity_probe import get_stats


def rat(v): return Q(str(v))
def audit(path):
    cert=json.loads(Path(path).read_text())
    assert cert['steps']==80000
    segments=cert['segments']; knots=cert['y_at_knots']
    assert len(segments)==6 and len(knots)==6
    d1lo=min(rat(row['y_min_lower_bound']) for row in segments[:3])
    d1hi=max(rat(row['y_max_upper_bound']) for row in segments[:3])
    d2lo=min(rat(row['y_min_lower_bound']) for row in segments[3:])
    d2hi=max(rat(row['y_max_upper_bound']) for row in segments[3:])
    y20lo=rat(knots[2]['y_interval'][0]); y20hi=rat(knots[2]['y_interval'][1]);
    y177upper=rat(knots[1]['y_interval'][1])
    def valid(beta):
        beta=Q(beta)
        return (d1lo>1-beta and d1hi<1+beta and
                d2lo>(1-beta)*y20hi and d2hi<(1+beta)*y20lo)
    assert valid('0.250')
    assert valid('0.247')
    assert not valid('0.240')
    assert y177upper < Q('0.760') # exclusion of fixed path with 24% lower band
    candidates=[get_stats(k,10-k) for k in [6,7,8,9]]
    assert all('fail' not in c for c in candidates)
    assert abs(candidates[-1]['mean_loss']-.02081139744)<1e-8
    assert abs(candidates[-1]['y40']-1.405160822)<1e-7
    assert [z['crisis_threshold_002'] for z in candidates]==[False,False,False,True]
    return {
        'validated_existing_interval_certificate': True,
        'certificate_steps':80000,
        'day1_y_outward_interval':[str(d1lo),str(d1hi)],
        'day2_y_outward_interval':[str(d2lo),str(d2hi)],
        'day1_reference_reset_y20_interval':[str(y20lo),str(y20hi)],
        'certified_fixed_path_band_24_7_percent':True,
        'certified_fixed_path_band_25_percent':True,
        'fixed_path_fails_band_24_percent':True,
        'fixed_path_failure_reason':'y(17.7) upper < 0.760, below proposed lower bound 0.760',
        'alternative_target_counts_exploratory_not_certified': candidates,
        'limitations':'Changing the target count or the band may allow another optimized path; this only tests one frozen target-control shape.'
    }
if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--cert',default='data/certificates/final_interval_certificate.json')
    p.add_argument('--out',default='data/sensitivity_audit.json')
    args=p.parse_args()
    data=audit(args.cert)
    Path(args.out).write_text(json.dumps(data,indent=2),encoding='utf-8')
    print('V9 sensitivity audit PASS:',json.dumps({k:v for k,v in data.items() if k.startswith(('certified_','fixed_path_'))},indent=2))
