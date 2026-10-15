"""Deterministic, independent numerical regression checks for this paper.

Run from project root: python scripts/verify_results.py
All tests here assess MODEL consistency, never empirical realism or proof originality.
"""
from __future__ import annotations
import json, math
from pathlib import Path
import numpy as np
from numerical_experiments import spectator_closed_path,two_pulse,dollar_pulse,systemic_crisis

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'data'/'numerical_verification.json'
checks={}

def check(key, predicate, detail):
    if not predicate:
        raise AssertionError(f'{key}: {detail}')
    checks[key]=detail

# Price impacts and exact dollar-pulse inversion in p=0,1,2.
for p in (0,1,2):
    s0=np.array([1.,1.,1.])
    d=np.array([.07,.07,-.14])
    s1=dollar_pulse(s0,d,p)
    s2=dollar_pulse(s1,-d,p)
    check(f'inverse_p{p}',bool(np.allclose(s2,s0,rtol=0,atol=4e-15)),f'max={np.max(abs(s2-s0)):.2g}')

# Same perfectly reversed dollar impulses around recovery, across all p.
for n,k in [(3,2),(12,11)]:
    for h in ((.01,.05,.10,.20) if n==3 else (.001,.005,.01,.03)):
        for p in (0,1,2):
            result=two_pulse(n=n,k=k,p=p,h=h,T=3.)
            check(f'two_pulse_closure_N{n}_p{p}_h{h}',np.max(abs(result['signed_dollars']))<1e-12,'all X_i(T)=0 by construction')
            if p==2:
                check(f'p2_barrier_N{n}_h{h}',result['crisis']<=5e-12,f'crisis={result["crisis"]:.8g}')
            if p==0:
                check(f'p0_crisis_N{n}_h{h}',result['crisis']>0,f'crisis={result["crisis"]:.8g}')

# Severe-dollar-closed witnesses, with trajectory checks including intermediate pairing.
rows=[]
for n,T in ((3,3.),(12,4.),(20,5.)):
    for L in (3.,5.,10.,20.):
        z=spectator_closed_path(n,T,L)
        asset_money_max=float(np.max(np.abs(z.cumulative_dollars[-1])))
        cross_money_max=float(np.max(np.abs(z.cumulative_dollars.sum(axis=1))))
        rmin=float(np.min(z.prices))
        check(f'witness_N{n}_L{L}',bool(asset_money_max<5e-10 and cross_money_max<5e-10 and rmin>0 and z.crisis>0),
              f'C={z.crisis:.6f} M={z.turnover:.6f}, max_end_dollar={asset_money_max:.2e}, max_sum_dollar={cross_money_max:.2e}, minS={rmin:.4g}')
        necessary_dollar=(n-1)*(1-math.exp(-2*z.crisis))/2
        check(f'necessary_dollar_N{n}_L{L}',z.turnover>=necessary_dollar-1e-9,
              f'actual {z.turnover:.5f} >= necessary {necessary_dollar:.5f}')
        rows.append({'n':n,'k':n-1,'T':T,'L':L,'achieved_crisis':z.crisis,'turnover':z.turnover,
                     'max_shares_sold':z.max_gross_share_sales,'max_dollar_residual':z.residual_dollars})

# Distinct zero-net-dollar and zero-net-share accounting.
z=spectator_closed_path(3,3,5)
check('shares_not_dollars',bool(np.max(np.abs(z.shares_delta[-1]))>.1 and np.max(np.abs(z.cumulative_dollars[-1]))<1e-10),
      f'max_terminal_delta_shares={np.max(np.abs(z.shares_delta[-1])):.5f}')

# Valid critical curve, monotonicity (no claim of independent proof of sharpness).
for n in (2,3,12,100):
    horizons=np.array([.2,.5,1.,2.,4.])
    values=np.log(np.sqrt(n)/(1+(np.sqrt(n)-1)*np.exp(-horizons)))
    check(f'critical_curve_N{n}',bool(np.all(values>0) and np.all(np.diff(values)>0) and max(values)<.5*math.log(n)),
          f'values={values.round(6).tolist()}')

# Local general-p family small-dollar experiment should reflect ordering under fixed controls.
for h in (.02,.10,.20):
    by_p={p:two_pulse(3,2,p,h,3)['crisis'] for p in (0,1,2)}
    check(f'abc_order_h{h}',by_p[0]>by_p[1]>0>by_p[2],
          f'C(p=0,1,2)={[by_p[p] for p in (0,1,2)]}')

output={'label':'deterministic numerical checks only, not formal proof or real market calibration',
        'count':len(checks),'checks':checks,'severe_witnesses':rows}
OUT.write_text(json.dumps(output,indent=2)+'\n')
print(f'PASSED {len(checks)} deterministic regression assertions')
print('Output:',OUT)
