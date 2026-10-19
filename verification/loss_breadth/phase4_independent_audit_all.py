"""High-accuracy, separate two-solver numerical reconstruction for all five Phase 4 proof candidates.
Its solver agreement does NOT replace rational interval certification, and cannot establish infeasibility.
"""
import json, math, os
from pathlib import Path
ROOT=Path(__file__).resolve().parent
from fractions import Fraction as Fr
import numpy as np
from scipy.integrate import solve_ivp
from numpy.polynomial.legendre import leggauss

SOURCES=[
 str(ROOT/'phase4_certificate_k7_16p4_under_M3.json'),
 str(ROOT/'phase4_certificate_k9_8_under_M3.json'),
 str(ROOT/'phase4_certificate_full_0p75_under_M3.json'),
 str(ROOT/'phase4_certificate_k7_20_under_M4.json'),
 str(ROOT/'phase4_certificate_full_2_under_M7.json'),
]

def audit(filename):
 cert=json.load(open(filename));rates=[Fr(q) for q in cert['q_exact']];n=len(rates)
 assert n in (80,160)
 k,m=cert['k'],cert['m'];r=Fr(k,m);dt=Fr(40,n)
 assert sum(rates,Fr(0))==0
 M_exact=Fr(k)*dt*sum((abs(q) for q in rates),Fr(0))
 assert abs(float(M_exact)-cert['M_bound'])<1e-11
 prices=np.ones(2);prices2=prices.copy();day_ref=np.ones(2)
 sales=np.zeros(2);maxrate=0.;band=999.;maxerr=0.;width=0.;integrated_variance=0.
 points,weights=leggauss(8)
 for j,q in enumerate(rates):
  if j==n//2:day_ref=prices.copy()
  flow=np.array([float(q),-float(q*r)])
  a=float(dt*j);b=float(dt*(j+1));prev=prices.copy()
  def ode(t,s):return -.4*(s-1.)+flow/s
  z=solve_ivp(ode,(a,b),prices,method='DOP853',rtol=3e-13,atol=1e-14,max_step=.035,dense_output=True)
  z2=solve_ivp(ode,(a,b),prices2,method='Radau',rtol=1e-12,atol=3e-14,max_step=.05)
  assert z.success and z2.success
  prices=z.y[:,-1];prices2=z2.y[:,-1]
  maxerr=max(maxerr,float(max(abs(prices-prices2))))
  minprice=np.minimum(prev,prices);maxprice=np.maximum(prev,prices)
  band=min(band,float(np.min(minprice-.75*day_ref)),float(np.min(1.25*day_ref-maxprice)))
  maxrate=max(maxrate,float(np.max(abs(flow)/minprice)))
  sales+=np.maximum(-flow,0)*float(dt)/minprice
  for i,label in enumerate(('x','y')):
   L,U=map(float,cert['trace'][j][label])
   assert L<=prices[i]<=U,(filename,j,label,prices[i],L,U)
   width=max(width,U-L)
  tt=.5*(a+b)+.5*(b-a)*points
  path=z.sol(tt)
  vals=np.exp(-.4*(40.-tt))*(k*(path[0]-1.)**2+m*(path[1]-1.)**2)
  integrated_variance+=.5*(b-a)*np.dot(weights,vals)
 assert band>0 and maxrate<.285 and max(sales)<2
 assert M_exact<Fr(cert['M_cap'])
 H=.5*(k*(prices[0]**2-1)+m*(prices[1]**2-1))
 residual=H+.4/2*integrated_variance
 assert abs(residual)<1e-8,(filename,residual)
 target_loss=float(Fr(cert['target_loss_certified_strictly_greater_than']))
 assert 1-prices[0]>target_loss
 if cert['case'].startswith('full'):assert 1-prices[1]>target_loss
 meanlog=-float((k*np.log(prices[0])+m*np.log(prices[1]))/10)
 res={'case':cert['case'],'audit':'PASS','step_count':cert['steps'],'bins':n,
    'terminal_prices':prices.tolist(),'ordinary_target_drop':1-prices[0],
    'ordinary_comp_drop':1-prices[1],'mean_log_loss':meanlog,'geometric_index_drop':1-math.exp(-meanlog),
    'M_exact':str(M_exact),'M':float(M_exact),'max_gross_rate':maxrate,'min_price_band_margin':band,
    'shares_sold_upper':sales.tolist(),'max_independent_solver_disagreement':maxerr,
    'max_interval_enclosure_width':width,'radial_identity_residual':residual,
    'source_certificate':filename,'scope':'Numerical crosscheck only; not an external or kernel-level proof audit'}
 print('INDEPENDENT AUDIT',res['case'],'PASS','terminal',[round(float(x),8) for x in prices],
       'd',round(float(1-prices[0]),6),'M',round(float(M_exact),5),'maxerr',format(maxerr,'.1e'),
       'radial',format(residual,'.1e'),flush=True)
 return res

if __name__=='__main__':
 results=[audit(p) for p in SOURCES]
 payload={'status':'PASS','cases':results,'warning':'Proof-critical verification is a separate handwritten integer interval program, not externally audited.'}
 json.dump(payload,open(ROOT/'phase4_all_independent_audits.json','w'),indent=2)
