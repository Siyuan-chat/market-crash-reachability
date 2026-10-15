"""Independent manuscript/certificate consistency audit for the two-day path.

This script does not implement a second interval ODE proof. It checks that the
written interval is a strict outward rounding of the certified endpoints and
independently integrates the stated six-segment ODE with SciPy DOP853.
"""
from __future__ import annotations
import json
import math
import hashlib
from decimal import Decimal, getcontext
from pathlib import Path
from scipy.integrate import solve_ivp

getcontext().prec = 70
ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / 'data/certificates/final_interval_certificate.json'
TEX = ROOT / 'paper/main.tex'

c = json.loads(CERT.read_text())
s = TEX.read_text()
assert c['steps'] == 80000 and c['step']=='0.0005'
assert c['certified_delta_0_020_reached_by_exact_rationals'] is True
assert c['certified_delta_0_021_not_reached_by_exact_rationals'] is True
assert c['zero_dollar_target_exact_from_quadratic_root'] is True
assert c['zero_dollar_comp_from_pairing'] is True
assert c['gross_rate_strictly_under_1'] is True
assert c['daily_bands_strictly_respected'] is True
lo, hi = map(Decimal, c['y_at_knots'][-1]['y_interval'])
y20lo,y20hi=map(Decimal,c['y_at_knots'][2]['y_interval'])
assert Decimal('1.4047874') < lo < hi < Decimal('1.4055543')
assert Decimal('1.2219388') < y20lo < y20hi < Decimal('1.2225356')
assert s.count('1.4047874<Y/F<1.4055543') == 1
assert s.count('1.4047874<y(40)<1.4055543') == 2
assert '1.4054212' not in s and '1.4061949' not in s
assert '1.02020225507905<h<1.02020225507908' in s
assert c['algebraic_plateau_root_interval']==['1.02020225507905','1.02020225507908']
assert '\\left|\\sum_{i\\in J}\\dot X_i(t)\\right|' in s
assert Decimal('0.020')<Decimal(c['terminal_crisis_lower_and_upper_numerical'][0])
assert Decimal(c['terminal_crisis_lower_and_upper_numerical'][1])<Decimal('0.021')
assert max(Decimal(row['gross_rate_y_tight_upper']) for row in c['segments'])<Decimal('0.285')
assert Decimal(c['compensator_sold_shares_certified_upper'])<Decimal('2')
assert Decimal(c['paired_dollar_turnover_certified_upper'])<Decimal('3')

# Solve the plateau root without the certificate's numerical root bracket.
a = Decimal('101600000000')
b = Decimal('-97138000000')
d = Decimal('-6646157699')
h = (-b + (b*b-4*a*d).sqrt()) / (2*a)
assert Decimal('1.02020225507905') < h < Decimal('1.02020225507908')
times = [0.,2.3,17.7,20.,22.3,37.7,40.]
xs = [1.,float(h),float(h),0.97,0.995,0.995,0.9409]
rho=0.4
y=1.
rows=[]
for i in range(6):
 t0,t1=times[i:i+2]
 slope=(xs[i+1]-xs[i])/(t1-t0)
 def ode(t,z):
  x=xs[i]+slope*(t-t0)
  u=x*(slope+rho*(x-1))
  return [-rho*(z[0]-1)-9*u/z[0]]
 res=solve_ivp(ode,(t0,t1),[y],method='DOP853',rtol=2e-13,atol=1e-14,max_step=0.025)
 assert res.success
 y=float(res.y[0,-1])
 rows.append({'end_time':t1,'numeric_y':y})
assert float(lo) < y < float(hi)
crisis=(9*math.log(1/.9409)-math.log(y))/10
assert 0.020 < crisis < 0.021
# Paired-dollar bookkeeping: exact target endpoint root gives zero net dollar flow.
# x' term integrated analytically segmentwise.
recovery_integral=0.
for i in range(6):
 dt=times[i+1]-times[i]
 slope=(xs[i+1]-xs[i])/dt
 # ∫ x(x-1) dt, with x linear from a to b
 x0,x1=xs[i],xs[i+1]
 integral_xx=(x0*x0+x0*x1+x1*x1)*dt/3
 integral_x=(x0+x1)*dt/2
 recovery_integral += 0.4*(integral_xx-integral_x)
Xtarget=(xs[-1]**2-xs[0]**2)/2+recovery_integral
assert abs(Xtarget)<1e-11, Xtarget
out={
 'certified_interval':[str(lo),str(hi)],
 'publication_outward_interval':['1.4047874','1.4055543'],
 'independent_ode_y40':y,
 'independent_ode_crisis_function':crisis,
 'target_net_dollar_residual_independent_formula':Xtarget,
 'day_end_states':rows,
 'gross_rate_upper_from_cert':str(max(Decimal(row['gross_rate_y_tight_upper']) for row in c['segments'])),
 'source_sha256':hashlib.sha256(TEX.read_bytes()).hexdigest(),
 'certificate_sha256':hashlib.sha256(CERT.read_bytes()).hexdigest(),
 'scope':'certificate-source rerun + independent high-precision ODE; not a second formal interval proof',
 'status':'PASS'
}
(ROOT/'data/v11_certificate_alignment_audit.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
