"""Independent V12 coordinate-equivalence checks.

These checks support the exactly stated change of variables; they do NOT
validate the manuscript's unrelated global reachability constructions.
"""
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

S,F,eta,p=sp.symbols('S F eta p',positive=True)
g=eta*(S/F)**p
phi=F**p*(S**(2-p)-F**(2-p))/(eta*(2-p))
phi2=F**2*sp.log(S/F)/eta
assert sp.simplify(sp.diff(phi,S)-S/g)==0
assert sp.simplify(sp.diff(phi2,S)-S/g.subs(p,2))==0
assert sp.simplify(phi.subs(S,F))==0
assert sp.simplify(phi2.subs(S,F))==0
for exponent in (0,1,2):
   test=phi2 if exponent==2 else phi.subs(p,exponent)
   assert sp.simplify(sp.diff(test,S)-S/g.subs(p,exponent))==0

G=sp.Function('g',positive=True)
elasticity=S*sp.diff(G(S),S)/G(S)
curv1=(1-elasticity)/G(S)
curv2=S**2/G(S)*(2-elasticity)
assert sp.simplify(sp.diff(S/G(S),S)-curv1)==0
assert sp.simplify(S*sp.diff(S*S/G(S),S)-curv2)==0

FF=1.0; EE=0.7; PP=0.6; RHO=0.4

def level_to_y(s):
 return FF**PP*(s**(2-PP)-FF**(2-PP))/(EE*(2-PP))

def y_to_level(y):
 return (FF**(2-PP)+ EE*(2-PP)*y/(FF**PP))**(1/(2-PP))

def edge_flux(t):
 return 0.04 if t<0.5 else -0.04

def dydt_levels(t,s):
 flow=edge_flux(t)*np.array([-1.,1.])
 return -RHO*(s-FF)+EE*(s/FF)**PP*flow/s

def dydt_coordinate(t,y):
 s=y_to_level(y)
 flow=edge_flux(t)*np.array([-1.,1.])
 return flow-RHO*s*(s-FF)/(EE*(s/FF)**PP)

ys=np.zeros(2);ss=np.ones(2)
for t0,t1 in ((0.,.5),(.5,1.)):
 sl=solve_ivp(dydt_levels,(t0,t1),ss,method='DOP853',rtol=2e-13,atol=2e-14,max_step=.002)
 sy=solve_ivp(dydt_coordinate,(t0,t1),ys,method='DOP853',rtol=2e-13,atol=2e-14,max_step=.002)
 assert sl.success and sy.success
 ss=sl.y[:,-1];ys=sy.y[:,-1]
 assert np.min(ss)>0.0
 assert np.max(np.abs(level_to_y(ss)-ys)) < 2e-12
assert np.max(np.abs(ss-y_to_level(ys)))<2e-12

results={
  'p_family_symbolic_derivative':'PASS',
  'coordinate_normalization_at_F':'PASS',
  'arbitrary_g_curvature_formulae':'PASS',
  'independent_nontrivial_pair_ODE_comparison':'PASS',
  'max_dollar_coordinate_residual':float(np.max(np.abs(level_to_y(ss)-ys))),
  'note':'Numerical comparison only verifies coordinate equivalence in a two-asset test, not the global theorems.'
}
root=Path(__file__).resolve().parents[1]
(root/'data/v12_coordinate_verification.json').write_text(json.dumps(results,indent=2))
print(json.dumps(results,indent=2))
