"""Plot-only numerical reconstruction of the V7 interval-certified path.

The independent RIGOROUS proof is verification/certify_streak_interval.py.
This script uses SciPy only for smooth illustrative curves; printed values
cannot substitute for the rational certificate.
"""
from __future__ import annotations
import argparse,json,math
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp, quad
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

RHO=.4; K=9; RAMP=2.3
P_COEFFS=[101600000000,-97138000000,-6646157699]
H=(-P_COEFFS[1]+math.sqrt(P_COEFFS[1]**2-4*P_COEFFS[0]*P_COEFFS[2]))/(2*P_COEFFS[0])
TIMES=[0,RAMP,20-RAMP,20,20+RAMP,40-RAMP,40]
PRICES=[1,H,H,.97,.995,.995,.9409]

def build(out):
 out=Path(out);out.mkdir(parents=True,exist_ok=True)
 t_all=[]; y_all=[]; x_all=[];u_all=[]
 current=1.
 target_sold=0.;comp_sold=0.;paired_turnover=0.
 for j in range(6):
  ta,tb=TIMES[j:j+2];a,b=PRICES[j:j+2]
  v=(b-a)/(tb-ta)
  def at(tt):return a+v*(tt-ta)
  def ufun(tt):
   x=at(tt);return x*(v+RHO*(x-1))
  def dydt(tt,Y):return [-RHO*(Y[0]-1)-K*ufun(tt)/Y[0]]
  grid=np.linspace(ta,tb,round((tb-ta)/.005)+1)
  sol=solve_ivp(dydt,(ta,tb),[current],t_eval=grid,atol=1e-13,rtol=1e-12,method='DOP853',max_step=.02,dense_output=True)
  assert sol.success
  def weighted(fun):
   roots=[]
   if abs(v)>1e-12:
    z0=ta+(1-v/RHO-a)/v
    if ta < z0 < tb:roots=[z0]
   return sum(quad(fun,l,r,epsabs=1e-12)[0] for l,r in zip([ta]+roots,roots+[tb]))
  paired_turnover+=weighted(lambda tt: 9*abs(ufun(tt)))
  target_sold+=weighted(lambda tt:max(0,-ufun(tt))/at(tt))
  comp_sold+=weighted(lambda tt:9*max(ufun(tt),0)/sol.sol(tt)[0])
  if j>0:grid=grid[1:]; yy=sol.y[0,1:]
  else:yy=sol.y[0]
  current=sol.y[0,-1]
  t_all.extend(grid);y_all.extend(yy);x_all.extend(at(grid));u_all.extend(ufun(grid))
 t=np.array(t_all);x=np.array(x_all);y=np.array(y_all);u=np.array(u_all)
 rx=np.abs(u)/x;ry=9*np.abs(u)/y
 q=9*np.log(1/.9409)/10-np.log(y[-1])/10
 np.savetxt(out/'improved_two_day_path.csv',np.column_stack([t,x,y,u,rx,ry]),delimiter=',',header='time,target_price,compensator_price,target_dollar_rate,target_gross_share_rate,compensator_gross_share_rate',comments='')
 report={'h':float(H),'ramp':RAMP,'y_day1':float(np.interp(20,t,y)),'y_day2':float(y[-1]),
  'crisis':float(q),'gross_rate_numerical':float(max(rx.max(),ry.max())),
  'target_sold_numerical':float(target_sold),'comp_sold_numerical':float(comp_sold),
  'paired_dollar_turnover_numerical':float(paired_turnover)}
 (out/'improved_witness_illustration.json').write_text(json.dumps(report,indent=2))
 plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False,'savefig.bbox':'tight'})
 fig,ax=plt.subplots(figsize=(7.2,3.15))
 ax.plot(t,x,label='9 streaking assets (each)',linewidth=1.8)
 ax.plot(t,y,label='1 compensating asset',linewidth=1.8)
 ax.axhline(.97,linestyle=':',linewidth=.8,color='0.4');ax.axhline(.9409,linestyle=':',linewidth=.8,color='0.4')
 ax.axvline(20,linestyle='--',color='0.5',linewidth=1)
 ax.fill_between([0,20],[.97,.97],[1.03,1.03],alpha=.08)
 y1=report['y_day1'];ax.fill_between([20,40],[.75*y1]*2,[1.25*y1]*2,alpha=.08)
 ax.text(20.3,.945,'day-2 reset floor',fontsize=8)
 ax.set(xlabel='Trading time',ylabel='Executed price / initial price',title='Certified two-session repeated lower-limit closes')
 ax.legend(frameon=False,loc='upper left');fig.tight_layout();fig.savefig(out.parent/'figures/v7_certified_multiday_prices.pdf');plt.close(fig)
 fig,ax=plt.subplots(figsize=(7.2,3.0))
 ax.plot(t,ry,label='Compensator: executed shares per unit time',linewidth=1.7)
 ax.plot(t,rx,label='Each streaking asset',linewidth=1.5)
 ax.axhline(.285,linestyle='--',color='0.3')  # certified rate limit; described in caption
 ax.axvline(20,linestyle=':',color='0.5')
 ax.set(xlabel='Trading time',ylabel='Gross executed share rate',title='Execution speed of the certified construction',ylim=(0,.35))
 ax.legend(frameon=True,facecolor='white',framealpha=1,edgecolor='none',loc='upper left');fig.tight_layout();fig.savefig(out.parent/'figures/v7_certified_rate_path.pdf');plt.close(fig)
 # Optimal rate bracket is a mathematical statement, not Monte Carlo confidence interval.
 fig,ax=plt.subplots(figsize=(7.2,1.9))
 ax.hlines(0,.044,.285,linewidth=7,alpha=.22)
 ax.vlines(.044,-.12,.12,linewidth=2)
 ax.vlines(.285,-.12,.12,linewidth=2)
 ax.text(.044,.16,'strict necessary floor\n$\\bar v_*>0.044$',ha='center',fontsize=9)
 ax.text(.285,.16,'interval-certified feasible path\n$\\bar v_*<0.285$',ha='center',fontsize=9)
 ax.set(xlim=(0,.35),ylim=(-.18,.40),xlabel='Gross executed-share rate cap (normalized units)',yticks=[],title='Unresolved global minimum: rigorous lower and upper bounds')
 ax.spines['left'].set_visible(False);ax.spines['bottom'].set_position(('data',0))
 fig.tight_layout();fig.savefig(out.parent/'figures/v7_minimum_rate_bracket.pdf');plt.close(fig)
 ns=np.arange(10,1001);q0=.97;c=.25;T=20
 def ratecut(k):
  m=ns-k
  return k/m*q0*q0*(1-q0*q0)/(2*T*(1+c)**2)
 k_one=ns-1;k_frac=np.ceil(.9*ns).astype(int)
 cut_one=ratecut(k_one);cut_fraction=ratecut(k_frac)
 fig,ax=plt.subplots(figsize=(7,3.0))
 ax.plot(ns,cut_one,label='One compensator, $k=N-1$')
 ax.plot(ns,cut_fraction,label=r'Fixed 90% breadth, $k=\lceil0.9N\rceil$',linestyle='--')
 ax.axhline(1.,linestyle=':',color='0.35',label='Reference cap 1')
 ax.set(xlabel='Number of assets $N$',ylabel='Necessary minimum gross rate',title='Cut-set funding capacity is controlled by $k/(N-k)$',ylim=(0,1.25))
 ax.legend(frameon=False,fontsize=8);fig.tight_layout();fig.savefig(out.parent/'figures/v7_cut_capacity_N.pdf');plt.close(fig)
 print(json.dumps(report,indent=2))
 return report
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--out',default='data');args=a.parse_args();build(Path(args.out))
