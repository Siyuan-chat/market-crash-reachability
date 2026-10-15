"""Generate all PDF figures and numerical CSV/JSON files for the paper.

Usage: python scripts/make_figures.py
Dependencies: numpy, scipy, matplotlib. All figures are analytical or numerical
ILLUSTRATIONS of a specified idealized model, not empirical calibrations.
"""
from pathlib import Path
import sys, math, json, csv
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, FancyArrowPatch
from numerical_experiments import spectator_closed_path, two_pulse, systemic_crisis
ROOT=Path(__file__).resolve().parents[1]
FIG=ROOT/'figures'; DATA=ROOT/'data'
FIG.mkdir(exist_ok=True); DATA.mkdir(exist_ok=True)
plt.rcParams.update({
    'font.family':'serif','font.size':9.4,'axes.labelsize':9.4,'axes.titlesize':10.5,
    'figure.dpi':150, 'savefig.dpi':180,'pdf.fonttype':42,
    'legend.fontsize':8.0,'xtick.labelsize':8.5,'ytick.labelsize':8.5,
    'axes.spines.top':False,'axes.spines.right':False,
    'axes.titleweight':'semibold',
})
colors=plt.rcParams['axes.prop_cycle'].by_key()['color']

def save(fig,name):
    fig.savefig(FIG/name,bbox_inches='tight',pad_inches=.08)
    plt.close(fig)

def csv_rows(filename,headers,rows):
    with (DATA/filename).open('w',newline='') as f:
        w=csv.writer(f); w.writerow(headers);w.writerows(rows)

# Figure 1: clean schematic of one specified market, with wrapped text.
fig,ax=plt.subplots(figsize=(7.15,2.2));ax.set_xlim(0,12.15);ax.set_ylim(0,2.9);ax.axis('off')
items=[
    (.18,'Execution\nprimitives','positive prices\nshare accounting'),
    (3.21,'Effective\nresponse','marginal impact\n$g(S)>0$'),
    (6.24,'Recovery\n& dollar pairing','fixed $F$; recovery\nbalanced dollars'),
    (9.27,'Systemic\ncrisis target','breadth; log loss\nresource limits'),
]
for idx,(x,headline,subtitle) in enumerate(items):
    width=2.60
    r=FancyBboxPatch((x,.65),width,1.78,boxstyle='round,pad=0.06',
        linewidth=.85,edgecolor='0.52',facecolor=f'C{idx}',alpha=.11)
    ax.add_patch(r)
    ax.text(x+width/2,1.94,headline,ha='center',va='center',
            fontsize=9.1,weight='bold',linespacing=1.1)
    ax.text(x+width/2,1.12,subtitle,ha='center',va='center',
            fontsize=7.5,color='0.23',linespacing=1.25)
    if idx<3:
        ax.add_patch(FancyArrowPatch((x+2.70,1.51),(x+2.97,1.51),
                arrowstyle='-|>',mutation_scale=12,linewidth=1.1,color='0.38'))
ax.text(6.07,.23,
        'Price priority and accounting are primitive; impact and resilience are imposed model conditions',
        ha='center',fontsize=7.6,color='0.27')
save(fig,'market_specification.pdf')

# Figure 2: impact per dollar, p family.
s=np.linspace(.34,1.65,500)
fig,ax=plt.subplots(figsize=(6.7,3.2))
for p,name in [(2,'A: p=2 (constant)'),(1,'B: p=1 (inverse price)'),(0,'C: p=0 (inverse price squared)')]:
    ax.plot(s,s**(p-2),lw=2.2,label=name)
ax.axvline(1,ls=':',lw=1.1,color='0.4')
ax.set(xlabel=r'Price relative to benchmark, $S/F$',ylabel='Normalized log-price impact\nper executed dollar',ylim=(0,9.5),xlim=(.34,1.65))
ax.grid(alpha=.17);ax.legend(frameon=False,loc='upper right')
save(fig,'response_regimes.pdf')

# Figure 3: elasticity, contrasting global vs local condition.
s=np.linspace(.32,1.45,550)
fig,ax=plt.subplots(figsize=(6.3,3.1))
for y,label in [(np.zeros_like(s),r'$g_0(S)=1$'),(2*s*s/(s*s+.25),r'$g_1(S)=(S^2+0.25)/1.25$'),(3*s**3/(s**3+.2),r'$g_2(S)=(S^3+0.2)/1.2$')]:
    ax.plot(s,y,lw=2,label=label)
for v,tag in [(1,r'$e=1$ (all-asset barrier)'),(2,r'$e=2$ (systemic barrier)')]:
    ax.axhline(v,ls='--',lw=1,color='0.55');ax.text(1.43,v+.055,tag,ha='right',fontsize=7.2,color='0.38')
ax.axvline(1,ls=':',lw=.9,color='0.3');ax.set(xlabel=r'Price relative to benchmark, $S/F$',ylabel=r'Price-response elasticity $e(S)$',xlim=(.32,1.45),ylim=(-.08,3.03))
ax.grid(alpha=.12);ax.legend(frameon=False,loc='upper left')
save(fig,'elasticity_examples.pdf')

# Figure 4: same pair of pulses in the three markets, local comparison.
hs=np.linspace(.005,.22,90)
fig,(ax,ax2)=plt.subplots(1,2,figsize=(7.5,3.0),gridspec_kw={'width_ratios':[1.1,1]})
rows=[]
for p,tag in [(2,'A: p=2'),(1,'B: p=1'),(0,'C: p=0')]:
    C=[]
    for h in hs:
        z=two_pulse(n=3,k=2,p=p,h=float(h),T=3)
        C.append(z['crisis'])
        rows.append((p,float(h),z['crisis'],z['turnover']))
    ax.plot(4*hs,C,lw=2.05,label=tag)
    z=two_pulse(n=3,k=2,p=p,h=.2,T=3)
    ax2.scatter([0,1,2],[float(s) for s in z['s3']],s=33,label=tag)
    ax2.plot([0,1,2],z['s3'],lw=1.15,alpha=.7)
ax.axhline(.05,color='0.45',ls=':',lw=1)
ax.text(.79,.053,'illustrative log threshold = 0.05',ha='right',fontsize=7.2,color='0.35')
ax.set(xlabel='Total executed-dollar turnover (2 pulses)',ylabel=r'Terminal crisis functional $\mathcal{C}_{2/3}$',xlim=(0,.88))
ax.grid(alpha=.12);ax.legend(frameon=False,loc='upper left');ax.set_title('(a) Same dollar-flow sequence')
ax2.axhline(1,ls=':',color='0.5',lw=1);ax2.set_xticks(range(3),['1','2','3']);ax2.set(xlabel='Asset index',ylabel='Terminal price relative to F',title='(b) Terminal prices, turnover = 0.8')
ax2.grid(alpha=.1);ax2.legend(frameon=False,loc='best',fontsize=7.4)
fig.tight_layout(w_pad=1.3);save(fig,'abc_control_comparison.pdf')
csv_rows('abc_two_pulse_sweep.csv',['p','pulse_dollar_h','crisis_function','total_paired_turnover'],rows)

# Figure 5: paths of all assets for p=0, 3- and 12-asset controlled witness.
paths={3:spectator_closed_path(3,3,3),12:spectator_closed_path(12,4,3)}
fig,axs=plt.subplots(1,2,figsize=(7.5,3.25))
for ax,n in zip(axs,[3,12]):
    z=paths[n]
    for i in range(n):
        if n == 3:
            ax.plot(z.times,z.prices[:,i],lw=1.45,alpha=.94,
                    label=('compensator' if i==n-1 else f'asset {i+1}'))
        elif i == n-1:
            ax.plot(z.times,z.prices[:,i],lw=1.9,label='compensator')
        else:
            ax.plot(z.times,z.prices[:,i],lw=.82,alpha=.65,color='0.48',
                    label='11 target assets' if i==0 else None)
    ax.axhline(1,ls=':',lw=1,color='0.5')
    ax.set(xlabel='Recovery time t',ylabel='Relative prices S/F',title=rf'$N={n},\ k={n-1},\ C_\alpha={z.crisis:.2f}$')
    ax.set_yscale('log');ax.grid(alpha=.13)
    ax.set_ylim(.025, max(z.prices.max()*1.2,3))
    ax.legend(frameon=False,fontsize=7.1,loc='upper right')
fig.tight_layout(w_pad=1.2);save(fig,'closed_flow_price_paths.pdf')
for n,z in paths.items():
    csv_rows(f'closed_flow_path_N{n}.csv', ['time','event']+[f'price_{i+1}' for i in range(n)]+[f'net_dollars_{i+1}' for i in range(n)]+[f'net_shares_{i+1}' for i in range(n)]+['cum_turnover'],
        [[float(z.times[j]),z.labels[j]]+z.prices[j].tolist()+z.cumulative_dollars[j].tolist()+z.shares_delta[j].tolist()+[float(z.cumulative_turnover[j])] for j in range(len(z.times))])

# Figure 6: closure versus share positions for N=3 example.
z=spectator_closed_path(3,3,5)
fig,axs=plt.subplots(1,2,figsize=(7.5,2.85))
for i in range(3):
    axs[0].plot(z.times,z.cumulative_dollars[:,i],label=f'asset {i+1}',lw=1.65)
    axs[1].plot(z.times,z.shares_delta[:,i],label=f'asset {i+1}',lw=1.65)
for ax in axs:
    ax.axhline(0,color='0.45',lw=.9,ls=':');ax.grid(alpha=.14);ax.set_xlabel('Recovery time t')
axs[0].set(ylabel='Cumulative signed executed dollars',title='(a) Each dollar ledger ends at zero')
axs[1].set(ylabel='Change in share holdings',title='(b) Share holdings need not close')
axs[1].legend(frameon=False,loc='best',fontsize=7.5)
fig.tight_layout(w_pad=1.2);save(fig,'dollar_vs_share_closure.pdf')

# Figure 7: bounded feasible turnover and share sales as target log loss grows.
fig,axs=plt.subplots(1,3,figsize=(9.4,2.88))
rows=[]
for n,T in [(3,3),(12,4),(20,5)]:
    Ls=np.linspace(3,19.8,39)
    Cs=[];Ms=[];Hs=[]
    for L in Ls:
        z=spectator_closed_path(n,T,float(L))
        Cs.append(z.crisis);Ms.append(z.turnover);Hs.append(z.max_gross_share_sales)
        rows.append((n,T,float(L),z.crisis,z.turnover,z.max_gross_share_sales,z.residual_dollars))
    axs[0].plot(Ls,Cs,label=f'N={n} (T={T:g})',lw=1.9)
    axs[1].plot(Ls,np.asarray(Ms)/n,lw=1.9)
    axs[2].plot(Ls,Hs,lw=1.9)
axs[0].set(ylabel=r'Crash functional $\mathcal{C}_\alpha$',xlabel='Target asset log loss')
axs[1].set(ylabel='Feasible turnover / asset',xlabel='Target asset log loss')
axs[2].set(ylabel='Maximum share sales / asset',xlabel='Target asset log loss')
for ax in axs:ax.grid(alpha=.14)
axs[0].legend(frameon=False,fontsize=7.2,loc='upper left')
axs[0].set_title('(a) Severe losses');axs[1].set_title('(b) Turnover bounded');axs[2].set_title('(c) Inventory bounded')
fig.tight_layout(w_pad=1.55);save(fig,'finite_resources_severe_crashes.pdf')
csv_rows('severe_crash_witnesses.csv',['N','horizon_T','target_logloss','achieved_crisis','feasible_turnover','max_gross_sale_shares','max_closed_dollar_residual'],rows)

# Figure 8: threshold for full coverage (strict unattained upper envelope).
z=np.linspace(.05,4,320)
fig,ax=plt.subplots(figsize=(6.2,2.9))
for n in (2,3,12,100):
    dc=np.log(np.sqrt(n)/(1+(np.sqrt(n)-1)*np.exp(-z)))
    ax.plot(z,100*(1-np.exp(-dc)),label=f'N={n}',lw=1.95)
ax.set(xlabel=r'Recovery-adjusted horizon $\rho T$',ylabel='Full-coverage common-decline supremum (%)',xlim=(0,4))
ax.grid(alpha=.15);ax.legend(frameon=False,loc='upper left',ncol=2)
save(fig,'full_coverage_threshold.pdf')

# Figure 9: phase diagram across N and rhoT for all-asset bound.
ns=np.arange(2,61); x=np.linspace(.15,5,150)
XX,NN=np.meshgrid(x,ns)
D=np.log(np.sqrt(NN)/(1+(np.sqrt(NN)-1)*np.exp(-XX)))
P=100*(1-np.exp(-D))
fig,ax=plt.subplots(figsize=(6.2,3.0))
c=ax.contourf(x,ns,P,levels=np.linspace(0,85,18),cmap='viridis')
cs=ax.contour(x,ns,P,levels=[20,40,50,60,70],colors='white',linewidths=.65)
ax.clabel(cs,inline=True,fontsize=7,fmt='%g%%')
ax.set(xlabel=r'Recovery-adjusted horizon $\rho T$',ylabel='Number of assets N',title='Strict supremum for full-coverage common price loss')
fig.colorbar(c,ax=ax,label='Common simple price loss (%)',pad=.015)
fig.tight_layout();save(fig,'all_asset_boundary_heatmap.pdf')

# Figure 10: necessary price impact resource lower bounds, not sufficiency.
d=np.linspace(.01,4,260);k=11
fig,axs=plt.subplots(1,2,figsize=(7.5,3.0))
for p in [0,1]:
    a=2-p;b=1-p
    Jd=k*(-np.expm1(-a*d))/a
    Js=k*(-np.expm1(-b*d))/b if b else k*d
    axs[0].plot(d,Jd,lw=2,label=f'p={p}')
    axs[1].plot(d,Js,lw=2,label=f'p={p}')
axs[0].set(xlabel=r'Log-loss threshold $\delta$',ylabel='Necessary total paired-dollar turnover')
axs[1].set(xlabel=r'Log-loss threshold $\delta$',ylabel='Necessary total executed share sales')
for ax in axs:ax.grid(alpha=.16);ax.legend(frameon=False,loc='upper left')
axs[0].set_title('(a) Dollar resource lower bounds')
axs[1].set_title('(b) Share resource lower bounds')
fig.tight_layout(w_pad=1.2);save(fig,'resource_lower_bounds.pdf')

# Figure 11: dependence on N of necessary amount at fixed 90% coverage.
fig,ax=plt.subplots(figsize=(6.2,2.75))
Ns=np.arange(2,81)
for p in [0,1]:
    d=.4; karr=np.ceil(.9*Ns).astype(int)
    lower=karr*(-math.expm1(-(2-p)*d))/(2-p)
    ax.step(Ns,lower,where='post',lw=1.9,label=f'p={p}')
ax.set(xlabel='Number of assets N',ylabel='Necessary paired-dollar turnover (normalized)',title=r'Fixed $\alpha=0.9,\ \delta=0.4$ (necessary bounds, not optima)')
ax.grid(alpha=.14);ax.legend(frameon=False)
save(fig,'resource_scaling_N.pdf')

# Reproducibility summary, with exact decimal diagnostics (not probabilistic sampling).
base={(int(n),float(L)):(C,M,H,R) for n,_,L,C,M,H,R in rows}
summary={
 'model':'idealized marginally settled paired-dollar resilient model, F=eta=rho=1',
 'crisis_definition':'min(mean log loss, kth largest log loss)',
 'figure_files':sorted(p.name for p in FIG.glob('*.pdf')),
 'n3_case':{'T':3,'k':2,'target_log_loss':5,'crisis':spectator_closed_path(3,3,5).crisis,'turnover':spectator_closed_path(3,3,5).turnover,'max_gross_sale_shares':spectator_closed_path(3,3,5).max_gross_share_sales,'max_dollar_closure_residual':spectator_closed_path(3,3,5).residual_dollars},
 'n12_case':{'T':4,'k':11,'target_log_loss':5,'crisis':spectator_closed_path(12,4,5).crisis,'turnover':spectator_closed_path(12,4,5).turnover,'max_gross_sale_shares':spectator_closed_path(12,4,5).max_gross_share_sales,'max_dollar_closure_residual':spectator_closed_path(12,4,5).residual_dollars},
 'figure_description':'Figures are analytic curves or deterministic constructed paths, not estimated time series and not actual market observations',
}
(DATA/'figure_verification.json').write_text(json.dumps(summary,indent=2)+'\n')
print('Wrote',len(summary['figure_files']),'vector figures to',FIG)
print(json.dumps(summary,indent=2))
