"""Create four vector figures for multi-session rolling price-limit extension."""
from __future__ import annotations
import math
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.ticker as mticker
import numpy as np
from consecutive_limit_down import Params,get_solution,necessary_scalar_speed


def create(output='figures'):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    p=Params();s,data=get_solution(p)
    t,x,y,u,rt,rc,X,Y,K,flx,upx,fly,upy=data
    plt.rcParams.update({'font.size':9,'axes.titlesize':10,'pdf.fonttype':42,'ps.fonttype':42})

    fig,ax=plt.subplots(figsize=(7.2,3.2),layout='constrained')
    days=np.arange(1,51)
    for beta in (0.03,0.10):
        daily=necessary_scalar_speed(beta,50,rho=.4,tau=20.)
        ax.plot(days,daily,label=f'Down band {100*beta:.0f}%')
    ax.axhline(.2,ls='--',color='gray',label='Illustrative rate cap 0.20')
    ax.axhline(.4,ls=':',color='black',label=r'Constant-impact global floor: $\rho F/\eta=0.40$')
    ax.set(xlabel='Consecutive closing-limit session number',ylabel='Necessary per-asset gross share-rate cap',
           title='A rolling daily band does not remove the execution-rate barrier',xlim=(1,50),ylim=(0,.43))
    ax.grid(alpha=.19);ax.legend(fontsize=7,loc='lower right')
    fig.savefig(out/'multiday_rate_frontier.pdf',bbox_inches='tight');plt.close(fig)

    fig,axes=plt.subplots(2,1,figsize=(7.35,5.2),sharex=True,layout='constrained')
    for ax,pr,lower,upper,name in ((axes[0],x,flx,upx,'Nine targets (each 3% symmetric daily band)'),
                                   (axes[1],y,fly,upy,'One compensator (25% symmetric daily band)')):
        ax.plot(t,pr,lw=1.6,label='Executed price')
        # Band levels reset at the rollover; keep both sides visually separate.
        for side in (t<=p.session,t>p.session):
            ax.plot(t[side],lower[side],color='gray',ls='--',lw=.9)
            ax.plot(t[side],upper[side],color='gray',ls='--',lw=.9)
        ax.axhline(1.0,color='black',lw=.75,ls=':',label='Fixed fundamental benchmark')
        ax.axvline(p.session,color='gray',ls=':',lw=.9)
        ax.grid(alpha=.18);ax.set(ylabel='Normalized price',title=name)
    axes[0].scatter([p.session,2*p.session],s['target_closes'],marker='v',s=28,zorder=7,label='Close exactly at down limit')
    axes[0].legend(fontsize=7,loc='lower left')
    axes[-1].set_xlabel('Within-session trading-time units (session resets at 20)')
    fig.suptitle('Two consecutive lower-limit closes in 90% of assets: continuous paired execution',fontsize=11)
    fig.savefig(out/'multiday_streak_witness.pdf',bbox_inches='tight');plt.close(fig)

    fig,axes=plt.subplots(2,1,figsize=(7.35,5.0),sharex=True,layout='constrained')
    axes[0].plot(t,X,lw=1.6,label='Signed dollars per target')
    axes[0].plot(t,Y,lw=1.2,label='Compensator signed dollars')
    axes[0].axhline(0,color='black',lw=.8);axes[0].axvline(p.session,color='gray',ls=':',lw=.8)
    axes[0].legend(fontsize=8,loc='best');axes[0].set(ylabel='Accumulated signed executed dollars',
        title='Dollar ledgers close at session 2, not necessarily each day')
    axes[1].plot(t,rt,lw=1.4,label='Target gross shares/time')
    axes[1].plot(t,rc,lw=1.4,label='Compensator gross shares/time')
    axes[1].axhline(p.rate_cap,ls='--',color='black',label='Rate cap = 1')
    axes[1].axvline(p.session,color='gray',ls=':',lw=.8)
    axes[1].set(xlabel='Trading-time units',ylabel='Gross share rate',ylim=(0,1.1))
    axes[1].legend(fontsize=8,loc='best');axes[1].grid(alpha=.18)
    fig.savefig(out/'multiday_ledgers_and_rates.pdf',bbox_inches='tight');plt.close(fig)

    beta=np.linspace(.001,.35,400)
    threshold=beta/(1-beta)
    fig,ax=plt.subplots(figsize=(6.65,3.4),layout='constrained')
    ax.plot(100*beta,100*threshold,label=r'$\beta_+ = \beta_-/(1-\beta_-)$')
    ax.plot(100*beta,100*beta,ls='--',label='Symmetric daily band')
    ax.fill_between(100*beta,0,100*threshold,alpha=.12,label='All-asset second limit-down excluded')
    ax.set(xlabel=r'First-day lower band $\beta_-$ (%)',
      ylabel=r'Next-day upper band $\beta_+$ (%)',
      title='A two-session structural obstruction for all-asset lower-limit closes',
      xlim=(0,35),ylim=(0,60))
    ax.legend(fontsize=7,loc='upper left');ax.grid(alpha=.16)
    fig.savefig(out/'multiday_fullbreadth_obstruction.pdf',bbox_inches='tight');plt.close(fig)
    # Exact terminal crisis functional conditional on nine repeated floor closes.
    D=2; lam=-math.log(1-p.target_band); n=p.k+1
    yy=np.linspace((1-p.target_band)**D,1.58,450)
    breadth=D*lam
    mean=(p.k*breadth-np.log(yy/p.F))/n
    cc=np.minimum(breadth,mean)
    fig,ax=plt.subplots(figsize=(7.0,3.5),layout='constrained')
    ax.plot(yy,cc,lw=1.8,label=r'$\mathcal{C}_{0.9}=\min(A,Q_{0.9})$')
    ax.axhline(.015,color='gray',lw=1.2,ls='--',label=r'$\delta=0.015$')
    ax.axhline(.020,color='black',lw=1.2,ls=':',label=r'$\delta=0.020$')
    # Marker from the formally certified improved target path (not the older V6 path).
    calibrated=json.loads((Path(__file__).resolve().parents[1]/'data/improved_witness_illustration.json').read_text())
    witness_y=float(calibrated['y_day2']); witness_c=float(calibrated['crisis'])
    ax.axvline(witness_y,color='tab:orange',lw=1.3,ls='-.',label='Certified-path reconstruction')
    ax.scatter([witness_y],[witness_c],color='tab:orange',zorder=5,s=42)
    ax.set(xlabel='Other asset terminal price $Y/F$',ylabel='Terminal systemic log-loss functional',
           title='Nine consecutive lower-limit streaks do not fix systemic severity',
           xlim=(float(yy[0]),float(yy[-1])))
    ax.legend(loc='upper right',fontsize=7);ax.grid(alpha=.18)
    fig.savefig(out/'multiday_crisis_trigger.pdf',bbox_inches='tight');plt.close(fig)
    return [out/n for n in ['multiday_rate_frontier.pdf','multiday_streak_witness.pdf',
                            'multiday_ledgers_and_rates.pdf','multiday_fullbreadth_obstruction.pdf',
                            'multiday_crisis_trigger.pdf']]

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--out',default='figures')
    a=p.parse_args();print('\n'.join(map(str,create(a.out))))
