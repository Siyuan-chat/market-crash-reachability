"""Independent finite-rate and single-session price-band audit.

No use of V4's numerical_experiments or old constructive path routines.
Each executed-dollar rate is decomposed into nonnegative pairing edges.
Outputs machine-readable evidence and three new vector figures.
"""
from __future__ import annotations
import json, math, csv
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[1]
FIG = ROOT/'figures'; DAT=ROOT/'data'
FIG.mkdir(exist_ok=True,parents=True); DAT.mkdir(exist_ok=True,parents=True)

F=1.; ETA=1.; RHO=1.; T=3.
Delta=T/3.; r=math.exp(-RHO*Delta)
THREE = np.array([1., -(1.+r), r]); TWO=np.array([1.,0.,-1.])


def run(n=3,p=0,ampl=.045,shape=THREE, beta=None, cap=None, steps=181):
    assert n>=2
    u=np.ones(n);u[-1]=-(n-1)
    a=ampl*u
    # Each bin has a constant dollar rate a_i shape[j]. The sum over assets
    # is zero and the time integral vanishes per asset.
    def rhs(j):
        return lambda t,s: -RHO*(s-F)+ ETA*np.power(s/F,p)*a*shape[j]/s
    state=F*np.ones(n)
    times=[0.]; states=[state.copy()]; dollar=[np.zeros(n)]
    gross=[np.zeros(n)]; netsh=[np.zeros(n)]
    peak_gross=0.; totalpaired=0.; inventory=np.zeros(n)
    for j in range(3):
        t0=j*Delta; t1=(j+1)*Delta
        sol=solve_ivp(rhs(j),(t0,t1),state,atol=2e-13,rtol=2e-12,
                      dense_output=True, max_step=.012)
        if not sol.success: raise RuntimeError(sol.message)
        ts=np.linspace(t0,t1,steps)
        ys=sol.sol(ts).T
        if min(ys.reshape(-1)) <=0: raise ValueError('Nonpositive price')
        dollar_start=dollar[-1].copy()
        for idx,t in enumerate(ts[1:],start=1):
            prices=ys[idx]
            dt=t-t0
            led=a*shape[j]*dt + dollar_start
            times.append(float(t)); states.append(prices.copy());dollar.append(led.copy())
        state=sol.y[:,-1]
        # cumulative pairing dollars per bin
        totalpaired += np.sum(np.maximum(a*shape[j],0))*Delta
        if j==0: ledger=np.zeros(n); theta=np.zeros(n); sales=np.zeros(n)
        # Gross shares via quadrature, for the chosen minimum gross pairing.
        # Share rate is a_i*shape_j/S_i at any moment.
        from scipy.integrate import simpson
        samplet=np.linspace(t0,t1,1001)
        samples=sol.sol(samplet).T
        share_delta=simpson((a*shape[j])[None,:]/samples,x=samplet,axis=0)
        sales_delta=simpson(np.maximum(-(a*shape[j])[None,:]/samples,0),x=samplet,axis=0)
        theta += share_delta; sales += sales_delta
        peak_gross=max(peak_gross,float(np.max(np.abs(a*shape[j])[None,:]/samples)))
        ledger+=a*shape[j]*Delta
        dollar[-1]=ledger.copy()
    states=np.array(states); times=np.array(times); dollars=np.array(dollar)
    loss=np.log(F/states[-1]); k=math.ceil((n-1)/n*n-1e-12)
    crisis=min(loss.mean(),np.sort(loss)[::-1][k-1])
    # The max gross-share execution rate is |dx_i/dt|/S_i, because
    # this control uses the minimum gross 2-leg pairing at every instant.
    band_range=(states.min(),states.max())
    admissible=(cap is None or peak_gross<=cap+1e-10) and (beta is None or
       (band_range[0]>=F*(1-beta)-1e-10 and band_range[1]<=F*(1+beta)+1e-10))
    return dict(n=n,p=p,ampl=ampl,shape=shape.tolist(),time=times,price=states,
                dollar=dollars,loss=loss,crisis=crisis,
                totalpaired=totalpaired,peakgrossrate=peak_gross,
                grosssales=sales,netshares=theta,netdollar=ledger,
                minprice=float(states.min()),maxprice=float(states.max()),
                admissible=bool(admissible))


def check(cond,desc):
    if not cond:raise AssertionError(desc)


def calc_analytic_y():
    # exact integrals for the bounded-rate THREE signal in the linearized law
    nper=1001
    integral=0.; y=0.;h0=ETA/F
    for j in range(3):
        t0=j*Delta;t1=(j+1)*Delta
        tt=np.linspace(t0,t1,nper)
        yvals=np.exp(-RHO*(tt-t0))*y +(h0*THREE[j]/RHO)*(1-np.exp(-RHO*(tt-t0)))
        integral += np.trapezoid(np.exp(-RHO*(T-tt))*yvals**2,tt)
        y=yvals[-1]
    return y,(RHO/(2*F**2))*integral


def main():
    cases={}; nchecks=0
    a=run(ampl=.035,p=0,shape=THREE,cap=.15,beta=.15)
    b=run(ampl=.035,p=1,shape=THREE,cap=.15,beta=.15)
    c=run(ampl=.035,p=2,shape=THREE,cap=.15,beta=.15)
    check(a['admissible'] and b['admissible'] and c['admissible'],'finite cap and band')
    nchecks+=1
    for result in [a,b,c]:
        check(np.max(abs(result['netdollar']))<4e-15,'terminal dollar closure')
        check(np.max(abs(result['dollar'].sum(axis=1)))<1e-12,'pairing at all times')
        check(np.all(result['price']>0),'positive')
        nchecks+=3
    check(a['crisis']>0,'g constant local all-asset decline')
    check(c['crisis']<=1e-9,'p2 barrier');nchecks+=2
    yerr, coeff=calc_analytic_y()
    check(abs(yerr)<2e-6,'first variation y(T)=0'); nchecks+=1
    small=[]
    for z in [.003,.005,.008,.012,.020,.035,.055]:
        o=run(p=0,ampl=z,shape=THREE)
        # for u=(1,1,-2), Q_{2/3} tends to same small-asset loss
        small.append([z,o['crisis'],o['crisis']/z**2])
    check(abs(small[0][2]-coeff)<.04*coeff,
          f'local coefficient mismatch predicted {coeff} observed {small[0][2]}')
    nchecks+=1
    # Small-rate quadratic bound derives from gross-share rate and pairwise dollar balance.
    Qb=(ETA*.15/(F*RHO))**2*((1-math.exp(-RHO*T))-RHO*T*math.exp(-RHO*T)
          +(1-math.exp(-RHO*T))**2/(2*(1-ETA*.15*(1-math.exp(-RHO*T))/(F*RHO))**2))
    check(a['crisis'] <= Qb, f'quadratic rate exclusion {a["crisis"]} {Qb}')
    nchecks+=1
    # Two-stage control separately checks p1 partial-coverage and cap/band.
    p1partial=run(p=1,ampl=.05,shape=TWO,cap=.2,beta=.2)
    check(p1partial['crisis']>0 and p1partial['admissible'], 'p1 partial crash with finite speed')
    nchecks+=1
    # Rate-based exclusion and price floor certificates: if a path stays in the
    # admissible region, none of its terminal losses can exceed the cap.
    speedcaps=[]
    for nu in [0.025,0.05,0.1,0.15,0.2,0.3,0.5]:
        A=ETA*nu/RHO*(1-math.exp(-RHO*T))
        if A<F:
            dc=-math.log(1-A/F)
        else:dc=float('inf')
        speedcaps.append([nu,dc])
    pricebands=[]
    for beta in [.025,.05,.1,.15,.2,.3,.5]:
        pricebands.append([beta,-math.log(1-beta)])
    check(a['crisis']<= min(-math.log(1-.15),-math.log(1-ETA*.15*(1-math.exp(-T)))),
          'exclusion bound')
    nchecks+=1

    # Figures with model-generated data and visible units/certificates.
    fig,ax=plt.subplots(1,2,figsize=(9.0,3.2))
    for obj,tag in [(a,'p=0'),(b,'p=1'),(c,'p=2')]:
        ax[0].plot(obj['time'],obj['price'][:,0],label=tag,lw=1.9)
    ax[0].axhline(.85,ls='--',color='.45',label='lower band=0.85');
    ax[0].axhline(1.15,ls='--',color='.45')
    ax[0].set(xlabel='Time',ylabel='Asset 1 executed price',title='Finite-rate three-stage dollar circulation');ax[0].legend(frameon=False,fontsize=8)
    ax[1].plot(a['time'],a['dollar'][:,0],label='Asset 1',lw=2)
    ax[1].plot(a['time'],a['dollar'][:,-1],label='Asset 3',lw=2)
    ax[1].axhline(0,ls=':',color='.45');ax[1].set(xlabel='Time',ylabel='Cumulative signed dollars',title='Exactly closed at T; share positions need not close')
    ax[1].legend(frameon=False,fontsize=8);fig.tight_layout()
    fig.savefig(FIG/'bounded_rate_continuous_path.pdf',bbox_inches='tight');plt.close(fig)

    fig,ax=plt.subplots(figsize=(5.8,3.35))
    ax.plot([x[0] for x in small],[x[1] for x in small],'o-',lw=1.8,label='Independent nonlinear ODE integration')
    xs=np.array([x[0] for x in small]);ax.plot(xs,coeff*xs**2,ls='--',lw=2,label=r'Analytic $O(a^2)$ coefficient')
    ax.set(xlabel='Bounded dollar-rate amplitude a',ylabel='Terminal crisis function C(2/3)',title='Local crisis survives finite speed and price limits')
    ax.legend(frameon=False,fontsize=8);fig.tight_layout();fig.savefig(FIG/'finite_rate_quadratic.pdf',bbox_inches='tight');plt.close(fig)

    fig,ax=plt.subplots(figsize=(6.8,3.5))
    rates=np.linspace(.001,.5,500)
    dec=1-np.exp(-RHO*T)
    speed=-np.log(1-ETA*rates*dec/(F*RHO))
    bvals=ETA*rates*dec/(F*RHO)
    quadr=(ETA*rates/(F*RHO))**2*(dec-RHO*T*np.exp(-RHO*T)
            +dec**2/(2*(1-bvals)**2))
    base=np.minimum(speed,quadr)
    ax.plot(rates,speed,lw=1.1,ls=':',label='Single-asset rate comparison bound')
    ax.plot(rates,quadr,lw=1.6,label='Paired-flow quadratic rate bound')
    for beta,tag in [(0.1,'10% price floor'),(.2,'20% price floor')]:
        bd=-math.log(1-beta)
        ax.plot(rates,np.minimum(base,bd),lw=1.8,ls='--',label=f'Both constraints; {tag}')
    ax.set(xlabel='Maximum per-asset gross share rate v (shares / time)',ylabel='Certified upper bound on log crisis severity',ylim=(0,.65),title='Dollar pairing sharpens small-rate exclusion to O(v²)')
    ax.legend(frameon=False,fontsize=7.5);fig.tight_layout();fig.savefig(FIG/'rate_and_price_limit_bounds.pdf',bbox_inches='tight');plt.close(fig)

    n=3
    for res,tag in [(a,'p0_threestage'),(p1partial,'p1_twostage')]:
        with (DAT/f'finite_rate_{tag}.csv').open('w',newline='') as fh:
            wr=csv.writer(fh);wr.writerow(['time']+[f'S_{i+1}' for i in range(n)]+[f'X_{i+1}' for i in range(n)])
            wr.writerows(np.column_stack([res['time'],res['price'],res['dollar']]))
    with (DAT/'finite_rate_scaling.csv').open('w',newline='') as fh:
        wr=csv.writer(fh); wr.writerow(['amplitude','C_alpha','C_div_a2']);wr.writerows(small)
    summary={
        'checks':nchecks,
        'assumptions':{'N':3,'T':T,'F':F,'eta':ETA,'rho':RHO,'gross_rate_cap':.15,'single_session_beta':.15},
        'local_three_stage':{'p0_C':a['crisis'],'p1_C':b['crisis'],'p2_C':c['crisis'],
                             'minimum_price_p0':a['minprice'],'maximum_price_p0':a['maxprice'],
                             'terminal_dollar_residual':float(np.max(abs(a['netdollar']))),
                             'maximum_gross_share_rate':a['peakgrossrate'],
                             'total_executed_dollar_turnover':a['totalpaired'],
                             'maximum_share_sales':float(max(a['grosssales'])),
                             'first_variation_terminal':yerr,'quadratic_coefficient':coeff},
        'p1_partial':{'C':p1partial['crisis'],'peak_gross_rate':p1partial['peakgrossrate'],
                      'terminal_dollar_residual':float(np.max(abs(p1partial['netdollar']))),
                      'minprice':p1partial['minprice'],'maxprice':p1partial['maxprice']},
        'minspeed_necessary_formula':'v >= rho F (1-exp(-delta))/(G*(1-exp(-rho*T)))',
        'paired_quadratic_formula':'(eta*v/(F*rho))^2 * [ (1-e^-rhoT)-rho*T*e^-rhoT + (1-e^-rhoT)^2/(2(1-b)^2) ], b=eta*v*(1-e^-rhoT)/(F*rho)<1',
        'quadratic_certificate_at_v_015':float((ETA*.15/(F*RHO))**2*((1-math.exp(-RHO*T))-RHO*T*math.exp(-RHO*T)+(1-math.exp(-RHO*T))**2/(2*(1-ETA*.15*(1-math.exp(-RHO*T))/(F*RHO))**2))),
        'speed_caps':speedcaps,'price_bands':pricebands,
        'note':'Deterministic controlled price paths, no stochastic frequencies or observed prices'
    }
    (DAT/'finite_rate_verification.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({k:v for k,v in summary.items() if k not in ('speed_caps','price_bands')},indent=2))

if __name__=='__main__':main()
