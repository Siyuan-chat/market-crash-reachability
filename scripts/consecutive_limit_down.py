"""Deterministic multi-session price-limit analysis for the ideal dollar-paired market.

This is NOT an order-book matching simulator; limit-hits here mean traded prices
reach a session floor, NOT unfilled sell queues or zero-volume locked sessions.

For p=0 and eta=F=1, nine target stocks have identical prescribed continuous
prices x(t). The tenth is a compensator y(t), computed INDEPENDENTLY by solving
  y'=-rho(y-1)-k*u(t)/y,
where u=x*(x'+rho*(x-1)) is each target's paired-dollar execution flow.

The target cash ledger is integrated from an exact piecewise-polynomial primitive.
Its first-session plateau is solved to enforce X_i(T_final)=0 exactly at the
mathematical model level. The numerical check of compensator positivity, bands,
and rate caps does not constitute a formal interval-arithmetic certificate.
"""
from __future__ import annotations
import argparse, json, math
from dataclasses import dataclass
from pathlib import Path
import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import brentq

@dataclass(frozen=True)
class Params:
    k: int = 9
    F: float = 1.0
    eta: float = 1.0
    rho: float = 0.4
    session: float = 20.0
    target_band: float = 0.03
    comp_band: float = 0.25
    second_high: float = 0.995
    ramp: float = 0.7
    rate_cap: float = 1.0


def knots(p: Params, first_high: float):
    t=p.session; a=p.ramp; q=1-p.target_band
    return np.asarray([
        [0.0,p.F], [a,first_high], [t-a,first_high], [t,p.F*q],
        [t+a,p.second_high], [2*t-a,p.second_high], [2*t,p.F*q*q]
    ],float)


def state_x(t, K):
    # One-sided right continuous derivative; changing derivative at finitely
    # many knots leaves the integrated state unchanged.
    j=int(np.searchsorted(K[:,0],t,side='right')-1)
    j=int(np.clip(j,0,len(K)-2))
    t0,x0=K[j]; t1,x1=K[j+1]
    v=(x1-x0)/(t1-t0)
    return x0+v*(t-t0),v


def segment_integral(x0,x1,dt):
    """Exact integral of x(t)*(x(t)-1) for linear x(t)."""
    return dt*((x0*x0+x0*x1+x1*x1)/3-(x0+x1)/2)


def target_ledger(t,K,p):
    x,_=state_x(t,K)
    integral=0.0
    for (t0,x0),(t1,x1) in zip(K[:-1],K[1:]):
        if t<=t0: break
        tstop=min(t,t1)
        if tstop>t0:
            xstop=x0+(x1-x0)*(tstop-t0)/(t1-t0)
            integral+=segment_integral(x0,xstop,tstop-t0)
    return (x*x-p.F*p.F)/(2*p.eta)+p.rho/p.eta*integral


def get_high(p):
    def res(h):
        K=knots(p,h)
        return target_ledger(2*p.session,K,p)
    low,high=1.005,1.029
    assert res(low)<0<res(high),(res(low),res(high))
    root=brentq(res,low,high,xtol=1e-14)
    assert abs(res(root))<1e-12
    return root


def get_solution(p:Params, samples:int=5001):
    h=get_high(p); K=knots(p,h)
    T=2*p.session
    # Dollar-matched flows: each of k targets transacts +u; compensator -ku.
    def fields(t,y):
        x,dx=state_x(t,K)
        u=x*(dx+p.rho*(x-p.F))/p.eta
        return [-p.rho*(y[0]-p.F)-p.eta*p.k*u/y[0],u]
    times=np.unique(np.r_[np.linspace(0,T,samples),K[:,0]])
    sol=solve_ivp(fields,(0,T),[p.F,0.],t_eval=times,rtol=1e-11,
                  atol=1e-12,method='DOP853',max_step=0.025)
    if not sol.success or sol.t.size!=times.size:raise RuntimeError(sol.message)
    x=np.array([state_x(t,K)[0] for t in times]);
    xprime=np.array([state_x(t,K)[1] for t in times]);
    u=x*(xprime+p.rho*(x-p.F))/p.eta
    y=sol.y[0]
    cap_target=np.abs(u)/x
    cap_comp=p.k*np.abs(u)/y
    xledger=np.array([target_ledger(t,K,p) for t in times]);
    yledger=-p.k*xledger
    # Independent consistency: the compensator's dollar ledger from its ODE.
    yprime=-p.rho*(y-p.F)-p.k*p.eta*u/y
    comp_xprime=(y/p.eta)*(yprime+p.rho*(y-p.F))
    pair_error=np.max(np.abs(p.k*u+comp_xprime))
    # Gross share sales in the two directions are finite and positive.
    sales_target=np.trapezoid(np.maximum(-u,0)/x,times)
    sales_comp=np.trapezoid(np.maximum(p.k*u,0)/y,times)
    turnover=np.trapezoid(p.k*np.abs(u),times)
    idx=np.searchsorted(times,p.session)
    assert abs(times[idx]-p.session)<1e-9
    base_y=y[idx]
    q=1-p.target_band
    band_floor_target=np.where(times<=p.session,q*p.F,q*q*p.F)
    band_top_target=np.where(times<=p.session,(1+p.target_band)*p.F,
                         (1+p.target_band)*q*p.F)
    band_floor_comp=np.where(times<=p.session,(1-p.comp_band)*p.F,
                         (1-p.comp_band)*base_y)
    band_top_comp=np.where(times<=p.session,(1+p.comp_band)*p.F,
                         (1+p.comp_band)*base_y)
    # At the session boundary, the old closing price satisfies both old and
    # new bands; either convention is valid there.
    lower_slack_y=y-band_floor_comp
    upper_slack_y=band_top_comp-y
    upper_slack_x=band_top_target-x
    lower_slack_x=x-band_floor_target
    assert min(y)>0
    assert min(lower_slack_y)>0.005
    assert min(upper_slack_y)>0.005
    assert min(upper_slack_x)>0.002
    assert min(lower_slack_x)>-5e-10
    assert cap_target.max()<p.rate_cap and cap_comp.max()<p.rate_cap
    assert abs(x[-1]-p.F*q*q)<1e-10
    assert abs(x[idx]-p.F*q)<1e-10
    assert abs(xledger[-1])<1e-11
    # Compute actual full-crisis functional alpha = k/(k+1).
    losses=np.log(p.F/np.r_[np.full(p.k,x[-1]),y[-1]])
    crisis=min(losses.mean(),np.sort(losses)[::-1][p.k-1])
    assert crisis>0
    # A second integration, using RK4 and a finer independent time grid,
    # is implemented below to cross-check compensator terminal price.
    day1_x=target_ledger(p.session,K,p)
    result={
        'n':p.k+1,'k':p.k,'coverage':p.k/(p.k+1),
        'number_of_sessions':2, 'rho':p.rho,'session_length':p.session,
        'target_lower_fraction':q,'target_band':p.target_band,
        'comp_band':p.comp_band,'rate_cap':p.rate_cap,
        'first_high':h,'second_high':p.second_high,
        'target_closes':[x[idx],x[-1]],'comp_closes':[base_y,y[-1]],
        'gross_rate_target_max':float(cap_target.max()),
        'gross_rate_comp_max':float(cap_comp.max()),
        'net_dollar_per_target_first_day':float(day1_x),
        'net_dollar_per_target_second_day':float(xledger[-1]-day1_x),
        'net_dollar_per_target_final':float(xledger[-1]),
        'net_dollar_comp_final':float(yledger[-1]),
        'max_pairing_derivative_error':float(pair_error),
        'gross_turnover':float(turnover),
        'max_gross_sold_shares':float(max(sales_target,sales_comp)),
        'target_gross_sold_shares':float(sales_target),
        'comp_gross_sold_shares':float(sales_comp),
        'terminal_crisis_functional':float(crisis),
        'terminal_average_log_loss':float(losses.mean()),
        'terminal_cover_quantile_log_loss':float(np.sort(losses)[::-1][p.k-1]),
        'max_upper_band_violation':float(max(-upper_slack_y.min(),-upper_slack_x.min(),0)),
        'min_strict_band_slack':float(min(lower_slack_y.min(),upper_slack_y.min(),upper_slack_x.min()))
    }
    return result, (times,x,y,u,cap_target,cap_comp,xledger,yledger,K,
                    band_floor_target,band_top_target,band_floor_comp,band_top_comp)


def necessary_scalar_speed(beta:float,D:int,rho:float,tau:float,F=1.,eta=1.):
    """Sharp one-asset necessary minimum cap ignoring counterparties."""
    q=1-beta; r=math.exp(-rho*tau)
    return rho*F/eta*np.asarray([
      1+q**(d-1)*(beta/(1-r)-1) for d in range(1,D+1)
    ])


def max_streak_scalar(beta:float,rate:float,rho:float,F=1.,eta=1.):
    """Global necessary max days from the rate-only price floor.
    Returns None if the rate-only certificate imposes no finite restriction.
    """
    vcrit=rho*F/eta
    if rate>=vcrit:return None
    floor=1-eta*rate/(rho*F)
    return max(0,int(math.floor(math.log(floor)/math.log(1-beta)+1e-12)))


def main(out:Path):
    out.mkdir(parents=True,exist_ok=True)
    p=Params()
    res, data=get_solution(p)
    t,x,y,u,rt,rc,X,Y,K,flx,upx,fly,upy=data
    from scipy.integrate import solve_ivp
    # Independently reconstruct comp y using a fourth-order Runge-Kutta step,
    # segment by segment to avoid evaluation across derivative jumps.
    def x_at(t):return state_x(t,K)
    def RHS(t,y):
        xx,dx=x_at(t); us=xx*(dx+p.rho*(xx-p.F))/p.eta
        return -p.rho*(y-p.F)-p.eta*p.k*us/y
    y_rk=1.0
    for j in range(len(K)-1):
        a,b=K[j,0],K[j+1,0]
        count=int(math.ceil((b-a)/.002))
        h=(b-a)/count
        # segment-specific derivative at endpoint avoids ambiguity
        slope=(K[j+1,1]-K[j,1])/(b-a)
        def fld(tt,yy):
            xx=K[j,1]+slope*(tt-a);uu=xx*(slope+p.rho*(xx-p.F))/p.eta
            return -p.rho*(yy-p.F)-p.eta*p.k*uu/yy
        for step in range(count):
            ti=a+step*h
            k1=fld(ti,y_rk);k2=fld(ti+h/2,y_rk+h*k1/2)
            k3=fld(ti+h/2,y_rk+h*k2/2);k4=fld(ti+h,y_rk+h*k3)
            y_rk+=h*(k1+2*k2+2*k3+k4)/6
    res['independent_rk4_comp_end_difference']=abs(y_rk-y[-1])
    assert res['independent_rk4_comp_end_difference']<1e-7
    with open(out/'consecutive_limit_down_summary.json','w') as f:
        json.dump(res,f,indent=2)
    import csv
    with open(out/'consecutive_limit_down_path.csv','w',newline='') as f:
        w=csv.writer(f);w.writerow(['time','target_price','compensator_price','target_signed_dollar_rate',
             'target_gross_share_rate','compensator_gross_share_rate',
             'target_net_dollars','compensator_net_dollars','target_daily_floor','target_daily_ceiling',
             'comp_daily_floor','comp_daily_ceiling']);
        for row in zip(t,x,y,u,rt,rc,X,Y,flx,upx,fly,upy):w.writerow(row)
    print(json.dumps(res,indent=2))
    return res,data

if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('--out',default='data')
    args=a.parse_args();main(Path(args.out))
