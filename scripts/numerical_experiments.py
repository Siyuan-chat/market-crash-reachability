"""Deterministic experiments underlying the figures of When Can Markets Crash Without News?

Not a stochastic order book or an empirical calibration.
The p=0 severe construction is an exact-primitive trajectory with numerical root-finding
for the partition and compensating direction; final net-dollar closure is checked.
"""
from __future__ import annotations
import math
from dataclasses import dataclass
import numpy as np
from scipy.optimize import brentq


def dollar_pulse(s, dx, p: float, F: float = 1., eta: float = 1.):
    s = np.asarray(s, dtype=float)
    dx = np.asarray(dx, dtype=float)
    a = 2. - p
    scaled = s / F
    if abs(a) < 1e-12:
        ans = F * scaled * np.exp((eta/F**2)*dx)
    else:
        val = scaled**a + a*(eta/F**2)*dx
        if np.any(val <= 0):
            raise ValueError('A pulse crosses zero price')
        ans = F*val**(1/a)
    if np.any(ans <= 0):
        raise ValueError('Nonpositive price')
    return ans


def systemic_crisis(prices, alpha: float, F=1.):
    loss = np.log(F/np.asarray(prices, dtype=float))
    k = math.ceil(alpha * len(loss) - 1e-12)
    return min(loss.mean(),np.sort(loss)[::-1][k-1])


def two_pulse(n=3, k=2, p=1, h=.1, T=3., F=1., eta=1., rho=1.):
    """A balanced pair h*u, -h*u separated by T units of recovery time."""
    if not 1<=k<n: raise ValueError('1<=k<n required')
    u = np.r_[np.ones(k), -float(k), np.zeros(n-k-1)]
    s0 = F*np.ones(n)
    s1 = dollar_pulse(s0, h*u, p, F, eta)
    s2 = F + (s1-F)*math.exp(-rho*T)
    s3 = dollar_pulse(s2,-h*u,p,F,eta)
    return dict(s0=s0,s1=s1,s2=s2,s3=s3,u=u,
        crisis=systemic_crisis(s3,k/n,F),turnover=h*np.abs(u).sum(),
        signed_dollars=np.zeros(n))


@dataclass
class ClosedPath:
    n: int
    k: int
    T: float
    loss_target: float
    high: float
    low: float
    compensator: float
    crisis: float
    average_loss: float
    q_alpha: float
    turnover: float
    max_gross_share_sales: float
    residual_dollars: float
    times: np.ndarray
    prices: np.ndarray
    cumulative_dollars: np.ndarray
    shares_delta: np.ndarray
    cumulative_turnover: np.ndarray
    labels: list[str]


def spectator_closed_path(n=3, T=3., loss_target=5., low=.001, steps_per_sector=25):
    """Construct n-1 low-price targets and one compensator in p=0 market.

    Normalization F=eta=rho=1. Executes marginal-price-integrated paired-dollar
    pulses and time-continuous rebalancing. All n terminal dollar ledgers must close.
    """
    if n < 2 or T <= 0 or low <=0: raise ValueError('invalid n,T,low')
    k=n-1; eps=math.exp(-loss_target)
    def params(b):
        aa=1-b*b-(k-1)*low*low
        if aa<=0: raise ValueError('invalid high direction')
        a=math.sqrt(aa); H=a+(k-1)*low+b; z=math.sqrt(n)-H
        def R(t): return H+z*math.exp(-t)
        def IR(t): return H*t+z*(-math.expm1(-t))
        def IR2(t): return H*H*t+2*H*z*(-math.expm1(-t))+z*z*(-math.expm1(-2*t))/2
        return a,H,R,IR,IR2
    def mismatch(b):
        a,H,R,IR,IR2=params(b)
        pcomp=R(T)**2-k*eps**2
        return (pcomp-1)+2*(b*b*IR2(T)-b*IR(T))
    left=1e-8; right=.25
    if mismatch(left)*mismatch(right)>=0:
        raise ValueError(f'No compensator root on interval: {mismatch(left)}, {mismatch(right)}; increase T or target')
    b=brentq(mismatch,left,right,xtol=1e-14)
    a,H,R,IR,IR2=params(b)
    def IW(t):return (a*a-low*low)*IR2(t)-(a-low)*IR(t)
    base=low*low*IR2(T)-low*IR(T)
    wtarget=(1-eps*eps)/2-base
    if abs(k*wtarget-IW(T))>2e-9: raise AssertionError('Partition balance failed')
    if wtarget<=0: raise ValueError('Negative target recovery weight')
    cuts=[0.] + [brentq(lambda t: IW(t)-j*wtarget,0,T,xtol=1e-14) for j in range(1,k)] + [T]
    pstar=np.r_[np.full(k,eps*eps),R(T)**2-k*eps*eps]
    if min(pstar)<=0: raise ValueError('nonpositive final price')
    prices=np.ones(n); ledger=np.zeros(n); shares=np.zeros(n); gross=np.zeros(n); budget=0.
    times=[]; ps=[]; xs=[]; ts=[]; ms=[]; labels=[]
    def record(t,label):
        times.append(t);ps.append(prices.copy());xs.append(ledger.copy());ts.append(shares.copy());ms.append(budget);labels.append(label)
    record(0.,'initial')
    def pulse(next_prices,t,label):
        nonlocal prices,ledger,shares,gross,budget
        new=np.asarray(next_prices,dtype=float)
        dx=(new*new-prices*prices)/2
        dth=new-prices
        if min(new)<=0 or abs(sum(dx))>3e-9: raise AssertionError(f'invalid pulse: {label}')
        ledger+=dx; shares+=dth; gross+=np.maximum(-dth,0)
        budget+=np.maximum(dx,0).sum()
        prices=new.copy();record(t,label)
    f=np.r_[[a],np.full(k-1,low),[b]]
    pulse(R(0)*f,0.,'initial reallocation')
    for j in range(k):
        f=np.r_[np.full(k,low),[b]]; f[j]=a
        t0,t1=cuts[j],cuts[j+1]
        assert np.max(abs(prices-R(t0)*f))<2e-8
        ledger0=ledger.copy();shares0=shares.copy();gross0=gross.copy();B0=budget
        coef_dollar=f*(f*H-1)
        coef_shares=f*H-1
        assert abs(sum(coef_dollar))<1e-10
        for t in np.linspace(t0,t1,steps_per_sector+1)[1:]:
            dIR=IR(float(t))-IR(t0)
            dx=coef_dollar*dIR
            dtheta=coef_shares*(float(t)-t0)
            ledger=ledger0+dx
            shares=shares0+dtheta
            gross=gross0+np.maximum(-dtheta,0)
            budget=B0+np.maximum(dx,0).sum()
            prices=R(float(t))*f
            record(float(t),'continuous rebalancing')
        if j<k-1:
            f2=f.copy();f2[j]=low;f2[j+1]=a
            pulse(R(t1)*f2,t1,'high-price rotation')
    pulse(np.sqrt(pstar),T,'terminal rebalance')
    residual=float(max(abs(ledger)))
    if residual>5e-9:raise AssertionError(f'dollar closure failed {residual}')
    arrP=np.asarray(ps); arrX=np.asarray(xs); arrS=np.asarray(ts)
    if np.min(arrP)<=0:raise AssertionError('lost positivity')
    if np.max(np.abs(arrX.sum(axis=1)))>5e-8:raise AssertionError('instantaneous pairing failed')
    losses=np.log(1/arrP[-1]);avg=float(losses.mean()); q=float(np.sort(losses)[::-1][k-1]); c=min(avg,q)
    return ClosedPath(n,k,T,loss_target,a,low,b,c,avg,q,budget,float(gross.max()),residual,
        np.asarray(times),arrP,arrX,arrS,np.asarray(ms),labels)

if __name__=='__main__':
    for n,T in [(3,3.),(12,4.),(20,5.)]:
        for L in (3.,5.,10.,20.):
            z=spectator_closed_path(n=n,T=T,loss_target=L)
            print(f'n={n:2} L={L:4g} C={z.crisis:.8f} M={z.turnover:.8f} H={z.max_gross_share_sales:.8f} Xerror={z.residual_dollars:.3g}')
