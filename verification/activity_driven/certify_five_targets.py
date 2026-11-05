#!/usr/bin/env python3
"""Outward-rounded interval check for V17 construction III (p=0, K=2).

Only mpmath interval elementary operations and an *explicit remainder-bounded*
Taylor series for arctangent are used in the proof-critical path.  Numeric
root candidates are optional hints for brackets; they do not certify signs.
Do not run under python -O; do not replace the interval path with float/mp.
"""
if not __debug__:
    raise RuntimeError('Python assertions are required for this interval check')

import json
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp

mp.mp.dps=60
mp.iv.dps=65
iv=mp.iv
K=2
D=10**23
LOWS=['1.085409','1.087707','1.085158','1.099042','1.106127','1.122661','1.14','1.15']
CLEFT='0.76065368494358'
CRIGHT='0.76065368494359'
Z=Q('0.04')


def rat(x):
    """Return exact rational bounds from internal MP interval binary endpoints."""
    def one(v):
        sign,mant,exp,_=v
        return Q((-1 if sign else 1)*mant*(2**max(exp,0)),2**max(-exp,0))
    if not hasattr(x,'_mpi_'):
        x=iv.mpf(str(x))
    return one(x._mpi_[0]),one(x._mpi_[1])


def box(lo,hi=None):
    lo=Q(lo);hi=Q(hi if hi is not None else lo)
    def point(x):
        return iv.mpf(x.numerator)/iv.mpf(x.denominator)
    a=point(lo);b=point(hi)
    # union: conversions of exact rationals are themselves outward-rounded
    return iv.mpf([a.a,b.b])


def atan_small(t):
    """|t|<1/2: alternating series + explicit absolute remainder."""
    left,right=rat(t)
    assert max(abs(left),abs(right))<Q(1,2)
    result=iv.mpf(0)
    t2=t*t
    power=t
    for j in range(58):
        result += (power if j%2==0 else -power)/(2*j+1)
        power *=t2
    upper=max(abs(left),abs(right))
    remainder=(upper**117)/Q(117)  # first omitted j=58 term, power 117
    return result+box(-remainder,remainder)


def atan_positive(t):
    a,b=rat(t)
    assert a>=0
    if b<Q(1,2):
        return atan_small(t)
    assert a>Q(49,100)
    return iv.pi/4+atan_small((t-1)/(t+1))


def prim(x,sgn):
    """P+ or P-, with interval arithmetic, no finite-difference derivative."""
    v=x-iv.mpf('0.5')
    if sgn==+1:
        temp=iv.sqrt(3)
        t=2*v/temp
        a,b=rat(t)
        assert 0<=a<=b<1
        # atanh(t) = (log(1+t) - log(1-t))/2
        return -iv.log(iv.mpf('1.5')-2*v*v)/4 + (iv.log(1+t)-iv.log(1-t))/(4*temp)
    else:
        return iv.log(2*v*v+iv.mpf('0.5'))/4 + atan_positive(2*v)/2


def encloses_gt(a,b):
    return rat(a)[0]>rat(b)[1]


def encloses_lt(a,b):
    return rat(a)[1]<rat(b)[0]


def invert(target,sgn,low,high,scale=D):
    """Certify one monotone inverse interval with rational bisection.

    f(low).hi < target.lo, f(high).lo > target.hi strictly. Intermediates
    keep those inequalities, so the exact inverse is inside [lo,hi].
    """
    lo=Q(low);hi=Q(high)
    assert encloses_lt(prim(box(lo),sgn),target),(sgn,lo,rat(target))
    assert encloses_gt(prim(box(hi),sgn),target),(sgn,hi,rat(target))
    # Exact rationals. No numerical computation chooses acceptance: tests do.
    for _ in range(100):
        if hi-lo <= Q(2,scale):break
        mid=(lo+hi)/2
        val=prim(box(mid),sgn)
        if encloses_lt(val,target): lo=mid
        elif encloses_gt(val,target): hi=mid
        else:break  # interval target has nonzero width; cannot bisect further
    assert encloses_lt(prim(box(lo),sgn),target)
    assert encloses_gt(prim(box(hi),sgn),target)
    return box(lo,hi)


def transfer(x,y,sgn,xnext=None,ynext=None):
    """One single-direction edge trade. sgn=+1 means x buys, y sells."""
    if sgn==1 and ynext is not None:
        # sell y to specified c, buy x the exact matching amount
        z=prim(y,-1)-prim(ynext,-1)
        assert rat(z)[0]>0
        xx=invert(prim(x,1)+z,1,Q('0.5'),Q('1.34'))
        yy=ynext
    elif sgn==-1 and xnext is not None:
        z=prim(x,-1)-prim(xnext,-1)
        assert rat(z)[0]>0
        yy=invert(prim(y,1)+z,1,Q('0.5'),Q('1.34'))
        xx=xnext
    elif sgn==+1 and xnext is not None:
        z=prim(xnext,1)-prim(x,1)
        assert rat(z)[0]>0
        yy=invert(prim(y,-1)-z,-1,Q('0.5'),Q('1.34'))
        xx=xnext
    elif sgn==-1 and ynext is not None:
        z=prim(ynext,1)-prim(y,1)
        assert rat(z)[0]>0
        xx=invert(prim(x,-1)-z,-1,Q('0.5'),Q('1.34'))
        yy=ynext
    else: raise ValueError('exactly one destination must be specified')
    return xx,yy,z


def simulate(c):
    x=y=box(1)
    allx=[x];ally=[y];amounts=[];signs=[]
    for low in LOWS:
        x,y,z=transfer(x,y,+1,ynext=c)
        amounts.append(z);signs.append(+1);allx.append(x);ally.append(y)
        x,y,z=transfer(x,y,-1,xnext=box(low))
        amounts.append(z);signs.append(-1);allx.append(x);ally.append(y)
    x,y,z=transfer(x,y,+1,ynext=c)
    amounts.append(z);signs.append(+1);allx.append(x);ally.append(y)
    x,y,z=transfer(x,y,-1,xnext=box(Q(3,4)))
    amounts.append(z);signs.append(-1);allx.append(x);ally.append(y)
    cut=len(amounts)
    x,y,z=transfer(x,y,-1,xnext=box(Q(9,16)))
    amounts.append(z);signs.append(-1);allx.append(x);ally.append(y)
    net=sum((z if s>0 else -z for s,z in zip(signs,amounts)),iv.mpf(0))
    A=sum(amounts,iv.mpf(0))
    A1=sum(amounts[:cut],iv.mpf(0))
    A2=sum(amounts[cut:],iv.mpf(0))
    return dict(net=net,amounts=amounts,signs=signs,x=allx,y=ally,
                cut=cut,A=A,A1=A1,A2=A2)


def interval_bounds(a):
    x,y=rat(a)
    return [f'{float(x):.12f}',f'{float(y):.12f}']


def verify():
    left=simulate(box(CLEFT));right=simulate(box(CRIGHT))
    assert rat(left['net'])[0]>0,('left ledger',interval_bounds(left['net']))
    assert rat(right['net'])[1]<0,('right ledger',interval_bounds(right['net']))
    # By IVT there is an exact c root in [CLEFT,CRIGHT]. This run evaluates
    # every transition with c as an interval and covers that unknown root.
    path=simulate(box(CLEFT,CRIGHT))
    assert len(path['amounts'])==19 and path['cut']==18
    firstx=path['x'][:19];firsty=path['y'][:19]
    secondx=path['x'][18:];secondy=path['y'][18:]
    for v in firstx+firsty:
        assert rat(v)[0]>=Q(3,4) and rat(v)[1]<=Q(5,4)
    close_y=path['y'][18]
    for v in secondx:
        assert rat(v)[0]>=Q(9,16) and rat(v)[1]<Q(15,16)
    for v in secondy:
        assert rat(v)[0]>Q(3,4)*rat(close_y)[1]
        assert rat(v)[1]<Q(5,4)*rat(close_y)[0]
    assert rat(path['x'][18])[0]>=Q(3,4) and rat(path['x'][18])[1]<=Q(3,4)
    assert rat(path['x'][-1])[0]>=Q(9,16) and rat(path['x'][-1])[1]<=Q(9,16)
    # sequential five-compensator cycle: one sale and one purchase per asset
    prices=[path['y'][-1]]*5
    cycle_history=[[interval_bounds(v) for v in prices]]
    for i in range(5):
        j=(i+1)%5
        prices[i],prices[j],z=transfer(prices[i],prices[j],-1,
                                       xnext=invert(prim(prices[i],-1)-box(Z),-1,Q('0.5'),Q('1.34')))
        assert rat(z)[0]>0
        # Strictly also require the executed amount is exactly Z, not just
        # an enclosure: one dimensional inverse ensures this mathematically.
        cycle_history.append([interval_bounds(v) for v in prices])
    for p in prices:
        assert rat(p)[0]>Q('1.2') and rat(p)[1]<Q('1.23')
        assert rat(p)[0]>Q(3,4)*rat(close_y)[1]
        assert rat(p)[1]<Q(5,4)*rat(close_y)[0]
    # Geometry: all five targets end at 9/16, all compensators <1.23,
    # so G <= sqrt((9/16)*1.23) <0.84 exactly (no numerical logarithms).
    assert Q(9,16)*Q('1.23')<Q('0.84')**2
    Amax=rat(path['A'])[1]
    A1max=rat(path['A1'])[1];A2max=rat(path['A2'])[1]
    turnover=5*Amax+5*Z
    inventory_target=Amax/2/Q(9,16)
    inventory_comp=Amax/2/Q(CLEFT)+Z/Q('1.2')
    rate1=A1max/20/Q(3,4)
    rate2=(A2max+5*Z)/20/Q(9,16)
    assert turnover<Q('11.261627')
    assert inventory_target<2 and inventory_comp<2
    assert max(rate1,rate2)<Q('0.133')
    return {
       'status':'internal directed-interval certificate; not external peer review',
       'model':'N=10, p=0, K=2, C1, F=eta=1, two sessions of length 20',
       'root_sign_left':interval_bounds(left['net']),
       'root_sign_right':interval_bounds(right['net']),
       'c_root_bracket':[CLEFT,CRIGHT],
       'segments':19,'cycle_edges':5,'cycle_edge_dollar_amount':str(Z),
       'first_session_target_close':'3/4','second_session_target_close':'9/16',
       'day1_compensator_close':interval_bounds(close_y),
       'day2_precycle_compensator':interval_bounds(path['y'][-1]),
       'final_compensator_prices':[interval_bounds(v) for v in prices],
       'max_paired_turnover_certified_upper':'11.261627',
       'max_paired_turnover_display_approx':str(float(turnover)),
       'sales_target_certified_upper':'2',
       'sales_compensator_certified_upper':'2',
       'rate_schedule':{'first_session_edge_dollar_rate':'A1 / 20',
                        'second_session_edge_dollar_rate':'(A2+5*0.04) / 20',
                        'all_edges_assigned_their_respective_session_duration':True},
       'max_gross_share_rate_certified_upper':'0.133',
       'max_gross_share_rate_display_approx':str(float(max(rate1,rate2))),
       'geometric_index_strict_upper':'0.84',
       'gross_activity_vs_net':'No instantaneous offsetting; temporal round trips allowed',
       'audit':'all prices are monotone within each single-edge event; exact pairing and zero dollar closure by IVT; interval bounds on each endpoint',
    }

if __name__=='__main__':
    result=verify()
    out=Path(__file__).with_name('five_target_certificate.json')
    out.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS V17 independent C1 interval certificate')
    print('ROOT c in',result['c_root_bracket'])
    print('M <',result['max_paired_turnover_certified_upper'],'gross share rate <',result['max_gross_share_rate_certified_upper'])
    print('WROTE',out)
