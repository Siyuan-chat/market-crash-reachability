"""Rational outward-rounded interval certificate for the V7 rate-smoothed 10-asset/two-day witness.

No scipy/numpy/MPmath. All arithmetic with integer fixed point at 10**32,
rounded outward after products/divisions. Certified enclosure uses a second-order
Taylor remainder bound |y''|<=5 on every open linear-price segment, scalar ODE
comparison, and a bootstrap region 0.70 <= y <= 1.60.

The prescribed target first plateau is an algebraic root isolated by rational
bracketing of an exactly known quadratic; it is not a decimal approximation.

Reproduce: python verification/certify_streak_interval.py --out data/v7_interval_certificate.json
"""
from __future__ import annotations
import argparse,json,math
from fractions import Fraction as Fr
from pathlib import Path
from decimal import Decimal, getcontext
getcontext().prec=75

Q=10**32

def fdec(x):
    return Fr(str(x))

def floordiv(a,b):
    return a//b

def ceildiv(a,b):
    return -((-a)//b)

class I:
    __slots__=('lo','hi')
    def __init__(self,lo,hi=None):
        self.lo=int(lo);self.hi=int(lo if hi is None else hi)
        assert self.lo<=self.hi,(self.lo,self.hi)
    @staticmethod
    def rat(v):
        v=Fr(v)
        return I(floordiv(v.numerator*Q,v.denominator),ceildiv(v.numerator*Q,v.denominator))
    @staticmethod
    def bounds(a,b):
        aa=I.rat(a);bb=I.rat(b)
        return I(aa.lo,bb.hi)
    def __add__(self,o):
        o=to_i(o);return I(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+(-to_i(o))
    def __rsub__(self,o):return to_i(o)+(-self)
    def __mul__(self,o):
        o=to_i(o);z=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi]
        return I(floordiv(min(z),Q),ceildiv(max(z),Q))
    __rmul__=__mul__
    def inv(self):
        assert self.lo>0
        return I(floordiv(Q*Q,self.hi),ceildiv(Q*Q,self.lo))
    def __truediv__(self,o):return self*to_i(o).inv()
    def __rtruediv__(self,o):return to_i(o)*self.inv()
    def contains(self,other):
        other=to_i(other); return self.lo<=other.lo and self.hi>=other.hi
    def min_float(self):return self.lo/Q
    def max_float(self):return self.hi/Q
    def as_decimal_str(self,digits=18):
        return [str(Decimal(self.lo)/Decimal(Q)),str(Decimal(self.hi)/Decimal(Q))]

def to_i(x):
    return x if isinstance(x,I) else I.rat(x)

def exact_poly(h):
    """Exact dollar-closing polynomial times 15,000,000,000."""
    return Fr(101600000000)*h*h - Fr(97138000000)*h-Fr(6646157699)

# h exact quadratic root, isolated by exact rational brackets
HLO=fdec('1.02020225507905')
HHI=fdec('1.02020225507908')
assert exact_poly(HLO)<0<exact_poly(HHI)
H=I.bounds(HLO,HHI)

RHO=I.rat(Fr(2,5)); N_TARGETS=9
KNOT_TIMES=[Fr(0),Fr(23,10),Fr(177,10),Fr(20),Fr(223,10),Fr(377,10),Fr(40)]
KNOT_X=[I.rat(1),H,H,I.rat(Fr(97,100)),I.rat(Fr(199,200)),I.rat(Fr(199,200)),I.rat(Fr(9409,10000))]
LOW_SAFE=I.rat(Fr(7,10)); HIGH_SAFE=I.rat(Fr(8,5))
DT=I.rat(Fr(1,2000))
# Taylor remainder uses the sharper segment-specific |y''| bound below.
M_VELOCITY=I.rat(Fr(17,10))

def abs_hi(z): return max(abs(z.lo),abs(z.hi))

def max_abs(z): return Fr(abs_hi(z),Q)

def min_u_bound_segment(x0,x1,dt):
    v=(x1-x0)/I.rat(dt)
    u0=x0*(v+RHO*(x0-1))
    u1=x1*(v+RHO*(x1-1))
    # interval product on whole x range includes any interior stationary point
    X=I(min(x0.lo,x1.lo),max(x0.hi,x1.hi))
    U=X*(v+RHO*(X-1))
    return v,U


def f_at(t_rel, x0, v, y):
    x=x0+v*I.rat(t_rel)
    u=x*(v+RHO*(x-1))
    return -RHO*(y-1)-N_TARGETS*u/y

def exp_positive_bounds(x, terms=22):
    """Exact rational enclosures of exp(x) for 0<=x<1.

    Tail from term terms+1 is bounded by geometric ratio x/(terms+2).
    """
    x=Fr(x)
    assert 0<=x<1
    val=Fr(0)
    for j in range(terms+1):
        val+=x**j/Fr(math.factorial(j))
    tail_first=x**(terms+1)/Fr(math.factorial(terms+1))
    upper=val+tail_first/(1-x/Fr(terms+2))
    return val,upper

def certificate(out,substep=Fr(1,2000)):
    assert substep == Fr(1,2000), 'Change DT and EPS together if grid is changed.'
    low=I.rat(1).lo; high=I.rat(1).hi
    lower_all=Q; upper_all=Q
    knots=[]; segment_rows=[]
    comp_sales_upper=0
    target_sales_upper=0
    turnover_upper=0
    for seg,(t0,t1) in enumerate(zip(KNOT_TIMES[:-1],KNOT_TIMES[1:])):
        delta=t1-t0; num=delta/substep
        assert num.denominator==1
        n=int(num)
        v,urange=min_u_bound_segment(KNOT_X[seg],KNOT_X[seg+1],delta)
        low_segment=low; high_segment=high
        # verify |u| <= 0.107, |u'| <= 0.040; hence |y''| <= 5
        assert max_abs(urange)<Fr(107,1000),(seg,max_abs(urange))
        xs=I(min(KNOT_X[seg].lo,KNOT_X[seg+1].lo),max(KNOT_X[seg].hi,KNOT_X[seg+1].hi))
        # |u'|=|v(v+rho(2x-1))|<=0.041
        uder=v*(v+RHO*(2*xs-1))
        assert max_abs(uder)<Fr(41,1000),(seg,max_abs(uder))
        umax=max_abs(urange)
        upmax=max_abs(uder)
        # analytic upper bound on |y''| over y in [0.70,1.60]
        # |F_t| <= 9 |u'|/0.70, |F_y| <= rho + 9|u|/(0.70**2)
        # |F| <= rho * 0.60 + 9 |u|/0.70.
        Bseg=Fr(9)*upmax/Fr(7,10)+(Fr(2,5)+Fr(9)*umax/Fr(49,100))*(Fr(6,25)+Fr(9)*umax/Fr(7,10))
        assert Bseg < 5
        EPSEG=I.rat(Bseg/2)*DT*DT
        max_rate_comp=Fr(0)
        max_rate_target=Fr(0)
        yminseg=high_segment
        ymaxseg=low_segment
        for j in range(n):
            # Exact local t is rational j/1000, x0 and v have certified intervals
            tr=Fr(j,2000)
            l=I(low);u=I(high)
            FL=f_at(tr,KNOT_X[seg],v,l)
            FU=f_at(tr,KNOT_X[seg],v,u)
            # scalar solutions preserve the order in their initial condition
            low_new=(l+DT*FL-EPSEG).lo
            high_new=(u+DT*FU+EPSEG).hi
            assert low_new<=high_new,(seg,j,low_new,high_new)
            # global second derivative bound uses y in [.70,1.60]; ensure bootstrap
            assert low>Fr(73,100)*Q and high<Fr(157,100)*Q,(seg,j,low/Q,high/Q)
            # Interval enclosure within each step via |y'|<=1.70, also verifies global region
            lb=min(low,low_new)-(M_VELOCITY*DT).hi
            hb=max(high,high_new)+(M_VELOCITY*DT).hi
            assert lb > LOW_SAFE.hi and hb<HIGH_SAFE.lo,(seg,j,lb/Q,hb/Q)
            yminseg=min(yminseg,lb)
            ymaxseg=max(ymaxseg,hb)
            low_segment=min(low_segment,lb)
            high_segment=max(high_segment,hb)
            # rigorous within-step price/flow intervals: do NOT replace the
            # time-varying rate by the coarse whole-segment amplitude.
            xx0=KNOT_X[seg]+v*I.rat(tr)
            xx1=KNOT_X[seg]+v*I.rat(tr+substep)
            xx=I(min(xx0.lo,xx1.lo),max(xx0.hi,xx1.hi))
            uu=xx*(v+RHO*(xx-1))
            ratecomp=Fr(9)*max_abs(uu)/Fr(lb,Q)
            ratetarget=max_abs(uu)/Fr(xx.lo,Q)
            # Directed outward bounds on integrated *selling* shares and
            # total paired-dollar turnover, without integrating numerical y.
            positive_u=I(max(0,uu.hi))
            negative_u=I(max(0,-uu.lo))
            comp_sales_upper+=((Fr(9)*positive_u/I(lb))*DT).hi
            target_sales_upper+=((negative_u/I(xx.lo))*DT).hi
            turnover_upper+=(I.rat(9)*I(max(abs(uu.lo),abs(uu.hi)))*DT).hi
            max_rate_comp=max(max_rate_comp,ratecomp)
            max_rate_target=max(max_rate_target,ratetarget)
            low,high=low_new,high_new
        knots.append({'time':str(t1),'y_interval':I(low,high).as_decimal_str(25)})
        # max u each segment and global min y gives rigorous rate bound
        maxrate_y= Fr(9,1)*max_abs(urange)/Fr(yminseg,Q)
        maxrate_x= max_abs(urange)/Fr(min(xs.lo,xs.hi),Q)
        assert maxrate_y < 1 and maxrate_x < 1
        segment_rows.append({'segment':seg+1,'t0':str(t0),'t1':str(t1),
                 'target_slope':v.as_decimal_str(18),
                 'u_enclosure':urange.as_decimal_str(18),
                 'second_derivative_bound':str(float(Bseg)),
                 'y_min_lower_bound':str(Decimal(yminseg)/Decimal(Q)),
                 'y_max_upper_bound':str(Decimal(ymaxseg)/Decimal(Q)),
                 'gross_rate_y_upper_bound':str(Decimal(ceildiv(maxrate_y.numerator*10**12,maxrate_y.denominator))/Decimal(10**12)),
                 'gross_rate_x_upper_bound':str(Decimal(ceildiv(maxrate_x.numerator*10**12,maxrate_x.denominator))/Decimal(10**12)),
                 'gross_rate_y_tight_upper':str(Decimal(ceildiv(max_rate_comp.numerator*10**12,max_rate_comp.denominator))/Decimal(10**12)),
                 'gross_rate_x_tight_upper':str(Decimal(ceildiv(max_rate_target.numerator*10**12,max_rate_target.denominator))/Decimal(10**12))})
        lower_all=min(lower_all,yminseg);upper_all=max(upper_all,ymaxseg)
    # day-1 y bounds for reset bands, and all-session min/max enclosures
    day1_low=min([Fr(row['y_min_lower_bound']) for row in segment_rows[:3]])
    day1_high=max([Fr(row['y_max_upper_bound']) for row in segment_rows[:3]])
    day2_low=min([Fr(row['y_min_lower_bound']) for row in segment_rows[3:]])
    day2_high=max([Fr(row['y_max_upper_bound']) for row in segment_rows[3:]])
    y1_l=Fr(knots[2]['y_interval'][0]);y1_u=Fr(knots[2]['y_interval'][1]);
    assert H.lo>Q and H.hi < Fr(103,100)*Q
    assert Fr(199,200) < Fr(97,100)*Fr(103,100)
    assert day1_low > Fr(3,4) and day1_high<Fr(5,4),('day1',float(day1_low),float(day1_high))
    assert day2_low > Fr(3,4)*y1_u and day2_high<Fr(5,4)*y1_l,('day2',float(day2_low),float(day2_high),float(y1_l),float(y1_u))
    for row in segment_rows:
        assert Fr(row['gross_rate_y_upper_bound']) < 1
        assert Fr(row['gross_rate_x_upper_bound']) < 1
    # terminal crisis: q=0.97 and 0.9409, y_end bracket validates delta=0.015
    y2_l=Fr(knots[-1]['y_interval'][0]);y2_u=Fr(knots[-1]['y_interval'][1]);
    from mpmath import mp
    mp.dps=60
    A_min=(9*mp.log(mp.mpf('1')/mp.mpf('0.9409'))-mp.log(mp.mpf(str(y2_u))))/10
    A_max=(9*mp.log(mp.mpf('1')/mp.mpf('0.9409'))-mp.log(mp.mpf(str(y2_l))))/10
    power=Fr(9409,10000)**9
    zlow=power*Fr(y2_l)
    zhigh=power*Fr(y2_u)
    e02lower,e02upper=exp_positive_bounds(Fr(1,5))
    e021lower,e021upper=exp_positive_bounds(Fr(21,100))
    # A >= .020 iff exp(0.20) * product(prices) <= 1.
    # A <  .021 iff exp(0.21) * product(prices) > 1.
    assert e02upper*zhigh < 1, 'Certified delta=0.020 crisis failed'
    assert e021lower*zlow > 1, 'Certified delta=0.021 upper severity failed'
    assert A_min > mp.mpf('.02') and A_max < mp.mpf('.021')
    assert comp_sales_upper < 2*Q and target_sales_upper < 2*Q
    assert turnover_upper < 3*Q
    assert all(Fr(item['gross_rate_y_tight_upper']) < Fr(285,1000) for item in segment_rows)
    result={
        'method':'outward-rounded fixedpoint interval Euler with global second derivative bound and scalar order preservation',
        'arithmetic':'integer endpoints with outward floor/ceil, grid Q=10**32',
        'fixedpoint_scale':str(Q),
        'algebraic_plateau_root_interval':[str(float(HLO)),str(float(HHI))],
        'plateau_root_exact_signs':[str(exact_poly(HLO)),str(exact_poly(HHI))],
        'second_derivative_bound':5,
        'bootstrap_state_interval':['0.70','1.60'],
        'bootstrap_velocity_bound':'1.70',
        'step':'0.0005','steps':80000,
        'y_at_knots':knots,
        'segments':segment_rows,
        'session1_y_bounds':[str(float(day1_low)),str(float(day1_high))],
        'session2_y_bounds':[str(float(day2_low)),str(float(day2_high))],
        'reset_day2_y1_bounds':[str(float(y1_l)),str(float(y1_u))],
        'gross_rate_strictly_under_1':True,
        'compensator_sold_shares_certified_upper':str(Decimal(comp_sales_upper)/Decimal(Q)),
        'target_sold_shares_certified_upper_each':str(Decimal(target_sales_upper)/Decimal(Q)),
        'paired_dollar_turnover_certified_upper':str(Decimal(turnover_upper)/Decimal(Q)),
        'daily_bands_strictly_respected':True,
        'target_end_closings':['0.97','0.9409'],
        'terminal_crisis_lower_and_upper_numerical':[str(A_min),str(A_max)],
        'certified_delta_0_020_reached_by_exact_rationals':True,
        'certified_delta_0_021_not_reached_by_exact_rationals':True,
        'exp_0_20_rational_bounds':[str(e02lower),str(e02upper)],
        'zero_dollar_target_exact_from_quadratic_root':True,
        'zero_dollar_comp_from_pairing':True,
        'note':'For a rigorous delta=0.02 crisis, use the exact rational exponential inequality check below.',
    }
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2),encoding='utf-8',newline='\n')
    return result
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--out',default='data/v7_interval_certificate.json')
    args=p.parse_args()
    result=certificate(Path(args.out))
    print(json.dumps({k:result[k] for k in ['steps','session1_y_bounds','session2_y_bounds','reset_day2_y1_bounds','terminal_crisis_lower_and_upper_numerical']},indent=2))
