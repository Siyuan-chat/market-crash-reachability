"""Exact-rational / outward-integer certificate for five repeated 25% lower closes.

N=10, k=m=5, F=eta=1, rho=2/5, sessions [0,20] and [20,40].
Each target follows piecewise-linear x, with u=x*(x'+rho*(x-1)).
Each compensator follows y'=-rho*(y-1)-u/y; y(0)=1.
A unique quadratic root closes all individual executed-dollar ledgers.
No numpy/scipy in the proof-critical checker. Disable Python -O.
"""
if not __debug__:
    raise RuntimeError("Disabled assertions invalidate certificate")

from fractions import Fraction as Fr
from decimal import Decimal, getcontext
from pathlib import Path
import json, argparse

getcontext().prec=60
Q=10**28
RHO=Fr(2,5); K=5
UP=Fr(5,4); DOWN=Fr(3,4); DT=Fr(1,2000)
HLOW=Fr("1.15451858960596"); HHIGH=Fr("1.15451858960597")
H2=Fr(187,200)
T=[Fr(0),Fr(5,2),Fr(35,2),Fr(20),Fr(24),Fr(36),Fr(40)]
X1=Fr(3,4);X2=Fr(9,16)
MINY=Fr(7,10);MAXY=Fr(31,20)

class I:
    __slots__=("lo","hi")
    def __init__(self,lo,hi=None):
        self.lo=int(lo);self.hi=int(lo if hi is None else hi)
        assert self.lo<=self.hi
    @staticmethod
    def rat(x):
        x=Fr(x)
        return I(x.numerator*Q//x.denominator,-((-x.numerator*Q)//x.denominator))
    @staticmethod
    def bounds(a,b):
        return I(I.rat(a).lo,I.rat(b).hi)
    def __add__(self,other):
        other=interval(other)
        return I(self.lo+other.lo,self.hi+other.hi)
    __radd__=__add__
    def __neg__(self):
        return I(-self.hi,-self.lo)
    def __sub__(self,other):
        return self+-interval(other)
    def __rsub__(self,other):
        return interval(other)+-self
    def __mul__(self,other):
        other=interval(other)
        z=(self.lo*other.lo,self.lo*other.hi,self.hi*other.lo,self.hi*other.hi)
        return I(min(z)//Q,-((-max(z))//Q))
    __rmul__=__mul__
    def inverse(self):
        assert self.lo>0
        return I(Q*Q//self.hi,-((-Q*Q)//self.lo))
    def __truediv__(self,other):
        return self*interval(other).inverse()
    def __rtruediv__(self,other):
        return interval(other)*self.inverse()
    def decimals(self):
        return [str(Decimal(self.lo)/Decimal(Q)),str(Decimal(self.hi)/Decimal(Q))]

def interval(x):
    return x if isinstance(x,I) else I.rat(x)
def absmax(i):
    return max(abs(i.lo),abs(i.hi))
def linear_integral(a,b,length):
    return length*((a*a+a*b+b*b)/3-(a+b)/2)
def target_ledger(h):
    xs=[Fr(1),h,h,X1,H2,H2,X2]
    integral=sum(linear_integral(a,b,t1-t0)
                 for a,b,t0,t1 in zip(xs[:-1],xs[1:],T[:-1],T[1:]))
    return (X2*X2-1)/2+RHO*integral

def isolate_root():
    a=(target_ledger(Fr(2))-2*target_ledger(Fr(1))+target_ledger(Fr(0)))/2
    b=target_ledger(Fr(1))-a-target_ledger(Fr(0))
    c=target_ledger(Fr(0))
    assert (a,b,c)==(Fr(20,3),-Fr(77,12),-Fr(2364683,1600000))
    assert target_ledger(HLOW)<0<target_ledger(HHIGH)
    assert 2*a*HLOW+b>0
    return {"polynomial":"32000000*h^2-30800000*h-7094049=0",
            "root_bracket":[str(HLOW),str(HHIGH)],
            "exact_target_ledger_zero":True}

H=I.bounds(HLOW,HHIGH)
XS=[I.rat(1),H,H,I.rat(X1),I.rat(H2),I.rat(H2),I.rat(X2)]

def ode_f(t,x0,slope,y):
    x=x0+slope*I.rat(t)
    u=x*(slope+interval(RHO)*(x-1))
    return -interval(RHO)*(y-1)-u/y

def verify_path():
    low=Q; high=Q
    endpoint_rows=[]; segment_rows=[]
    s1lo=[];s1hi=[];s2lo=[];s2hi=[]
    Htarget=0;Hcomp=0;turnover=0;maxrate=Fr(0);steps=0
    close20=None
    for seg,(t0,t1) in enumerate(zip(T[:-1],T[1:])):
        length=t1-t0
        slope=(XS[seg+1]-XS[seg])/interval(length)
        x0=XS[seg]
        xrange=I(min(XS[seg].lo,XS[seg+1].lo),max(XS[seg].hi,XS[seg+1].hi))
        urange=xrange*(slope+interval(RHO)*(xrange-1))
        uprime=slope*(slope+interval(RHO)*(2*xrange-1))
        umax=Fr(absmax(urange),Q)
        upmax=Fr(absmax(uprime),Q)
        maxf=RHO*Fr(11,20)+umax/MINY
        maxfy=RHO+umax/MINY**2
        second=upmax/MINY+maxfy*maxf
        assert second<2,(seg,second)
        assert maxf<1 and 1-DT*maxfy>0
        # Taylor error |y''|*(DT^2)/2 <= DT^2, outward.
        eps=I.rat(DT*DT)
        n=length/DT
        assert n.denominator==1
        n=int(n);steps+=n
        seglo=low; seghi=high
        for step in range(n):
            assert Fr(low,Q)>MINY and Fr(high,Q)<MAXY,(seg,step,"bootstrap")
            tlocal=step*DT
            ylo=I(low);yhi=I(high)
            FL=ode_f(tlocal,x0,slope,ylo)
            FU=ode_f(tlocal,x0,slope,yhi)
            ln=(ylo+interval(DT)*FL-eps).lo
            hn=(yhi+interval(DT)*FU+eps).hi
            assert ln<=hn
            # The Euler map z->z+DT*f(t,z) is increasing by
            # 1-DT*(rho+|u|/MINY^2)>0.
            # Within-step |y'|<1 yields another safe enclosure.
            ybl=min(low,ln)-interval(DT).hi
            ybu=max(high,hn)+interval(DT).hi
            assert Fr(ybl,Q)>MINY and Fr(ybu,Q)<MAXY,(seg,step,"within step")
            seglo=min(seglo,ybl);seghi=max(seghi,ybu)
            xa=x0+slope*interval(tlocal)
            xb=x0+slope*interval(tlocal+DT)
            xx=I(min(xa.lo,xb.lo),max(xa.hi,xb.hi))
            uu=xx*(slope+interval(RHO)*(xx-1))
            assert xx.lo>0 and ybl>0
            maxrate=max(maxrate,Fr(absmax(uu),xx.lo),Fr(absmax(uu),ybl))
            dt=interval(DT)
            Htarget+=(I(max(0,-uu.lo))/I(xx.lo)*dt).hi
            Hcomp+=(I(max(0,uu.hi))/I(ybl)*dt).hi
            turnover+=(interval(K)*I(absmax(uu))*dt).hi
            low,high=ln,hn
        if t1<=20:
            s1lo.append(seglo);s1hi.append(seghi)
        else:
            s2lo.append(seglo);s2hi.append(seghi)
        if t1==20: close20=I(low,high)
        endpoint_rows.append({"time":str(t1),"y_interval":I(low,high).decimals()})
        segment_rows.append({"interval":[str(t0),str(t1)],
                             "y_intrasegment":[str(Decimal(seglo)/Decimal(Q)),
                                               str(Decimal(seghi)/Decimal(Q))],
                             "second_derivative_bound":str(Decimal(second.numerator)/Decimal(second.denominator))})
    assert close20 is not None
    a=min(s1lo);b=max(s1hi);c=min(s2lo);d=max(s2hi)
    assert a>interval(DOWN).hi and b<interval(UP).lo
    assert c>(interval(DOWN)*close20).hi
    assert d<(interval(UP)*close20).lo
    assert maxrate<Fr(285,1000),maxrate
    assert Htarget<2*Q and Hcomp<2*Q
    assert turnover<14*Q
    end=I(low,high)
    assert interval(X2).hi*end.hi < interval(Fr(21,25)**2).lo*Q
    return {"target_closes":[str(X1),str(X2)],
            "day1_compensator_end":close20.decimals(),
            "day2_compensator_end":end.decimals(),
            "compensator_first_session_enclosure":[str(Decimal(a)/Decimal(Q)),str(Decimal(b)/Decimal(Q))],
            "compensator_second_session_enclosure":[str(Decimal(c)/Decimal(Q)),str(Decimal(d)/Decimal(Q))],
            "gross_rate_upper":str(Decimal(maxrate.numerator)/Decimal(maxrate.denominator)),
            "shares_sold_per_target_upper":str(Decimal(Htarget)/Decimal(Q)),
            "shares_sold_per_compensator_upper":str(Decimal(Hcomp)/Decimal(Q)),
            "paired_dollar_turnover_upper":str(Decimal(turnover)/Decimal(Q)),
            "geometric_index_terminal_ratio_strict_upper":"21/25",
            "systemic_C_0p5_strict_lower":"-log(21/25)",
            "fixedpoint_scale":"10**28","time_step":"1/2000","time_steps":steps,
            "enclosure_method":"directed fixed-point interval Euler with second-derivative remainder and verified order of scalar Euler map",
            "endpoint_rows":endpoint_rows,"segments":segment_rows}

def coverage_obstruction():
    # Independent necessary bound, NOT a certificate of optimum coverage.
    assert Fr(44800,5915)==Fr(1280,169)
    for k in range(1,11):
        required=k*(1-X2**2)/(2*RHO)
        admissible_upper=20*(Fr(35-3*k,16)-Fr(15*k,256))
        assert (required<=admissible_upper)==(k<=7)
    return {"necessary_maximum_k":7,"constraint":"1183*k <= 8960",
            "six_or_seven_attainability":"unresolved"}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--out",default=None)
    args=p.parse_args()
    result={
        "model":"N=10, five target and five compensator assets, F=eta=1, rho=2/5, sessions 0-20 and 20-40, uniform rolling +/-25% bands",
        "target_knots":[{"t":str(t),"x":("[h root]" if i in (1,2) else str([Fr(1),Fr(0),Fr(0),X1,H2,H2,X2][i]))} for i,t in enumerate(T)],
        "root":isolate_root(),"coverage_obstruction":coverage_obstruction(),
        "certificate":verify_path(),
        "ledger_identity":"Each target ledger is EXACTLY zero by polynomial root; each paired compensator ledger is the negative of its target.",
        "evidence_status":"Internally authored outward-rounded certification; no external implementation audit"
    }
    c=result["certificate"]
    assert c["time_steps"]==80000
    print("PASS EXACT five-target 25%-then-25% lower-limit construction")
    print("PASS two-session bands, continuous pairing, exact ledger closure")
    print("PASS rate <0.285, initial shares 2 each, paired turnover <14")
    print("PASS geometric-index loss >16%, necessary coverage k<=7")
    print("PASS",c["time_steps"],"integer outward-rounded ODE steps")
    print("y(20):",c["day1_compensator_end"])
    print("y(40):",c["day2_compensator_end"])
    if args.out:
        Path(args.out).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
        print("WROTE",args.out)

if __name__=="__main__":
    main()
