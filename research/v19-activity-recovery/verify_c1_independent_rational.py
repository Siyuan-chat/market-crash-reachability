#!/usr/bin/env python3
"""Independent exact-grid rational interval certification of V19 Construction III.

No mpmath, numpy or scipy. All arithmetic rounds outward to 10^-65.
log and atan are evaluated by convergent rational series with explicit tails.
Run with normal Python assertions enabled (never python -O).
"""
if not __debug__: raise RuntimeError("assertions required")
from fractions import Fraction as F
from math import isqrt
import json

S=10**65
NT=42
def ceil(a,b): return -((-a)//b)
class I:
    __slots__=("lo","hi")
    def __init__(self,a,b=None):
        if isinstance(a,I) and b is None: self.lo,self.hi=a.lo,a.hi;return
        if b is None:b=a
        a,b=F(a),F(b)
        self.lo=a.numerator*S//a.denominator
        self.hi=ceil(b.numerator*S,b.denominator)
        assert self.lo<=self.hi
    @classmethod
    def raw(cls,a,b):
        z=cls.__new__(cls);z.lo,z.hi=a,b;assert a<=b;return z
    def __add__(self,b):
        b=I(b);return I.raw(self.lo+b.lo,self.hi+b.hi)
    __radd__=__add__
    def __neg__(self):return I.raw(-self.hi,-self.lo)
    def __sub__(self,b):return self+-I(b)
    def __rsub__(self,b):return I(b)+-self
    def __mul__(self,b):
        b=I(b);q=[x*y for x in (self.lo,self.hi) for y in (b.lo,b.hi)]
        return I.raw(min(q)//S,ceil(max(q),S))
    __rmul__=__mul__
    def __truediv__(self,b):
        b=I(b);assert b.lo>0 or b.hi<0
        if b.hi<0:return (-self)/(-b)
        q=[(a*S,v) for a in (self.lo,self.hi) for v in (b.lo,b.hi)]
        return I.raw(min(a//v for a,v in q),max(ceil(a,v) for a,v in q))
    def __rtruediv__(self,b):return I(b)/self
    def sq(self):
        if self.lo>=0:return I.raw(self.lo*self.lo//S,ceil(self.hi*self.hi,S))
        if self.hi<=0:return I.raw(self.hi*self.hi//S,ceil(self.lo*self.lo,S))
        return I.raw(0,ceil(max(self.lo*self.lo,self.hi*self.hi),S))
    def lower(self):return F(self.lo,S)
    def upper(self):return F(self.hi,S)
    def below(self,b):return self.hi<I(b).lo
    def above(self,b):return self.lo>I(b).hi
    def inside(self,a,b):return self.lo>=I(a).lo and self.hi<=I(b).hi
    def __repr__(self):return f"[{float(self.lower()):.17g},{float(self.upper()):.17g}]"

def tail(r,n,scale):
    assert 0<=r<=F(1,2)
    return F(scale)*r**(2*n+1)/(F(2*n+1)*(1-r*r))
def rbound(t):
    r=max(abs(t.lower()),abs(t.upper()))
    return F(7,20) if r<=F(7,20) else r
def logseries(t):
    r=rbound(t); assert r<=F(1,2)
    a=I(0);power=t;two=t.sq()
    for j in range(NT):
        a=a+power/F(2*j+1)
        power=power*two
    rem=tail(r,NT,2)
    return 2*a+I(-rem,rem)
LOG2=logseries(I(F(1,3)))
def ln(z):
    z=I(z);assert z.lo>0
    k=0;y=z
    while y.hi>I(2).hi:y=y/2;k+=1
    while y.lo<I(1).lo:y=y*2;k-=1
    assert y.lo>=I(1).lo and y.hi<=I(2).hi
    return logseries((y-1)/(y+1))+k*LOG2
def atan_small(t):
    r=rbound(t);assert r<=F(1,2)
    a=I(0);power=I(t);two=t.sq()
    for j in range(NT):
        term=power/F(2*j+1)
        a=a+term if j%2==0 else a-term
        power=power*two
    rem=tail(r,NT,1)
    return a+I(-rem,rem)
PI4=4*atan_small(I(F(1,5)))-atan_small(I(F(1,239)))
def atanpos(t):
    t=I(t);assert t.lo>=0
    return atan_small(t) if t.hi<I(F(1,2)).lo else PI4+atan_small((t-1)/(t+1))
q=isqrt(3*S*S)
SQRT3=I.raw(q,q+1)
def prim(x,sgn):
    v=I(x)-I(F(1,2))
    if sgn==1:
        t=2*v/SQRT3
        assert t.lo>=0 and t.hi<I(1).lo
        return -ln(I(F(3,2))-2*v.sq())/4+(ln(1+t)-ln(1-t))/(4*SQRT3)
    assert sgn==-1
    return ln(2*v.sq()+I(F(1,2)))/4+atanpos(2*v)/2
def inverse(target,sgn):
    target=I(target)
    lo0=F("0.5");hi0=F("1.34")
    assert prim(I(lo0),sgn).below(target)
    assert prim(I(hi0),sgn).above(target)
    brackets=[]
    for point in (I.raw(target.lo,target.lo),I.raw(target.hi,target.hi)):
        lo,hi=lo0,hi0
        for _ in range(82):
            mid=(lo+hi)/2;v=prim(I(mid),sgn)
            if v.below(point):lo=mid
            elif v.above(point):hi=mid
            else:break
        assert prim(I(lo),sgn).below(point) and prim(I(hi),sgn).above(point)
        brackets.append((lo,hi))
    return I(brackets[0][0],brackets[1][1])
def edge(x,y,sgn,forced_x=None,forced_y=None):
    x=I(x);y=I(y)
    if sgn==1 and forced_y is not None:
        yy=I(forced_y);z=prim(y,-1)-prim(yy,-1)
        xx=inverse(prim(x,+1)+z,+1)
    elif sgn==-1 and forced_x is not None:
        xx=I(forced_x);z=prim(x,-1)-prim(xx,-1)
        yy=inverse(prim(y,+1)+z,+1)
    else:raise AssertionError("unsupported event")
    assert z.lo>0
    return xx,yy,z
LOWS=["1.085409","1.087707","1.085158","1.099042","1.106127","1.122661","1.14","1.15"]
CLEFT="0.76065368494358";CRIGHT="0.76065368494359"
Z=I(F("0.04"))
def simulate(c):
    x=y=I(1);xs=[x];ys=[y];zs=[];signs=[]
    for low in LOWS:
        x,y,z=edge(x,y,+1,forced_y=c)
        xs.append(x);ys.append(y);zs.append(z);signs.append(+1)
        x,y,z=edge(x,y,-1,forced_x=low)
        xs.append(x);ys.append(y);zs.append(z);signs.append(-1)
    x,y,z=edge(x,y,+1,forced_y=c)
    xs.append(x);ys.append(y);zs.append(z);signs.append(+1)
    x,y,z=edge(x,y,-1,forced_x=F(3,4))
    xs.append(x);ys.append(y);zs.append(z);signs.append(-1)
    cut=len(zs)
    x,y,z=edge(x,y,-1,forced_x=F(9,16))
    xs.append(x);ys.append(y);zs.append(z);signs.append(-1)
    return dict(xs=xs,ys=ys,zs=zs,cut=cut,
        ledger=sum((s*z for s,z in zip(signs,zs)),I(0)),
        amount=sum(zs,I(0)),a1=sum(zs[:cut],I(0)),a2=sum(zs[cut:],I(0)))
def verify():
    left=simulate(I(CLEFT));right=simulate(I(CRIGHT))
    assert left["ledger"].lo>0 and right["ledger"].hi<0
    p=simulate(I(CLEFT,CRIGHT))
    assert len(p["zs"])==19 and p["cut"]==18
    for x in p["xs"][:19]+p["ys"][:19]:assert x.inside(F(3,4),F(5,4))
    close=p["ys"][18]
    for x in p["xs"][18:]:assert x.inside(F(9,16),F(15,16))
    for x in p["ys"][18:]:
        assert x.lo>(I(F(3,4))*close).hi and x.hi<(I(F(5,4))*close).lo
    prices=[p["ys"][-1]]*5
    for i in range(5):
        j=(i+1)%5
        target=inverse(prim(prices[i],-1)-Z,-1)
        xx,yy,amount=edge(prices[i],prices[j],-1,forced_x=target)
        prices[i],prices[j]=xx,yy
        assert amount.lo<=Z.lo and amount.hi>=Z.hi
        for x in prices:
            assert x.inside(F("1.2"),F("1.30"))
            assert x.lo>(I(F(3,4))*close).hi and x.hi<(I(F(5,4))*close).lo
    for x in prices:assert x.inside(F("1.2"),F("1.23"))
    M=5*p["amount"]+5*Z
    Htarget=p["amount"]/2/I(F(9,16))
    Hcomp=p["amount"]/2/I(CLEFT)+Z/I(F("1.2"))
    rate1=p["a1"]/20/I(F(3,4))
    rate2=(p["a2"]+5*Z)/20/I(F(9,16))
    assert M.hi<I(F("11.261627")).lo
    assert Htarget.hi<I(2).lo and Hcomp.hi<I(2).lo
    assert max(rate1.hi,rate2.hi)<I(F("0.133")).lo
    assert F(9,16)*F("1.23")<F("0.84")**2
    certificate = {
        "status": "INTERNAL_INTERVAL_CROSSCHECK_2",
        "method": "outward rational grid 1e-65, analytic series remainders",
        "parameters": {"N": 10, "p": 0, "K": 2,
                       "root_left": CLEFT, "root_right": CRIGHT,
                       "events_per_pair": 19, "compensator_cycles": 5},
        "left_ledger": [str(left["ledger"].lower()), str(left["ledger"].upper())],
        "right_ledger": [str(right["ledger"].lower()), str(right["ledger"].upper())],
        "edge_amounts": [[str(z.lower()), str(z.upper())] for z in p["zs"]],
        "target_prices_at_endpoints": [[str(x.lower()), str(x.upper())] for x in p["xs"]],
        "compensator_prices_at_endpoints": [[str(x.lower()), str(x.upper())] for x in p["ys"]],
        "compensator_final_prices": [[str(x.lower()), str(x.upper())] for x in prices],
        "day1_amount": [str(p["a1"].lower()), str(p["a1"].upper())],
        "day2_amount": [str(p["a2"].lower()), str(p["a2"].upper())],
        "total_amount": [str(M.lower()), str(M.upper())],
        "gross_share_rate_upper": str(F(max(rate1.hi, rate2.hi), S)),
        "target_inventory_upper": str(Htarget.upper()),
        "compensator_inventory_upper": str(Hcomp.upper()),
        "limits": {"turnover_lt": "11.261627", "gross_rate_lt": "0.133",
                   "inventory_lt": "2", "final_compensator_lt": "1.23"}
    }
    with open("research/v19-activity-recovery/independent_c1_certificate.json", "w", encoding="utf-8") as fp:
        json.dump(certificate, fp, sort_keys=True, indent=2)
    print("PASS independently certified 19 event pairs, 5 cycles, full bounds")
    print("left ledger",left["ledger"],"right ledger",right["ledger"])
    print("M",M,"max gross share rate",I.raw(0,max(rate1.hi,rate2.hi)))
    print("final compensator prices",prices)
    return True
if __name__=="__main__": verify()
