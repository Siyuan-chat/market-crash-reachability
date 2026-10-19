"""Reproduce the Phase-3 constant-impact loss/breadth witnesses with rational interval bounds.

F=eta=1, rho=2/5, T=40, two 20-unit sessions, uniform reset +/-25% bands.
Every exact rational target-group dollar input q is offset by -k/(10-k)*q.
The comparisons are internal computer-assisted interval certificates,
not independently peer-reviewed or claims of optimality.
"""
from fractions import Fraction as R
from math import ceil
import argparse,json,hashlib,pathlib

Q=10**24
RHO=R(2,5)
BAND=R(1,4)
V=R(285,1000)
MINP=R(3,5);MAXP=R(8,5)
QBOUND=R(28,100)
FB=R(71,100);FPB=R(118,100);SBOUND=R(1)
DT=R(1,4000)
assert FB >= RHO*(MAXP-1)+QBOUND/MINP
assert FPB >= RHO+QBOUND/(MINP*MINP)
assert FB*FPB < SBOUND

def ceil_div(a,b): return -((-a)//b)
def lo(f):return f.numerator*Q//f.denominator
def hi(f):return ceil_div(f.numerator*Q,f.denominator)
def dec(v):return f"{float(R(v,Q)):.12f}"

def step(v,h,q):
    low,high=v
    rem=hi(SBOUND*h*h/2)
    def inc(z,upper):
        a=-2*h.numerator*(z-Q);b=5*h.denominator
        c=h.numerator*q.numerator*Q*Q
        d=h.denominator*q.denominator*z
        return (ceil_div(a,b)+ceil_div(c,d)) if upper else (a//b+c//d)
    return low+inc(low,False)-rem,high+inc(high,True)+rem

def flow(v,duration,q):
    assert abs(q)<=QBOUND
    count=ceil(duration/DT)
    if not count:return v,0
    h=duration/count
    margin=hi(FB*h)
    lower=hi(MINP)+margin
    upper=lo(MAXP)-margin
    for j in range(count):
        assert v[0]>=lower and v[1]<=upper,("bootstrap",j,v)
        v=step(v,h,q)
        assert v[0]>=lower and v[1]<=upper,("bootstrap after step",j,v)
    return v,count

def cases():
    C=R;out=[]
    for k,mass,a,b,case,limit,index in [
      (5,".26","2.0","1.55","P50-20",".7771",".96"),
      (6,".24","3.5","1.4","P60-20",".7910",".95"),
      (7,".19","5.5","2.7","P70-10",".8740",".97")]:
        mass=C(mass);a=C(a);b=C(b)
        out.append(dict(case=case,k=k,cap=C(3),target=C(limit),index=C(index),
          windows=[(C(0),a,mass/a),(C(40)-b,C(40),-mass/b)]))
    for case,k,a,z,w1,w2,w3,g1,cap,target,index in [
      ("R80-10",8,".020005576338",".158140461748",".401289730597","11.552628595060","2.358357669804",".004457191867",3,".892",".97"),
      ("R70-20-M5",7,".036616",".291916",".5179","12.9713","2.6763",".0115",5,".798",".94"),
      ("R70-15.5",7,".013956473042",".195977071642",".222524383211","6.090944893906","1.650596722494",".074442494954",3,".845",".96")]:
        a,z,w1,w2,w3,g1=map(C,(a,z,w1,w2,w3,g1))
        out.append(dict(case=case,k=k,cap=C(cap),target=C(target),index=C(index),
          windows=[(C(20)-w1,C(20),-a/w1),
                   (C(20)+g1,C(20)+g1+w2,(a+z)/w2),
                   (C(40)-w3,C(40),-z/w3)]))
    return out

def schedule(windows):
    prior=R(0);out=[]
    for a,b,q in windows:
        assert prior<=a<b<=40
        if a>prior:out.append((prior,a,R(0)))
        out.append((a,b,q));prior=b
    if prior<40:out.append((prior,R(40),R(0)))
    result=[]
    for a,b,q in out:
        if a<20<b:result.extend(((a,R(20),q),(R(20),b,q)))
        else:result.append((a,b,q))
    assert sum((b-a)*q for a,b,q in result)==0
    assert all(result[i][1]==result[i+1][0] for i in range(len(result)-1))
    return result

def verify(spec):
    k=spec["k"];m=10-k
    ratio=R(k,m)
    state=[(Q,Q),(Q,Q)]
    reference=[(R(1),R(1)),(R(1),R(1))]
    turnover=R(0);rate=R(0);sold=[R(0),R(0)]
    bandmargin=R(9);steps=0;records=[]
    sch=schedule(spec["windows"])
    for a,b,q in sch:
        if a==20:
            reference=[(R(v[0],Q),R(v[1],Q)) for v in state]
        next_state=[]
        for i,dollar in enumerate((q,-ratio*q)):
            prev=state[i]
            nxt,n=flow(prev,b-a,dollar)
            steps+=n;next_state.append(nxt)
            pmin=R(min(prev[0],nxt[0]),Q)
            pmax=R(max(prev[1],nxt[1]),Q)
            reflo,refhi=reference[i]
            bandmargin=min(bandmargin,pmin-R(3,4)*refhi,R(5,4)*reflo-pmax)
            assert bandmargin>0,(spec["case"],"price band",i,float(bandmargin))
            if dollar:
                rate=max(rate,abs(dollar)/pmin)
                if dollar<0:sold[i]+=-dollar*(b-a)/pmin
        turnover+=k*abs(q)*(b-a)
        state=next_state
        records.append(dict(start=str(a),end=str(b),target_dollar_rate=str(q),
            compensator_dollar_rate=str(-ratio*q),
            target=[dec(x) for x in state[0]],
            compensator=[dec(x) for x in state[1]]))
    assert rate<V and turnover<spec["cap"] and max(sold)<R(2)
    x,y=state
    assert R(x[1],Q)<spec["target"]
    assert x[1]<y[0]
    # Exact, non-logarithmic geometric-index certificate.
    assert R(x[1],Q)**k*R(y[1],Q)**m < spec["index"]**10
    return dict(case=spec["case"],k=k,N=10,coverage=f"{k}/10",
        target_loss_guaranteed_strictly_over=float(1-spec["target"]),
        index_price_loss_guaranteed_strictly_over=float(1-spec["index"]),
        terminal_target_interval=[dec(z) for z in x],
        terminal_compensator_interval=[dec(z) for z in y],
        paired_turnover=float(turnover),budget=float(spec["cap"]),
        gross_rate_rigorous_upper=float(rate),gross_shares_sold_upper=list(map(float,sold)),
        price_band_margin_rigorous_lower=float(bandmargin),
        scalar_interval_steps=steps,ledger_exact_zero=True,
        segments=records,acceptance="internal integer outward-rounded interval PASS")

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--out",default=None)
    args=parser.parse_args()
    verified=[verify(c) for c in cases()]
    for c in verified:
        print(c["case"],"PASS k",c["k"],"price loss >",c["target_loss_guaranteed_strictly_over"],
             "M",c["paired_turnover"],"gross rate <",c["gross_rate_rigorous_upper"])
    result=dict(model="constant impact F=eta=1, rho=0.4, 2 x 20, +/-25% reset band",
                validator="integer outward-rounded scalar ODE enclosure, Q=10^24; unaudited proof code",
                cases=verified)
    if args.out:pathlib.Path(args.out).write_text(json.dumps(result,indent=2)+"\n")
    print("PASS",len(verified),"interval witnesses")

if __name__=="__main__":main()
