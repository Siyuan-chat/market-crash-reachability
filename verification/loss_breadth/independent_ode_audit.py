"""Floating-point cross-check for exact dollar schedules (not an interval proof).

Requires scipy. Uses two different high-accuracy ODE algorithms, checks all
segment endpoint values against the certified rational enclosures and verifies
dollar-ledger closure and execution budgets independently of interval rounding.
"""
import json,math
from fractions import Fraction as F
from pathlib import Path
from scipy.integrate import solve_ivp
from certify_loss_breadth import phase3_cases,phase4_cases

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
DATA=ROOT/"build/loss_breadth/certificates.json"

def main():
    results={x['case']:x for x in json.loads(DATA.read_text())}
    cases=phase3_cases()+phase4_cases((HERE/"phase4_schedules.b64").read_text())
    for case in cases:
        k=case['k'];m=10-k;ratio=k/m
        x=y=1.
        previous=(x,y)
        market0=market1=0.
        for (a,b,q),expected in zip(case['parts'],results[case['id']]['history']):
            t0=float(a);t1=float(b);r=float(q)
            def flow(t,z):
                px,py=z
                return [-.4*(px-1)+r/px,-.4*(py-1)-ratio*r/py]
            high=solve_ivp(flow,(t0,t1),(x,y),method='DOP853',
                           rtol=5e-13,atol=2e-14,max_step=.08)
            independent=solve_ivp(flow,(t0,t1),(x,y),method='Radau',
                                  rtol=2e-12,atol=2e-13,max_step=.14)
            assert high.success and independent.success,(case['id'],t0,t1)
            px,py=high.y[:,-1]
            assert max(abs(px-independent.y[0,-1]),abs(py-independent.y[1,-1]))<3e-8
            for v,box in ((px,expected[1]),(py,expected[2])):
                a,b=map(lambda z:float(F(z)),box)
                assert a-5e-12<v<b+5e-12,(case['id'],t1,v,a,b)
            x,y=px,py
            market0+=r*(t1-t0)
            market1+=-ratio*r*(t1-t0)
        assert abs(market0)<1e-10 and abs(market1)<1e-10
        assert x<1-float(case['drop'])
        if case['full']:assert y<1-float(case['drop'])
        mloss=-(k*math.log(x)+m*math.log(y))/10
        assert 1-math.exp(-mloss)>float(case['index'])
        print("INDEPENDENT PASS",case['id'],"x",round(x,9),"y",round(y,9),
              "mean-log",round(mloss,7))
    print("PASS: 12 independent SciPy DOP853/Radau integration comparisons")

if __name__=="__main__":
    main()
