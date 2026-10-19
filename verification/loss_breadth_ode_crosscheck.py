"""Independent SciPy ODE cross-check of the rational interval witnesses.

This module uses floating-point DOP853 and RK45 only as an audit. The
proof-critical directed-integer interval checks live in loss_breadth_certified.py.
Run from repository root:
  python verification/loss_breadth_ode_crosscheck.py
"""
from fractions import Fraction
import math
from scipy.integrate import solve_ivp
from loss_breadth_certified import cases,schedule,verify

def audit(spec):
    result=verify(spec)
    k=spec["k"];m=10-k;ratio=k/m
    state=[1.,1.,0.,0.];first=None
    turnover=0.;max_rate=0.;min_band=100.
    for a,b,q in schedule(spec["windows"]):
        left,right,dollar=map(float,(a,b,q))
        if abs(left-20)<1e-12:first=state[:2]
        ref=[1.,1.] if right<=20 else first
        assert ref is not None
        def f(t,z):
            x,y,shx,shy=z
            return (-.4*(x-1)+dollar/x,
                    -.4*(y-1)-ratio*dollar/y,
                    max(-dollar/x,0.),max(ratio*dollar/y,0.))
        opts=dict(rtol=2e-12,atol=2e-14,max_step=.06)
        sol=solve_ivp(f,(left,right),state,method="DOP853",dense_output=True,**opts)
        chk=solve_ivp(f,(left,right),state,method="RK45",**opts)
        assert sol.success and chk.success,(spec["case"],sol.message,chk.message)
        assert max(abs(sol.y[i,-1]-chk.y[i,-1]) for i in range(2))<2e-9
        for j in range(121):
            xx,yy=sol.sol(left+(right-left)*j/120.)[:2]
            for i,s in enumerate((xx,yy)):
                min_band=min(min_band,s-.75*ref[i],1.25*ref[i]-s)
                assert .75*ref[i]<s<1.25*ref[i]
            if dollar:
                max_rate=max(max_rate,abs(dollar)/xx,abs(ratio*dollar)/yy)
        state=[float(sol.y[i,-1]) for i in range(4)]
        turnover+=k*abs(dollar)*(right-left)
    x,y=state[:2]
    assert result["terminal_target_interval"][0] and result["terminal_compensator_interval"][0]
    for val,field in ((x,"terminal_target_interval"),(y,"terminal_compensator_interval")):
        a,b=map(float,result[field])
        assert a-1e-11<=val<=b+1e-11,(spec["case"],field,val,a,b)
    assert abs(turnover-result["paired_turnover"])<1e-9
    assert min_band>0 and max_rate<.285 and max(state[2:])<2
    assert x<float(spec["target"])
    geometric=1-math.exp((k*math.log(x)+m*math.log(y))/10)
    assert geometric>float(1-spec["index"])
    print(spec["case"],"PASS",f"target loss={100*(1-x):.4f}%",
          f"index={100*geometric:.4f}%",
          f"turnover={turnover:.6f}",f"max-step rate={max_rate:.6f}")

if __name__=="__main__":
    for case in cases():audit(case)
    print("PASS six cases independently checked by DOP853 and RK45")
