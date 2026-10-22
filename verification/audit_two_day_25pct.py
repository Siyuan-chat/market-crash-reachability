"""Independent numerical audit of the exact five-target two-day path.

A pure-Python fourth-order Runge--Kutta integrator; this is not itself a
proof. The separate outward-rounded interval checker establishes the bounds.
"""
from pathlib import Path
import math,json,argparse

def audit(dt_max=1/4000):
    A=32000000.;B=-30800000.;C=-7094049.
    h=(-B+math.sqrt(B*B-4*A*C))/(2*A)
    times=(0.,2.5,17.5,20.,24.,36.,40.)
    xs=(1.,h,h,.75,.935,.935,.5625)
    y=1.;lx=0.;ly=0.;Ht=0.;Hc=0.;M=0.
    day1_min=1.;day1_max=1.;day2_min=10.;day2_max=0.
    maxrate=0.;records=[]
    for seg in range(6):
        a,b=times[seg],times[seg+1]
        duration=b-a;v=(xs[seg+1]-xs[seg])/duration
        n=math.ceil(duration/dt_max)
        dt=duration/n
        def f(t,Y):
            x=xs[seg]+v*(t-a)
            u=x*(v+.4*(x-1))
            yy=Y[0]
            return (-.4*(yy-1)-u/yy,u,-u,
                    max(-u,0)/x,max(u,0)/yy,5*abs(u))
        z=[y,lx,ly,Ht,Hc,M]
        for j in range(n):
            t=a+j*dt
            k1=f(t,z)
            k2=f(t+dt/2,[p+dt*q/2 for p,q in zip(z,k1)])
            k3=f(t+dt/2,[p+dt*q/2 for p,q in zip(z,k2)])
            k4=f(t+dt,[p+dt*q for p,q in zip(z,k3)])
            z=[p+dt*(q+2*r+2*s+w)/6
               for p,q,r,s,w in zip(z,k1,k2,k3,k4)]
            yy=z[0]
            assert yy>0
            if seg<3:
                day1_min=min(day1_min,yy);day1_max=max(day1_max,yy)
            else:
                day2_min=min(day2_min,yy);day2_max=max(day2_max,yy)
            x=xs[seg]+v*(t-a)
            u=x*(v+.4*(x-1))
            maxrate=max(maxrate,abs(u)/min(x,yy))
        y,lx,ly,Ht,Hc,M=z
        if seg==2:y20=y
        records.append({"time":b,"target":xs[seg+1],"compensator":y})
    index=math.sqrt(xs[-1]*y)
    assert abs(lx)<1e-9 and abs(ly)<1e-9
    assert .75<day1_min<=day1_max<1.25
    assert .75*y20<day2_min<=day2_max<1.25*y20
    assert maxrate<.285 and max(Ht,Hc)<2 and M<14 and index<.84
    return {
      "h":h,"target_closes":[.75,.5625],
      "compensator_closes":[y20,y],
      "terminal_dollar_residuals":[lx,ly],
      "y_day1":[day1_min,day1_max],"y_day2":[day2_min,day2_max],
      "gross_share_rate":maxrate,
      "shares_sold_per_target":Ht,"shares_sold_per_compensator":Hc,
      "paired_dollar_turnover":M,
      "geometric_index_ratio":index,
      "geometric_index_drop":1-index,
      "systemic_C_half":-math.log(index),
      "segments":records,
      "status":"Independent floating-point RK4 sanity only, not rigorous certification"}

def main():
    p=argparse.ArgumentParser();p.add_argument("--out",default=None)
    args=p.parse_args()
    result=audit()
    print("PASS independent RK4 numerical crosscheck")
    print("target prices",result["target_closes"])
    print("compensator closes",result["compensator_closes"])
    print("absolute individual dollar residuals",result["terminal_dollar_residuals"])
    print("index ordinary decline",result["geometric_index_drop"])
    if args.out:
        Path(args.out).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")

if __name__=="__main__":main()
