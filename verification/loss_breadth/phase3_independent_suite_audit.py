"""Independent ODE integration audit of exact rational interval certificate inputs.
Scientific scope: floating-point crosscheck only, independent of directed interval algorithm.
"""
import json,math
from pathlib import Path
from fractions import Fraction as Fr
from scipy.integrate import solve_ivp
PATH=Path(__file__).resolve().parent/'phase3_certification_suite_results.json'

def audit():
    rec=json.load(open(PATH))
    result=[]
    for cert in rec['case_results']:
        k=cert['k'];m=cert['m'];r=k/m
        old=1.,1.
        dollar=0.;turnover=0.;first=None;slack=1e6;rate=0.;H=[0.,0.];maxendpoint_error=0.
        for entry,expected in zip(cert['schedules'],cert['endpoint_intervals']):
            a,b,q=[float(Fr(s)) for s in entry]
            assert b>a
            def ode(t,z):
                x,y,hx,hy=z
                return [-.4*(x-1)+q/x,-.4*(y-1)-r*q/y,max(-q/x,0.),max(r*q/y,0.)]
            ini=[old[0],old[1],*H]
            sol=solve_ivp(ode,(a,b),ini,method='DOP853',rtol=4e-13,atol=1e-14,max_step=.04,dense_output=True)
            sol2=solve_ivp(ode,(a,b),ini,method='RK45',rtol=2e-12,atol=1e-13,max_step=.07)
            assert sol.success and sol2.success
            pts=sol.sol([a,b])
            now=(sol.y[0,-1],sol.y[1,-1]);H=[float(sol.y[2,-1]),float(sol.y[3,-1])]
            assert abs(sol.y[0,-1]-sol2.y[0,-1])<1e-8 and abs(sol.y[1,-1]-sol2.y[1,-1])<1e-8
            for i,label in enumerate(('target_bounds','comp_bounds')):
                lo,hi=map(float,expected[label]);assert lo-1e-12<=now[i]<=hi+1e-12,(cert['case'],label,now[i],(lo,hi))
                maxendpoint_error=max(maxendpoint_error,hi-lo)
                rate=max(rate, max(abs(q)/min(pts[0]) if i==0 else abs(r*q)/min(pts[1]),0.))
            if abs(b-20)<1e-10:first=now
            assert first is not None or b<=20
            # Endpoint numerical bands (rigorous endpoint checks already in certificate).
            base=(1.,1.) if b<=20 else first
            for i in range(2):
                slack=min(slack,min(old[i],now[i])-.75*base[i],1.25*base[i]-max(old[i],now[i]))
            dollar+=(b-a)*q
            turnover+=k*abs(q)*(b-a)
            old=now
        d=1-old[0]
        mean=-(k*math.log(old[0])+m*math.log(old[1]))/10.
        geom=1-math.exp(-mean)
        assert abs(dollar)<1e-12
        assert abs(turnover-cert['paired_dollar_turnover'])<1e-9
        assert turnover<float(Fr(cert['exact_inputs']['Mcap'])) and rate<.285 and min(slack,.25)>0 and max(H)<2
        assert d>float(Fr(cert['target_loss_strictly_exceeds']))
        if cert['case']=='F100-0.65pct':assert 1-old[1]>float(Fr(cert['target_loss_strictly_exceeds']))
        result.append({'case':cert['case'],'audit':'PASS','terminal_x':now[0],'terminal_y':now[1],
            'loss_fraction':d,'mean_log_loss':mean,'geom_index_loss':geom,
            'turnover':turnover,'peak_rate_endpoints':rate,
            'band_slack_endpoints':slack,'gross_sold_per_asset_group':H,
            'max_interval_width_of_certified_endpoint':maxendpoint_error})
        print(cert['case'],'PASS','d',round(d,6),'A',round(mean,6),'M',round(turnover,4),'bandslack',round(slack,5))
    out=str(Path(__file__).resolve().parent/'phase3_independent_suite_audit.json')
    with open(out,'w') as f:json.dump({'method':'DOP853 plus RK45; separate from integer interval proof','cases':result},f,indent=2)
    print('Saved',out)
if __name__=='__main__':audit()
