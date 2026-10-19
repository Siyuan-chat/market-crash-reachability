"""Additional exact-rational, directed-rounding certificates for loss/breadth witnesses.

All endpoints/bounds derive from rational step clocks and inputs; no unbounded
float rounding is used in any proof assertion. The numerical result displays
are not proof data. Underlying interval scheme is independently auditable and
has not yet had external code review; NOT a full formal-verification claim.
"""
from fractions import Fraction as Fr
from math import ceil
from pathlib import Path
import json,hashlib

Q=10**24
rho=Fr(2,5)
BAND=Fr(1,4)
VM=Fr(285,1000)
HMAX=Fr(2)
MIN_S=Fr(3,5)
MAX_S=Fr(8,5)
QB=Fr(28,100)            # max absolute group dollar flow per asset
FB=Fr(71,100)           # upper bound on |S'| for S in [3/5,8/5]
FPB=Fr(118,100)         # upper bound on |f'(S)|
SB=Fr(1)                # upper bound on |S''| < FB*FPB < SB
DTMAX=Fr(1,4000)

def ceil_div(a,b):return -((-a)//b)
def fmin(fr):return fr.numerator*Q//fr.denominator
def fmax(fr):return ceil_div(fr.numerator*Q,fr.denominator)
def x_decimal(x):return f'{float(Fr(x,Q)):.12f}'

def one(bounds,h,q):
    lo,hi=bounds
    rem=ceil_div(SB.numerator*h.numerator*h.numerator*Q,2*SB.denominator*h.denominator*h.denominator)
    def delta(S,upper):
        a=-2*h.numerator*(S-Q);b=5*h.denominator
        c=h.numerator*q.numerator*Q*Q;d=h.denominator*q.denominator*S
        return (ceil_div(a,b)+ceil_div(c,d)) if upper else (a//b+c//d)
    return lo+delta(lo,False)-rem, hi+delta(hi,True)+rem

def solve_iv(bounds,dur,q):
    if not dur:return bounds,0
    assert abs(q)<=QB,(q,abs(q))
    assert FB>=rho*Fr(3,5)+QB/MIN_S
    assert FPB>=rho+QB/(MIN_S*MIN_S)
    assert FB*FPB<SB
    if q==0 and bounds==(Q,Q):return bounds,0
    n=ceil(dur/DTMAX)
    h=dur/n
    gap=fmax(FB*h)
    boundlo=fmax(MIN_S)+gap;boundhi=fmin(MAX_S)-gap
    for i in range(n):
        assert bounds[0]>=boundlo and bounds[1]<=boundhi,('bootstrap fail',i,str(q),bounds)
        bounds=one(bounds,h,q)
        assert bounds[0]>=boundlo and bounds[1]<=boundhi,('bootstrap fail after step',i,str(q),bounds)
    return bounds,n

def C(s):return Fr(s)
def construct_cases():
    T=C(40);DAY=C(20)
    q=[]
    for k,b,tp,tn,lab,index_floor in [
        (5,C('.26'),C('2.0'),C('1.55'),'P50-20',C('.96')),
        (6,C('.24'),C('3.5'),C('1.4'),'P60-20',C('.95')),
        (7,C('.19'),C('5.5'),C('2.7'),'P70-10',C('.97')),
    ]:
        q.append({'id':lab,'k':k,'Mcap':C(3),'target_floor':{5:C('.7771'),6:C('.7910'),7:C('.8740')}[k],'index_floor':index_floor,
            'segments':[(C(0),tp,b/tp),(T-tn,T,-b/tn)]})
    for k,a1,a3,w1,w2,w3,g1,lab,mcap,tprice,index_floor in [
        (8,C('0.020005576338'),C('0.158140461748'),C('0.401289730597'),C('11.552628595060'),C('2.358357669804'),C('0.004457191867'),'R80-10',C(3),C('.892'),C('.97')),
        (7,C('0.036616'),C('0.291916'),C('0.5179'),C('12.9713'),C('2.6763'),C('0.0115'),'R70-20-M5',C(5),C('.798'),C('.94')),
    ]:
        q.append({'id':lab,'k':k,'Mcap':mcap,'target_floor':tprice,'index_floor':index_floor,
            'segments':[(DAY-w1,DAY,-a1/w1),(DAY+g1,DAY+g1+w2,(a1+a3)/w2),(T-w3,T,-a3/w3)]})
    a1=C('0.013956473042');a3=C('0.195977071642');w1=C('0.222524383211');w2=C('6.090944893906');w3=C('1.650596722494');g1=C('0.074442494954')
    q.append({'id':'R70-15.5', 'k':7, 'Mcap':C(3), 'target_floor':C('.845'), 'index_floor':C('.96'),
        'segments':[(DAY-w1,DAY,-a1/w1),(DAY+g1,DAY+g1+w2,(a1+a3)/w2),(T-w3,T,-a3/w3)]})
    # All coverage: both five-asset groups descend, using three-stage +/-/+ (dollar-balanced).
    a1=C('0.176678824899');a3=C('0.108632498009');w1=C('4.284528203015');w2=C('1.631953032273');w3=C('0.485079583660');g1=C('4.857369196812');g2=C('1.361936093903')
    t0=T-(w1+w2+w3+g1+g2)
    q.append({'id':'F100-0.65pct','k':5,'Mcap':C(3),'target_floor':C('.9935'),'comp_floor':C('.9935'),'index_floor':C('.9935'),
        'segments':[(t0,t0+w1,a1/w1),(t0+w1+g1,t0+w1+g1+w2,-(a1+a3)/w2),(T-w3,T,a3/w3)]})
    return q

def fill(spec):
    out=[];prior=C(0)
    for a,b,rate in spec['segments']:
        assert prior<=a<b<=40
        if a>prior:out.append((prior,a,C(0)))
        out.append((a,b,rate));prior=b
    if prior<40:out.append((prior,C(40),C(0)))
    split=[]
    for a,b,rate in out:
        if a<C(20)<b:split.extend([(a,C(20),rate),(C(20),b,rate)])
        else:split.append((a,b,rate))
    assert split[0][0]==0 and split[-1][1]==40
    assert all(split[i][1]==split[i+1][0] for i in range(len(split)-1))
    assert sum((b-a)*rate for a,b,rate in split)==0
    return split

def test_case(spec):
    k=spec['k'];m=10-k;ratio=Fr(k,m);schedules=fill(spec)
    groups=[(Q,Q),(Q,Q)]; steps=0;records=[];maxrate=C(0); gross=[C(0),C(0)];turnover=C(0)
    ref=[(C(1),C(1)),(C(1),C(1))];min_band=C(100)
    for a,b,q in schedules:
        if a==20:
            ref=[(Fr(g[0],Q),Fr(g[1],Q)) for g in groups]
        old=groups
        groups=[]
        for gi,rate in enumerate((q,-ratio*q)):
            interval,n=solve_iv(old[gi],b-a,rate)
            steps+=n
            groups.append(interval)
            smin=Fr(min(old[gi][0],interval[0]),Q)
            if rate!=0:
                maxrate=max(maxrate,abs(rate)/smin)
                if rate<0:gross[gi]+=-rate*(b-a)/smin
            for lower,upper in (old[gi],interval):
                l,u=Fr(lower,Q),Fr(upper,Q)
                slack_lower=l-(1-BAND)*ref[gi][1]
                slack_upper=(1+BAND)*ref[gi][0]-u
                min_band=min(min_band,slack_lower,slack_upper)
                assert slack_lower>0 and slack_upper>0,('band failure',spec['id'],str(a),gi,float(slack_lower),float(slack_upper))
        turnover+=Fr(1,2)*(k*abs(q)+m*abs(ratio*q))*(b-a)
        records.append({'start':str(a),'end':str(b),'target_dollar_rate':str(q),'comp_dollar_rate':str(-ratio*q),
            'target_bounds':[x_decimal(x) for x in groups[0]],'comp_bounds':[x_decimal(x) for x in groups[1]]})
    assert maxrate<VM,('rate',spec['id'],float(maxrate))
    assert turnover<spec['Mcap'],('M',spec['id'],float(turnover))
    assert max(gross)<HMAX,('H',spec['id'],*[float(g) for g in gross])
    assert Fr(groups[0][1],Q)<spec['target_floor'],('target floor',spec['id'],[x_decimal(x) for x in groups[0]])
    if 'comp_floor' in spec: assert Fr(groups[1][1],Q)<spec['comp_floor'],('comp floor',spec['id'],[x_decimal(x) for x in groups[1]])
    else:assert groups[0][1]<groups[1][0],('target breadth',spec['id'])
    # Product of 10 normalized terminal prices < index_floor^10 implies geometric-index drop > 1-index_floor.
    products=(Fr(groups[0][1],Q)**k)*(Fr(groups[1][1],Q)**m)
    assert products<spec['index_floor']**10,('mean loss',spec['id'],float(products))
    result={'case':spec['id'],'conclusion':'PASS: exact rational directed-rounding interval certificate',
        'status':'independently auditable but not externally audited; computer-assisted witness, not optimality proof',
        'k':k,'m':m,'max_absolute_asset_price_interval_x':[x_decimal(v) for v in groups[0]],
        'max_absolute_asset_price_interval_y':[x_decimal(v) for v in groups[1]],
        'target_loss_strictly_exceeds':str(1-spec['target_floor']),
        'min_geometric_index_loss_strictly_exceeds':str(1-spec['index_floor']),
        'per_asset_selling_shares_upper':[float(v) for v in gross],
        'paired_dollar_turnover':float(turnover),'per_asset_gross_share_rate_upper':float(maxrate),
        'min_price_band_slack_lower':float(min_band),'scalar_steps':steps,
        'exact_dollar_ledger_closed':True,'segment_count':len(schedules),
        'exact_inputs':{a:str(v) for a,v in spec.items() if a!='segments'},
        'schedules':[[str(a),str(b),str(q)] for a,b,q in schedules],
        'endpoint_intervals':records}
    print(spec['id'],'PASS price intervals',[x_decimal(v) for v in groups[0]],[x_decimal(v) for v in groups[1]],
          'step',steps,'M',round(float(turnover),6),'rateUB',round(float(maxrate),6),'band margin LB',round(float(min_band),6),flush=True)
    return result

def main():
    cases=construct_cases()
    results=[]
    for spec in cases:results.append(test_case(spec))
    payload={'assumptions':{
        'F':'1','eta':'1','rho':'2/5','T':'40','day_length':'20',
        'band':'1/4','gross_rate_cap':'0.285','H_per_asset_cap':'2',
        'positive_price_bootstrap':'3/5 to 8/5','B_on_second_derivative':'1',
        'precision_Q':str(Q),'maximum_time_step':str(DTMAX)},
        'proof':('Scalar price ODE Sdot=-(2/5)(S-1)+q/S with exact rational piecewise-constant dollar rates. '
                 'Directed integer floor/ceil Taylor steps with |Sddot|<1 on the verified bootstrap interval. '
                 'Autonomous scalar price monotonicity between segment endpoints ensures extrema/rate/band bounds. '
                 'Dollar flows sum to zero and each group-specific ledger closes exactly. '
                 'Conservative share-sale upper bounds computed from exact dollar masses and certified segment minimum prices. '
                 'Market geometric loss uses an exact rational product inequality.'),
        'case_results':results}
    path=str(Path(__file__).resolve().parent/'phase3_certification_suite_results.json')
    with open(path,'w') as f:json.dump(payload,f,indent=2)
    print('ALL',len(results),'CERTIFICATES PASS',path)

if __name__=='__main__':main()
