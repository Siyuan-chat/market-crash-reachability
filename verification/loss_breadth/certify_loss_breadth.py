"""Reproduce Phase 3/4 loss--breadth interval witnesses with exact rational controls.

Strict bounds use integer-directed outward rounding, scalar ODE comparison,
and Taylor remainders. This code is original research software, not an externally
audited formal proof or a claim of numerical optimization global optimality.
"""
from __future__ import annotations
import base64, json, zlib
from fractions import Fraction as F
from pathlib import Path
from math import ceil

N=10
RHO=F(2,5)
Q=10**25
DTMAX=F(1,4000)
LOW=F(3,5)
HIGH=F(8,5)
BAND=F(1,4)
RATECAP=F(285,1000)
SHARECAP=F(2)

def fi(v:F)->int:
    return v.numerator*Q//v.denominator

def ci(a:int,b:int)->int:
    return -((-a)//b)

def ce(v:F)->int:
    return ci(v.numerator*Q,v.denominator)

def step(bounds:tuple[int,int], h:F, q:F, sec:F):
    lo,hi=bounds
    rem=ce(sec*h*h/2)
    def change(s:int,upper:bool):
        x=-2*h.numerator*(s-Q)
        y=5*h.denominator
        z=h.numerator*q.numerator*Q*Q
        w=h.denominator*q.denominator*s
        if upper: return ci(x,y)+ci(z,w)
        return x//y+z//w
    return lo+change(lo,False)-rem,hi+change(hi,True)+rem

def run_step(bounds,dur,q,qbound,fb,fprime,sec):
    n=ceil(dur/DTMAX)
    if n==0:return bounds,0
    h=dur/n
    gap=ce(fb*h)
    floor=ce(LOW)+gap
    roof=fi(HIGH)-gap
    for _ in range(n):
        assert bounds[0]>=floor and bounds[1]<=roof,('bootstrap start',q,bounds)
        bounds=step(bounds,h,q,sec)
        assert bounds[0]>=floor and bounds[1]<=roof,('bootstrap end',q,bounds)
    return bounds,n

def f(v):return F(str(v))

def piecewise_case(name,k,segments,thr,idx,cap,full=False):
    end=F(40);previous=F(0);steps=[]
    for a,b,q in segments:
        assert previous<=a<b<=end
        if a>previous:steps.append((previous,a,F(0)))
        steps.append((a,b,q));previous=b
    if previous<end:steps.append((previous,end,F(0)))
    refined=[]
    for a,b,q in steps:
        if a<F(20)<b:refined.extend([(a,F(20),q),(F(20),b,q)])
        else:refined.append((a,b,q))
    assert sum(((b-a)*q for a,b,q in refined),F(0))==0
    return dict(id=name,k=k,cap=cap,drop=thr,index=idx,full=full,parts=refined,source='phase3')

def phase3_cases():
    C=f;out=[];T=C(40);DAY=C(20)
    for k,b,tp,tn,name,loss,index in [
        (5,C('.26'),C('2.0'),C('1.55'),'P50-20',C('.2229'),C('.04')),
        (6,C('.24'),C('3.5'),C('1.4'),'P60-20',C('.209'),C('.05')),
        (7,C('.19'),C('5.5'),C('2.7'),'P70-10',C('.126'),C('.03')),
    ]:
        out.append(piecewise_case(name,k,[(C(0),tp,b/tp),(T-tn,T,-b/tn)],loss,index,C(3)))
    for k,a1,a3,w1,w2,w3,g1,name,cap,loss,index in [
        (8,C('0.020005576338'),C('0.158140461748'),C('0.401289730597'),C('11.552628595060'),C('2.358357669804'),C('0.004457191867'),'R80-10',C(3),C('.108'),C('.03')),
        (7,C('0.036616'),C('0.291916'),C('0.5179'),C('12.9713'),C('2.6763'),C('0.0115'),'R70-20-M5',C(5),C('.202'),C('.06')),
        (7,C('0.013956473042'),C('0.195977071642'),C('0.222524383211'),C('6.090944893906'),C('1.650596722494'),C('0.074442494954'),'R70-15.5',C(3),C('.155'),C('.04')),
    ]:
        out.append(piecewise_case(name,k,[(DAY-w1,DAY,-a1/w1),(DAY+g1,DAY+g1+w2,(a1+a3)/w2),(T-w3,T,-a3/w3)],loss,index,cap))
    a1=C('0.176678824899');a3=C('0.108632498009');w1=C('4.284528203015');w2=C('1.631953032273');w3=C('0.485079583660');g1=C('4.857369196812');g2=C('1.361936093903')
    t0=T-(w1+w2+w3+g1+g2)
    out.append(piecewise_case('F100-0.65pct',5,[(t0,t0+w1,a1/w1),(t0+w1+g1,t0+w1+g1+w2,-(a1+a3)/w2),(T-w3,T,a3/w3)],C('.0065'),C('.0065'),C(3),full=True))
    return out

def phase4_cases(encoded:str):
    rows=json.loads(zlib.decompress(base64.b64decode(encoded)).decode())
    out=[]
    for r in rows:
        rates=[F(v,10**12) for v in r['q12']]
        assert len(rates) in (80,160) and sum(rates)==0
        dt=F(40,len(rates))
        parts=[(dt*i,dt*(i+1),q) for i,q in enumerate(rates)]
        out.append(dict(id=r['id'],k=r['k'],cap=F(r['cap']),drop=F(r['target']),index=F(r['idx']),full=r['id'].startswith('full'),parts=parts,source='phase4'))
    return out

def certify(case):
    k=case['k'];m=N-k;ratio=F(k,m)
    qmax=max(max(abs(q),abs(ratio*q)) for _,_,q in case['parts'])
    qb=F(ceil(qmax*100),100)
    fb=RHO*(HIGH-1)+qb/LOW+F(1,100)
    fp=RHO+qb/(LOW*LOW)+F(1,100)
    sb=fb*fp+F(1,50)
    assert fb*fp<sb
    state=[(Q,Q),(Q,Q)]
    ref=[(Q,Q),(Q,Q)]
    total=F(0);sold=[F(0),F(0)];speed=F(0);slack=F(100);stepCount=0
    trajectory=[]
    for a,b,q in case['parts']:
        if a==20:ref=state[:]
        current=[]
        for i,dollar in enumerate((q,-ratio*q)):
            previous=state[i]
            last,n=run_step(previous,b-a,dollar,qb,fb,fp,sb)
            stepCount+=n
            lower=F(min(previous[0],last[0]),Q)
            upper=F(max(previous[1],last[1]),Q)
            lowerRef=F(ref[i][0],Q)
            upperRef=F(ref[i][1],Q)
            gap=min(lower-(1-BAND)*upperRef,(1+BAND)*lowerRef-upper)
            assert gap>0,('price band',case['id'],a,i,float(gap))
            slack=min(slack,gap)
            if dollar:
                speed=max(speed,abs(dollar)/lower)
                if dollar<0:sold[i]+=-dollar*(b-a)/lower
            current.append(last)
        state=current
        total+=k*abs(q)*(b-a)
        trajectory.append([str(b),[str(F(x,Q)) for x in state[0]],[str(F(x,Q)) for x in state[1]]])
    assert speed<RATECAP,('gross share rate',case['id'],float(speed))
    assert total<case['cap'],('gross paired-dollar turnover',case['id'],float(total))
    assert max(sold)<SHARECAP,('sale inventory',case['id'],*map(float,sold))
    targetU=F(state[0][1],Q);compU=F(state[1][1],Q)
    assert targetU<1-case['drop'],('target drop',case['id'],float(targetU))
    if case['full']:assert compU<1-case['drop'],('all-asset drop',case['id'],float(compU))
    assert targetU**k*compU**m<(1-case['index'])**N,('geometric index drop',case['id'])
    assert sum(((b-a)*q for a,b,q in case['parts']),F(0))==0
    output={'case':case['id'],'source':case['source'],'k_group':k,'coverage_k':N if case['full'] else k,
            'strict_ordinary_price_drop':str(case['drop']),'strict_geometric_index_drop':str(case['index']),
            'cap_M':str(case['cap']),'M_exact':str(total),'rate_upper':str(speed),
            'sell_share_upper':[str(x) for x in sold],'band_slack_lower':str(slack),
            'target_endpoint_interval':[str(F(x,Q)) for x in state[0]],
            'comp_endpoint_interval':[str(F(x,Q)) for x in state[1]],
            'ledger_exact':True,'steps':stepCount,'time_intervals':len(case['parts']),
            'case_proof_constants':{'min_price':str(LOW),'max_price':str(HIGH),'max_flow':str(qb),
               'max_speed':str(fb),'max_derivative':str(fp),'max_second_derivative':str(sb),
               'scale_Q':str(Q),'step_max':str(DTMAX)},
            'history':trajectory}
    print('PASS',case['id'],'k',output['coverage_k'],'price>',float(case['drop']),
          'index>',float(case['index']),'M=',round(float(total),6),
          'rate=',round(float(speed),6),'band=',round(float(slack),6),
          'steps=',stepCount,flush=True)
    return output

def run_all(encoded,output_dir):
    cases=phase3_cases()+phase4_cases(encoded)
    results=[certify(x) for x in cases]
    root=Path(output_dir);root.mkdir(parents=True,exist_ok=True)
    (root/'certificates.json').write_text(json.dumps(results,indent=2)+'\n')
    (root/'summaries.json').write_text(json.dumps([{k:v for k,v in row.items() if k!='history'} for row in results],indent=2)+'\n')
    decoded=json.loads(zlib.decompress(base64.b64decode(encoded)).decode())
    (root/'decoded_phase4_schedules.json').write_text(json.dumps(decoded,indent=2)+'\n')
    assert len(results)==12
    print('PASS ALL',len(results),'strict rational interval checks')
    return results

if __name__=='__main__':
    root=Path(__file__).resolve().parents[2]
    run_all(Path(__file__).with_name('phase4_schedules.b64').read_text(),
            root/'build/loss_breadth')
