"""Independent-of-float, exact rational interval certifier for two phase-4 dollar-closed schedules.
Polynomial/rational directed rounding using integers only in proof-critical path.
Not externally audited; mathematical claims conditional on this simple checker and scalar ODE lemma.
"""
from fractions import Fraction as Fr
from math import ceil
from pathlib import Path
import json,hashlib,time

RHO=Fr(2,5)
Q=10**25
VM=Fr(285,1000)
BAND=Fr(1,4)
MIN_S=Fr(3,5)
MAX_S=Fr(8,5)
QB=Fr(37,100)
FB=Fr(86,100)
FPB=Fr(143,100)
SB=Fr(5,4)
DTMAX=Fr(1,4000)
assert FB>= RHO*(MAX_S-1)+QB/MIN_S
assert FPB>= RHO+QB/(MIN_S*MIN_S)
assert FB*FPB < SB

def ceil_div(a,b):return -((-a)//b)
def lo(fr):return fr.numerator*Q//fr.denominator
def hi(fr):return ceil_div(fr.numerator*Q,fr.denominator)
def fmt(i):return f'{float(Fr(i,Q)):.12f}'

def step(bound,h,q):
    a,b=bound
    rem=hi(SB*h*h/2)
    def df(s,up):
      first=-2*h.numerator*(s-Q)
      denom=5*h.denominator
      # f(s)=-.4(s-1)+q/s ; s measured in integer Q units
      second=h.numerator*q.numerator*Q*Q
      denom2=h.denominator*q.denominator*s
      return (ceil_div(first,denom)+ceil_div(second,denom2)) if up else (first//denom+second//denom2)
    return a+df(a,False)-rem,b+df(b,True)+rem

def propagate(bounds,duration,q):
    assert abs(q)<=QB,(abs(q),QB)
    n=ceil(duration/DTMAX)
    if n==0:return bounds,0
    h=duration/n
    gap=hi(FB*h)
    low=hi(MIN_S)+gap
    high=lo(MAX_S)-gap
    for t in range(n):
        assert bounds[0]>=low and bounds[1]<=high,('failed bootstrap initial',t,bounds)
        bounds=step(bounds,h,q)
        assert bounds[0]>=low and bounds[1]<=high,('failed bootstrap after step',t,bounds)
    return bounds,n

def get_inputs(path,scale_str,case):
    rows=json.loads(Path(path).read_text())
    rec=next(r for r in rows if r['status']=='solved')
    raw=rec['q']
    from decimal import Decimal,localcontext
    scale=Decimal(scale_str)
    # Build exactly representable decimal dollar rates; each 1/2-unit bin, last bin adjusted to give zero integral.
    rr=[Fr(Decimal(f'{Decimal(str(x))*scale:.12f}')) for x in raw]
    rr[-1]=-sum(rr[:-1],Fr(0))
    assert sum(rr,Fr(0))==0
    return {'case':case,'k':rec['k'],'m':10-rec['k'],'rates':rr,'dt':Fr(1,2),
        'target_loss':Fr(1,5) if case.startswith('k7') else Fr(1,50),
        'index_loss':Fr(3,50) if case.startswith('k7') else Fr(1,50),
        'M_cap':Fr(4) if case.startswith('k7') else Fr(7),
        'source':path,'scale':scale_str}

def verify(inputs):
    global QB, FB, FPB, SB
    # Minimize interval overestimation with a rational model-wide derivative bound
    # tailored to this exact schedule (both groups, all time bins).
    k0=inputs['k'];m0=inputs['m'];r0=Fr(k0,m0)
    q_max=max([abs(q) for q in inputs['rates']]+[abs(r0*q) for q in inputs['rates']])
    QB=Fr(ceil(q_max*100),100)
    FB=RHO*(MAX_S-1)+QB/MIN_S+Fr(1,100)
    FPB=RHO+QB/(MIN_S*MIN_S)+Fr(1,100)
    SB=FB*FPB+Fr(1,50)
    assert FB*FPB<SB and max(abs(q) for q in inputs['rates'])<=QB
    print('BEGIN',inputs['case'],'q bound',float(QB),'2nd derivative bound',float(SB),flush=True)
    started=time.monotonic();k=inputs['k'];m=inputs['m'];ratio=Fr(k,m);dt=inputs['dt']
    states=[(Q,Q),(Q,Q)];ref=[(Q,Q),(Q,Q)]
    bandslack=Fr(10);speed=Fr(0);turnover=Fr(0);shares=[Fr(0),Fr(0)];steps=0;trace=[]
    for j,q in enumerate(inputs['rates']):
        if j==len(inputs['rates'])//2:ref=states[:]
        previous=states[:];out=[]
        for ix,p in enumerate([q,-ratio*q]):
            result,n=propagate(states[ix],dt,p)
            out.append(result);steps+=n
            # For scalar autonomous ODE each segment is monotone, so its
            # full-time range is bounded by the hull of its endpoint intervals.
            minP=Fr(min(states[ix][0],result[0]),Q)
            maxP=Fr(max(states[ix][1],result[1]),Q)
            refLo=Fr(ref[ix][0],Q);refHi=Fr(ref[ix][1],Q)
            slack=min(minP-(1-BAND)*refHi,(1+BAND)*refLo-maxP)
            assert slack>0, ('band',j,ix,float(slack))
            bandslack=min(bandslack,slack)
            if p!=0:speed=max(speed,abs(p)/minP)
            if p<0:shares[ix]+= -p*dt/minP
        states=out
        turnover+=k*abs(q)*dt
        trace.append({'t':str((j+1)*dt),'x':[fmt(v) for v in states[0]],'y':[fmt(v) for v in states[1]]})
    assert speed<VM,('rate',float(speed))
    assert turnover<inputs['M_cap'],('turnover',float(turnover))
    assert all(s<2 for s in shares),('share',*[float(s) for s in shares])
    assert Fr(states[0][1],Q) < 1-inputs['target_loss'],('target loss',fmt(states[0][1]))
    if inputs['case'].startswith('full'):
        assert Fr(states[1][1],Q)<1-inputs['target_loss'],('full comp loss',fmt(states[1][1]))
    # all-assets geometric index average, proven by rational comparisons
    prod=Fr(states[0][1],Q)**k * Fr(states[1][1],Q)**m
    assert prod< (1-inputs['index_loss'])**10,('index loss',float(prod))
    return {
      'case':inputs['case'],'M_cap':str(inputs['M_cap']),'scope':'computer-assisted rational directed-rounding interval certificate; external audit pending',
      'source':inputs['source'],'scale':inputs['scale'],
      'k':k,'m':m,'T':'40','bin_duration':str(dt),'exact_ledger_check':sum(inputs['rates'],Fr(0))==0,
      'terminal_target':[fmt(x) for x in states[0]],'terminal_comp':[fmt(x) for x in states[1]],
      'target_loss_certified_strictly_greater_than':str(inputs['target_loss']),
      'market_geometric_index_loss_strictly_greater_than':str(inputs['index_loss']),
      'M_bound':float(turnover),'rate_upper':float(speed),'share_upper':[float(s) for s in shares],
      'min_band_margin':float(bandslack),'steps':steps,'seconds':round(time.monotonic()-started,2),
      'q_exact':[str(x) for x in inputs['rates']],'trace':trace,'regime':{'rho':str(RHO),'minS':str(MIN_S),'maxS':str(MAX_S),
        'maxQ':str(QB),'maxSdot':str(FB),'maxDerivative':str(FPB),'maxSecondDerivative':str(SB),'precisionQ':str(Q),'dt_max':str(DTMAX)} }

if __name__=='__main__':
    configs=[(str(Path(__file__).resolve().parent/'phase4_ipopt_k7_M4.0_B80.json'),'.99','k7_20_under_M4'),
             (str(Path(__file__).resolve().parent/'phase4_ipopt_full_M6.8_B80.json'),'.99','full_2_under_M7')]
    for file,scale,case in configs:
        result=verify(get_inputs(file,scale,case))
        output=str(Path(__file__).resolve().parent/('phase4_certificate_'+case+'.json'))
        with open(output,'w') as f:json.dump(result,f,indent=2)
        print('PASS',case,'end',result['terminal_target'],result['terminal_comp'],'M',result['M_bound'],'rate',result['rate_upper'],'band',result['min_band_margin'],'steps',result['steps'],'sec',result['seconds'],'output',output,flush=True)
