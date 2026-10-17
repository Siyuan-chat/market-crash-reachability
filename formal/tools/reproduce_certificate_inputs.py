import argparse,hashlib,json,re,runpy
from pathlib import Path
from fractions import Fraction as F
ap=argparse.ArgumentParser(description='Reproduce exact rational Lean inputs; generator output is not a proof.')
ap.add_argument('--project',type=Path,default=Path.cwd())
ap.add_argument('--out',type=Path,required=True)
ap.add_argument('--interval-source',type=Path,default=Path('formal/lean/MarketCrash/IntervalODEEnclosure.lean'))
a=ap.parse_args(); root=a.project.resolve(); out=a.out.resolve(); out.mkdir(parents=True,exist_ok=True)
source=root/'verification/certify_streak_interval.py'
certificate=root/'data/certificates/final_interval_certificate.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(certificate)=='354c7797c1e25ebee143d04d11e23ec92cb93214b7333eed7fcd91dd0493c18f'
p=runpy.run_path(str(source)); I=p['I']; Q=p['Q']; dt=p['DT']; rho=p['RHO']; kn=p['KNOT_X'];times=p['KNOT_TIMES'];f=p['f_at']
assert Q==10**32 and dt.lo==Q//2000 and dt.hi==Q//2000
assert rho.lo==2*Q//5 and rho.hi==2*Q//5
assert kn[1].lo==102020225507905*10**18 and kn[1].hi==102020225507908*10**18
assert times==[F(0),F(23,10),F(177,10),F(20),F(223,10),F(377,10),F(40)]
low=high=Q; cs=ts=turn=0; rows=[];checkpoints=[[Q,Q]]
for seg in range(6):
 d=times[seg+1]-times[seg];v,ur=p['min_u_bound_segment'](kn[seg],kn[seg+1],d)
 xs=I(min(kn[seg].lo,kn[seg+1].lo),max(kn[seg].hi,kn[seg+1].hi));ud=v*(v+rho*(2*xs-1));M=p['max_abs'](ur);D=p['max_abs'](ud)
 B=9*D/F(7,10)+(F(2,5)+9*M/F(49,100))*(F(6,25)+9*M/F(7,10));ep=I.rat(B/2)*dt*dt
 for j in range(int(d/F(1,2000))):
  nl=(I(low)+dt*f(F(j,2000),kn[seg],v,I(low))-ep).lo;nh=(I(high)+dt*f(F(j,2000),kn[seg],v,I(high))+ep).hi
  lb=min(low,nl)-(I.rat(F(17,10))*dt).hi;hb=max(high,nh)+(I.rat(F(17,10))*dt).hi
  x0=kn[seg]+v*I.rat(F(j,2000));x1=kn[seg]+v*I.rat(F(j+1,2000));xx=I(min(x0.lo,x1.lo),max(x0.hi,x1.hi));u=xx*(v+rho*(xx-1))
  cs+=((9*I(max(0,u.hi))/I(lb))*dt).hi;ts+=((I(max(0,-u.lo))/I(xx.lo))*dt).hi;turn+=(I.rat(9)*I(max(abs(u.lo),abs(u.hi)))*dt).hi
  low,high=nl,nh;rows.append([low,high,cs,ts,turn])
  if len(rows)%100==0:checkpoints.append([low,high])
assert len(rows)==80000 and len(checkpoints)==801
lean=(root/'formal/lean/MarketCrash/RationalIntervalChecker.lean').read_text(encoding='utf-8')
body=lean.split('def replayCheckpoints : Array (Int × Int) := #[',1)[1].split(']',1)[0]
committed=[list(map(int,m)) for m in re.findall(r'\((\d+),\s*(\d+)\)',body)]
assert checkpoints==committed
(out/'checkpoints.json').write_text(json.dumps(checkpoints))
(out/'rolling-reference-row40000.json').write_text(json.dumps([40000]+rows[39999]))
(out/'critical-rows-79800-80000.json').write_text(json.dumps([[79800]+rows[79799]]+[[k]+rows[k-1] for k in range(79801,80001)]))
row=lambda r:'⟨'+', '.join(map(str,r))+'⟩'
fragments=[]
for c in [8,9]:fragments.append(f'def resourceChunk_079_{c} : Array Row := #['+',\n'.join(row(r) for r in rows[79000+c*100:79000+(c+1)*100])+']')
groups=['#[]']*79+['#['+', '.join(['#[]']*7+['(Array.replicate 99 (default : Row)).push '+row(rows[79799]),'resourceChunk_079_8','resourceChunk_079_9'])+']']
groups[39]='#['+', '.join(['#[]']*9+['(Array.replicate 99 (default : Row)).push '+row(rows[39999])])+']'
fragments.append('def rows : Array (Array (Array Row)) := #[\n'+',\n'.join(groups)+'\n]')
(out/'critical-row-data.lean.txt').write_text('\n'.join(fragments),encoding='utf-8')
intervalsource=a.interval_source if a.interval_source.is_absolute() else root/a.interval_source
intervaltext=intervalsource.read_text(encoding='utf-8')
intervalbody=intervaltext.split('-- BEGIN D01 RESOURCE ROW DATA',1)[1].split('-- END D01 RESOURCE ROW DATA',1)[0].strip()
assert intervalbody=='\n'.join(fragments).strip(), 'final retained201 row data differs from regenerated exact input'
result={'status':'PASS','retained201RowFragmentIdentical':True,'rollingReferenceRow40000Identical':True,'retainedLiteralRows':202,'leanIntervalSource':str(a.interval_source),'leanIntervalSourceSHA256':sha(intervalsource),'sourceCertificateSHA256':sha(certificate),'generatorInputSHA256':sha(source),'leanCheckpointSource':'formal/lean/MarketCrash/RationalIntervalChecker.lean','leanCheckpointSourceSHA256':sha(root/'formal/lean/MarketCrash/RationalIntervalChecker.lean'),'Q':Q,'steps':len(rows),'checkpointCount':len(checkpoints),'criticalSteps':[79800,80000],'checkpointTableIdentical':True,'outputSHA256':{q.name:sha(q) for q in sorted(out.iterdir()) if q.is_file() and q.name!='result.json'},'trust':'All mathematical soundness and required numeric checks are proved by Lean kernel. This generator only reproduces exact inputs.'}
(out/'result.json').write_text(json.dumps(result,indent=2)); print(json.dumps(result))
