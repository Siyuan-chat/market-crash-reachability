"""Run the curated verification commands without changing mathematical assertions."""
from pathlib import Path
import subprocess, sys, hashlib, json
ROOT=Path(__file__).resolve().parents[1]
mode=sys.argv[1] if len(sys.argv)>1 else 'quick'
if mode not in ('quick','full'): raise SystemExit('Choose quick or full')
logs=ROOT/'build/logs'; logs.mkdir(parents=True,exist_ok=True)
commands=[['scripts/verify_results.py'],['scripts/verify_multiday.py'],['scripts/verify_figure_data.py'],
          ['verification/verify_generalized_coordinate.py'],
          ['verification/verify_consistency.py'],
          ['verification/audit_manuscript_certificate.py']]
if mode=='full':
    commands.insert(0,['verification/certify_streak_interval.py','--out','build/final_interval_certificate.json'])
    commands.append(['verification/audit_sensitivity.py'])
results=[]
for command in commands:
    proc=subprocess.run([sys.executable,*command],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (logs/(Path(command[0]).stem+'.txt')).write_text(proc.stdout.replace(str(ROOT),'<repository>'),encoding='utf-8')
    print(command[0], 'PASS' if proc.returncode==0 else 'FAIL',flush=True)
    results.append({'command':command,'exit_code':proc.returncode})
    if proc.returncode: print(proc.stdout)
if mode=='full':
    expected=(ROOT/'data/certificates/final_interval_certificate.json').read_bytes()
    actual=(ROOT/'build/final_interval_certificate.json').read_bytes() if (ROOT/'build/final_interval_certificate.json').exists() else b''
    same=actual==expected
    results.append({'check':'certificate_byte_identity','passed':same,'sha256':hashlib.sha256(actual).hexdigest()})
    print('certificate byte identity:',same)
(logs/(mode+'_summary.json')).write_text(json.dumps(results,indent=2)+'\n')
if any(r.get('exit_code',0)!=0 or r.get('passed',True) is False for r in results): raise SystemExit(1)
