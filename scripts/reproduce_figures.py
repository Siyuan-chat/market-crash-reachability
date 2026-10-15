"""Regenerate illustrations in a scratch copy; preserve distributed figure assets."""
from pathlib import Path
import subprocess, sys, shutil, json, math
ROOT=Path(__file__).resolve().parents[1]
scratch=ROOT/'build/figure_workspace'; scratch.mkdir(parents=True,exist_ok=True)
for name in ('scripts','verification'):
    shutil.copytree(ROOT/name,scratch/name,dirs_exist_ok=True)
(scratch/'data').mkdir(exist_ok=True)
(scratch/'figures').mkdir(exist_ok=True)
shutil.copyfile(ROOT/'data/fixtures/improved_witness_illustration.json',scratch/'data/improved_witness_illustration.json')
commands=[['scripts/make_figures.py'],['verification/finite_rate_and_bands.py'],
 ['scripts/consecutive_limit_down.py'],['scripts/improved_multiday_witness.py'],
 ['scripts/make_multiday_figures.py'],['verification/illustrate_removed_pulse_paths.py']]
for command in commands:
    subprocess.run([sys.executable,*command],cwd=scratch,check=True)
for folder in ('paper','supplementary'):
    for asset in (ROOT/folder/'figures').glob('*.pdf'):
        assert (scratch/'figures'/asset.name).is_file(), 'Missing generator output: '+asset.name
def compare(expected,actual,location=''):
    if isinstance(expected,dict):
        for key,value in expected.items(): compare(value,actual[key],location+'/'+key)
    elif isinstance(expected,list):
        assert len(expected)==len(actual),location
        for i,(a,b) in enumerate(zip(expected,actual)): compare(a,b,location+'/'+str(i))
    elif isinstance(expected,(int,float)) and not isinstance(expected,bool):
        assert math.isclose(expected,actual,rel_tol=1e-8,abs_tol=1e-11),(location,expected,actual)
    else: assert expected==actual,(location,expected,actual)
# The figure_files list is a directory inventory, whose timing differs by script order.
for name in ('figure_verification.json','finite_rate_verification.json'):
    expected=json.loads((ROOT/'data/fixtures'/name).read_text())
    actual=json.loads((scratch/'data'/name).read_text())
    if name=='figure_verification.json':
        expected.pop('figure_files'); actual.pop('figure_files')
    compare(expected,actual,name)
shutil.copytree(scratch/'figures',ROOT/'figures',dirs_exist_ok=True)
print('All distributed figure filenames regenerated; bytes may differ by rendering environment.')
