"""Check selected published figure data against recomputed model values."""
from pathlib import Path
import json, math, re
from numerical_experiments import spectator_closed_path
ROOT=Path(__file__).resolve().parents[1]
fixture=json.loads((ROOT/'data/fixtures/figure_verification.json').read_text())
for key,n,t in [('n3_case',3,3),('n12_case',12,4)]:
    expected=fixture[key]; result=spectator_closed_path(n,t,5)
    for field,value in [('crisis',result.crisis),('turnover',result.turnover),('max_gross_sale_shares',result.max_gross_share_sales)]:
        assert math.isclose(value,expected[field],rel_tol=1e-10,abs_tol=1e-12),(key,field,value,expected[field])
for directory,source in [('paper','main.tex'),('supplementary','supplementary.tex')]:
    for name in re.findall(r'\\includegraphics(?:\[[^\]]*\])?\{([^}]+)\}',(ROOT/directory/source).read_text()):
        assert (ROOT/directory/name).is_file(),name
        assert Path(name).name in fixture['figure_files'],name
print('PASS: two figure-data cases and all manuscript/supplement figure references; not pixel-equivalence validation.')
