"""Check manuscript table rows against generated strict interval evidence."""
import json
from fractions import Fraction as F
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
PAPER=(ROOT/"submission/v14-turnover-dissipation/main.tex").read_text()
DATA=json.loads((ROOT/"build/loss_breadth/certificates.json").read_text())
LOOKUP={record['case']:record for record in DATA}

# Exact schedule ID -> manuscript alias, effective coverage, safe rate cap.
EXPECTED={
 'P50-20':('P50-20',5,'0.217'),
 'P60-20':('P60-20',6,'0.258'),
 'P70-10':('P70-10',7,'0.165'),
 'R70-15.5':('R70-15.5',7,'0.278'),
 'k7_16p4_under_M3':('R70-16.4',7,'0.283'),
 'R80-10':('R80-10',8,'0.273'),
 'k9_8_under_M3':('R90-8',9,'0.283'),
 'F100-0.65pct':('F100-0.65',10,'0.260'),
 'full_0p75_under_M3':('F100-0.75',10,'0.283'),
 'k7_20_under_M4':('R70-20 (M4)',7,'0.283'),
 'R70-20-M5':('R70-20 (M5)',7,'0.263'),
 'full_2_under_M7':('F100-2 (M7)',10,'0.283')
}
assert set(LOOKUP)==set(EXPECTED)
for key,(label,k,rate_cap) in EXPECTED.items():
    record=LOOKUP[key]
    assert record['ledger_exact'] and record['coverage_k']==k
    assert F(record['M_exact'])<F(record['cap_M'])
    assert F(record['rate_upper'])<F(rate_cap)
    assert max(F(x) for x in record['sell_share_upper'])<2
    assert F(record['band_slack_lower'])>0
    line=next((line for line in PAPER.splitlines()
               if line.startswith(label+" & ")),None)
    assert line is not None,("Missing manuscript comparison row",label)
    target=f"{float(F(record['strict_ordinary_price_drop'])*100):.2f}"
    index=f"{float(F(record['strict_geometric_index_drop'])*100):.2f}"
    m=f"{float(F(record['M_exact'])):.3f}"
    assert '$>'+target+'$' in line,(key,"target",target,line)
    assert '$>'+index+'$' in line,(key,"index",index,line)
    assert '$'+m+'$' in line,(key,"turnover",m,line)
    assert '$'+rate_cap+'$' in line,(key,"share rate",rate_cap,line)
    assert '$'+str(k)+'/10$' in line,(key,"breadth",k,line)
for label in ("prop:uniform-band-breadth","tab:loss-breadth","app:loss-breadth"):
    assert "\\label{"+label+"}" in PAPER
r80=LOOKUP['R80-10']
assert r80['cap_M']=='3' and r80['coverage_k']==8
assert F(r80['strict_ordinary_price_drop'])==F('0.108')
assert F(r80['strict_geometric_index_drop'])==F('0.03')
assert F(r80['band_slack_lower'])>F('.007')
assert F(r80['rate_upper'])<F('.273')
assert max(F(x) for x in r80['sell_share_upper'])<F('.874')
assert F(r80['M_exact'])==F('2.850336609376')
assert r"\Cris_{0.8}(40)>0.03" in PAPER
assert "1.020225507905" not in PAPER
print("PASS paper/table parity: all 12 exact schedules, strict loss and resource limits")
