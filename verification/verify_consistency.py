"""Independent consistency checks for V7 multiday claim and rate bracket.

The machine-checkable interval proof is run by certify_streak_interval.py;
this file checks inputs, theorem algebra, numerical plotting outputs, and
certified enclosure containment. It cannot replace the interval verifier.
"""
from __future__ import annotations
import argparse,json
from pathlib import Path
from fractions import Fraction as Q
from math import exp,log,ceil

def verify(root:Path):
 c=json.loads((root/'data/certificates/final_interval_certificate.json').read_text())
 d=json.loads((root/'data/fixtures/improved_witness_illustration.json').read_text())
 assert c['certified_delta_0_020_reached_by_exact_rationals']
 assert c['certified_delta_0_021_not_reached_by_exact_rationals']
 assert c['zero_dollar_target_exact_from_quadratic_root']
 assert c['zero_dollar_comp_from_pairing']
 assert c['daily_bands_strictly_respected'] and c['gross_rate_strictly_under_1']
 assert c['steps']==80000 and c['fixedpoint_scale']==str(10**32)
 tight=max(Q(s['gross_rate_y_tight_upper']) for s in c['segments'])
 target=max(Q(s['gross_rate_x_tight_upper']) for s in c['segments'])
 assert tight<Q('0.285') and target<Q('0.285')
 assert Q(c['compensator_sold_shares_certified_upper'])<2
 assert Q(c['target_sold_shares_certified_upper_each'])<2
 assert Q(c['paired_dollar_turnover_certified_upper'])<3
 y1=c['y_at_knots'][2]['y_interval'];y2=c['y_at_knots'][-1]['y_interval']
 assert Q(y1[0])<Q(str(d['y_day1']))<Q(y1[1])
 assert Q(y2[0])<Q(str(d['y_day2']))<Q(y2[1])
 assert d['gross_rate_numerical']<float(tight)
 assert d['comp_sold_numerical']<float(c['compensator_sold_shares_certified_upper'])
 assert d['target_sold_numerical']<float(c['target_sold_shares_certified_upper_each'])
 assert d['paired_dollar_turnover_numerical']<float(c['paired_dollar_turnover_certified_upper'])
 # Independent exact-rational speed lower-bound test from V5 quadratic theorem.
 v=Q(44,1000);rho=Q(2,5);z=v/rho
 upper=z*z*(1+1/(2*(1-z)**2))
 assert upper==Q(1563441,79210000)
 assert upper<Q(1,50) # .020
 # scalar one-asset comparator, and N,k-dependent market-cut bound
 N=10;k=9;m=1;F=eta=Q(1);tau=Q(20);q=Q(97,100);beta_comp=Q(1,4)
 cut=Q(k,m)*F*(q**2-q**4)/(2*eta*tau*(1+beta_comp)**2)
 assert cut>Q('0.008') and cut<Q('0.009')
 scalar=rho*max(1+q**(day-1)*((1-q)/(1-Q(str(exp(-8))))-1) for day in (1,2))
 assert .023<float(scalar)<.024
 cut_1000=Q(999,1)*F*(q**2-q**4)/(2*eta*tau*(1+beta_comp)**2)
 assert cut_1000>Q('0.88')
 # mandatory model-derived alpha=0.9 crisis criterion
 s2=Q(9409,10000); loss_target=-log(float(s2)); A=(9*loss_target-log(d['y_day2']))/10
 assert 0.020 < A < 0.021 and loss_target>A
 assert c['arithmetic'].startswith('integer endpoints')
 result={
  'certificate':'PASS, all exact rational and enclosure assertions',
  'target_prices':['0.9700','0.9409'],
  'certified_crisis':'>0.020 and <0.021',
  'tight_compensator_max_gross_rate_upper':str(tight),
  'tight_target_max_gross_rate_upper':str(target),
  'max_comp_sale_shares_upper':c['compensator_sold_shares_certified_upper'],
  'total_paired_turnover_upper':c['paired_dollar_turnover_certified_upper'],
  'minimum_rate_lower_strict':'0.044',
  'minimum_rate_upper_strict':'0.285',
  'quadratic_bound_at_rate_0_044':str(float(upper)),
  'scalar_day2_rate_necessary_approx':str(float(scalar)),
  'cut_day2_rate_necessary_k9_m1':str(float(cut)),
  'cut_day2_rate_necessary_k999_m1':str(float(cut_1000)),
  'numerical_y20_in_interval':True,'numerical_y40_in_interval':True,
  'numerical_sales_and_turnover_inside_certificate':True,
  'limitation':'No claim of the global optimal rate or real-world locked-order-book limit-down.'
 }
 (root/'data/v7_regression_summary.json').write_text(json.dumps(result,indent=2))
 print(json.dumps(result,indent=2));return result
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--root',default=str(Path(__file__).resolve().parents[1]));args=a.parse_args();verify(Path(args.root))
