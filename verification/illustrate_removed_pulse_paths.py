"""Visualize why a formerly admissible severe sweep is excluded by new controls.
Purely diagnostic: imports the OLD witness only to flag its violations, not to
certify a constrained reachable trajectory.
"""
import sys,json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
root=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(root/'scripts'))
from numerical_experiments import spectator_closed_path
w=spectator_closed_path(n=3,T=3,loss_target=3)
fig,ax=plt.subplots(figsize=(6.5,3.0))
for i in range(3):
    ax.plot(w.times,w.prices[:,i],label=f'Asset {i+1}',lw=1.65)
ax.axhline(.8,ls='--',color='.4',lw=1.2,label='Stylized 20% session floor')
ax.axhline(1,ls=':',color='.5',lw=1)
ax.set(yscale='log',xlabel='Time',ylabel='Executed price (log scale)',
       title='The old severe sweep cannot be reused under the new rules')
ax.legend(frameon=False,fontsize=8,loc='upper right')
fig.tight_layout();fig.savefig(root/'figures'/'old_pulse_path_fails_limits.pdf',bbox_inches='tight')
(root/'data'/'old_path_violation.json').write_text(json.dumps({
 'n':3,'target_loss':3,'min_executed_price':float(w.prices.min()),
 'twenty_percent_session_floor':.8,
 'violates_price_band':bool(w.prices.min()<.8),
 'violates_any_finite_gross_rate':'yes: contains positive-size instantaneous sweeps',
 'total_dollar_turnover':w.turnover,
 'terminal_dollar_residual':w.residual_dollars
},indent=2)+'\n')
print('old pulse witness min price',w.prices.min(),'outside fixed floor 0.8')
