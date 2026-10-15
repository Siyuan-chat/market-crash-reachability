"""Independent deterministic tests and analytic checks for Section 7.

Does not call the former phase-7/8 impulse witnesses. The new example uses
explicit piecewise-linear targets and a separately integrated compensator ODE.
"""
from pathlib import Path
import json,math
import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq
from consecutive_limit_down import Params, main, get_high,knots,state_x,target_ledger,necessary_scalar_speed,max_streak_scalar


def verify():
    p=Params();res,tra=main(Path(__file__).resolve().parents[1]/"data")
    t,x,y,u,rt,rc,X,Y,K,flx,upx,fly,upy=tra
    checks={}
    def check(name,test):
        checks[name]=bool(test)
        if not test:raise AssertionError(name)

    # Independent direct numerical quadrature of the dollar-ledger integrand,
    # splitting at prescribed ramps/holds so that no kink is hidden.
    def integrand(t):
        z,v=state_x(t,K)
        return z*(v+p.rho*(z-1))/p.eta
    direct=sum(quad(integrand,ta,tb,epsabs=1e-12,epsrel=1e-12,limit=200)[0]
               for ta,tb in zip(K[:-1,0],K[1:,0]))
    check('closed_target_ledger_analytic',abs(X[-1])<1e-11)
    check('closed_target_ledger_independent_quadrature',abs(direct)<1e-10)
    check('paired_compensator_final_ledger',abs(Y[-1])<1e-10)
    # Independent finite-difference derivative of the integrated compensator;
    # ignore the known slope discontinuities at the path knots.
    y_diff=np.gradient(y,t,edge_order=2)
    smooth_mask=np.ones(t.size,dtype=bool)
    for break_t in K[:,0]:
        smooth_mask &= np.abs(t-break_t)>.04
    independent_dollar_residual=y*(y_diff+p.rho*(y-p.F))+p.k*u
    check('paired_dollar_rates_finite_difference',
          np.max(np.abs(independent_dollar_residual[smooth_mask]))<2e-5)
    check('all_prices_strictly_positive',min(x.min(),y.min())>0.0)
    check('target_first_close_at_floor',abs(x[np.searchsorted(t,p.session)]-(1-p.target_band))<1e-12)
    check('target_second_close_at_reset_floor',abs(x[-1]-(1-p.target_band)**2)<1e-12)
    check('target_within_daily_band',bool(np.all(x>=flx-1e-10) and np.all(x<=upx+1e-10)))
    check('comp_within_daily_band',bool(np.all(y>=fly-1e-9) and np.all(y<=upy+1e-9)))
    check('all_rate_caps_hold',max(rt.max(),rc.max())<p.rate_cap)
    check('finite_share_inventory',res['max_gross_sold_shares']<2)
    check('crisis_triggered_at_delta015',res['terminal_crisis_functional']>0.015)
    check('target_rate_lower_than_cap',res['gross_rate_target_max']<0.12)
    check('comp_rate_lower_than_cap',res['gross_rate_comp_max']<0.75)
    check('independent_compensator_integration',res['independent_rk4_comp_end_difference']<1e-8)
    check('first_day_target_has_positive_signed_dollars',res['net_dollar_per_target_first_day']>0)
    check('second_day_target_has_negative_signed_dollars',res['net_dollar_per_target_second_day']<0)

    # Exact single-asset minimum cap via saturated comparison solution.
    for s, beta, rho, tau in [(1.,.03,.4,20.),(.97,.03,.4,20.),(.85,.10,.3,3.),(1.2,.10,.4,2.)]:
        r=math.exp(-rho*tau)
        raw=rho*((1.-s)+beta*s/(1.-r))
        v=max(0.,raw)
        z_end=1.+(s-1.)*r-v*(1.-r)/rho
        check(f'scalar_bound_{s}_{beta}_{rho}_{tau}', v==0 or abs(z_end-(1-beta)*s)<2e-13)
    q=.97
    daily=necessary_scalar_speed(.03,20,.4,20.)
    check('daily_scalar_requirements_monotonic_in_example',np.all(np.diff(daily)>0))
    check('global_rate_price_floor',q**20>1-.2/.4)
    check('rate_floor_prevents_30days_for_v02',q**30<1-.2/.4)
    check('streak_bound_D_is_finite',max_streak_scalar(.03,.2,.4)<30)

    # Conditional all-asset two-day obstruction: even when the price band
    # permits day-1 lower-limit closing, day-2 highest executable price is
    # below the unchanged fundamental value.
    for beta in [.01,.03,.1,.18,.3]:
        check(f'symmetric_band_global_obstruction_{beta}',(1+beta)*(1-beta)<1)
    check('breadth_is_9_of_10',p.k/(p.k+1)==.9)
    check('reset_cumulative_log_loss',abs(-math.log(x[-1])-2*(-math.log(.97)))<1e-12)
    check('rate_bound_necessary_day2',p.rate_cap>max(necessary_scalar_speed(.03,2,.4,20.)))

    # Necessary preconditioning bound. In this explicit witness targets remain
    # strictly below F during day 2, so positive recovery integral is only
    # obtained before the first close.
    check('targets_below_fundamental_whole_second_day',np.max(x[t>=p.session])<1.)
    q2=q*q
    rhs=(1-q2*q2)/2
    lhs=p.rho*p.session*((1+p.target_band)*p.target_band)
    check('preconditioning_bound_satisfied',lhs>rhs)

    # Independent check of exact terminal crisis functional.
    L=-np.log(np.r_[np.full(p.k,x[-1]),y[-1]])
    criterion=min(np.mean(L),np.sort(L)[::-1][p.k-1])
    check('crisis_recomputed_from_prices',abs(criterion-res['terminal_crisis_functional'])<2e-12)

    # Exact systemic-trigger product test conditional on k rolling-limit closes.
    lam=-math.log(q); D=2; n=p.k+1; yc=res['comp_closes'][-1]
    for delta in (0.005,0.015,0.019,0.020,0.04):
        product_condition=(yc<=math.exp(p.k*D*lam-n*delta)+1e-13)
        true_crisis=(res['terminal_crisis_functional']>=delta-1e-13)
        check(f'compensator_product_iff_{delta}',product_condition==true_crisis)
    threshold=math.exp(p.k*D*lam-10*.020)
    check('delta002_requires_smaller_compensator',yc>threshold)
    check('equal_q_equals_target_2day_loss',abs(res['terminal_cover_quantile_log_loss']-D*lam)<1e-12)
    # An exact case where k streaks do NOT produce a systemic crisis.
    high_y=math.exp(p.k*D*lam-n*.015)+.02
    A_hi=(p.k*D*lam-math.log(high_y))/n
    check('breadth_alone_not_sufficient',A_hi<.015<D*lam)

    out=Path(__file__).resolve().parents[1]/'verification'
    out.mkdir(exist_ok=True)
    with open(out/'v6_multiday_checks.json','w') as f:json.dump({
        'total_checks':len(checks),'passed_checks':sum(checks.values()),
        'checks':checks,'direct_quadrature_terminal_ledger':direct,
        'parameters':res,'important_scope':'Numerical ODE band checks are not certified interval enclosures.'
    },f,indent=2)
    print('All',len(checks),'multiday checks passed.')

if __name__=='__main__':verify()
