import numpy as np
from scipy.integrate import solve_ivp
from scipy.optimize import minimize_scalar
h=1.02020225507906
knots_t=np.array([0,2.3,17.7,20,22.3,37.7,40.0])
knots_x=np.array([1,h,h,.97,.995,.995,.9409])
rho=.4

def point(t):
    j=min(np.searchsorted(knots_t,t,side='right')-1,5)
    slope=(knots_x[j+1]-knots_x[j])/(knots_t[j+1]-knots_t[j]); x=knots_x[j]+slope*(t-knots_t[j]);u=x*(slope+rho*(x-1));return float(x),float(u)

def get_stats(k,m):
    ratio=k/m
    def rhs(t,y): return -rho*(y[0]-1)-ratio*point(t)[1]/y[0]
    all_times=[]; ys=[]
    y=[1.0]
    for i in range(6):
        tt=np.linspace(knots_t[i],knots_t[i+1],2001)
        sol=solve_ivp(rhs,(knots_t[i],knots_t[i+1]),y,t_eval=tt,rtol=2e-12,atol=2e-13,max_step=.01)
        if not sol.success:return {'k':k,'m':m,'fail':sol.message}
        all_times.extend(tt[1:] if i>0 else tt)
        ys.extend(sol.y[0][1:] if i>0 else sol.y[0]);y=[sol.y[0][-1]]
    all_times=np.array(all_times); ys=np.array(ys)
    day1=all_times<=20;day2=all_times>=20
    y20=ys[np.argmin(abs(all_times-20))]
    gross=np.array([abs(ratio*point(t)[1])/yy for t,yy in zip(all_times,ys)])
    loss=(-k*np.log(.9409)-m*np.log(ys[-1]))/(k+m)
    breadth=(k/(k+m))
    # day1 limits around F=1; day2 around y20
    beta_needed=max(1-ys[day1].min(),ys[day1].max()-1,1-ys[day2].min()/y20,ys[day2].max()/y20-1)
    return {'k':k,'m':m,'y20':y20,'y40':ys[-1],'day1min':ys[day1].min(),'day1max':ys[day1].max(),'day2min':ys[day2].min(),'day2max':ys[day2].max(),'max_rate_comp':gross.max(),'required_band_for_fixed_path':beta_needed,'mean_loss':loss,'max_price_end':max(.9409,ys[-1]),'crisis_threshold_002':bool(loss>=.02)}
if __name__=='__main__':
    import json
    for k in [6,7,8,9]:print(json.dumps(get_stats(k,10-k),indent=2))
