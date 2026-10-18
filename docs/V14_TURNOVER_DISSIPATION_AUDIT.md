# V14 research result: proof and scope audit

**Origin:** The phase-5 resource screening note (18 October 2026),
independently rederived before manuscript inclusion.

## Assumptions

For each asset: S_i(0)=F>0, g(S)=eta>0, common rho>0.
Controls are absolutely continuous; executed-dollar rates q_i=dot X_i
arise from nonnegative paired edge rates dot z_e, satisfying
sum_i q_i=0. Define M(t)=sum_e integral_0^t dot z_e.
Assume the whole positive-price path obeys S_i(t)>=a>0 and
|S_i(t)-F|<=b. Terminal dollar-ledger closure is not required.

## Derivation

Let x_i=S_i-F and V_2=0.5 sum_i(S_i^2-F^2).
Then dV_2/dt=-rho[V_2+0.5 sum_i x_i^2] by pairing.
Integrating V_2(0)=0 gives
-V_2(T)=(rho/2) int_0^T exp[-rho(T-t)] sum_i x_i(t)^2 dt.

Variation of constants in
dx_i/dt=-rho x_i+eta q_i/S_i
implies sum_i |x_i(t)| <= (eta/a)int_0^t
exp[-rho(t-u)]sum_i |q_i(u)|du.

**Corrected net/gross accounting:** sum_i |q_i(u)| <= 2 dot M(u),
and equality is NOT guaranteed with crossed flows at one node.
Using x_i^2<=b|x_i|, Tonelli, and max_{z>=0} rho*z*exp(-rho*z)
= exp(-1), yields

    -V_2(T) <= (rho*eta*b/a) int_0^T (T-u)exp[-rho(T-u)]dot M(u) du
             <= (eta*b/(a*exp(1))) M(T).

For each of two hypothetical sessions with uniform +/-25% reset bands,
F*9/16 <= S_i(t) <= F*25/16, hence a=b=F*9/16.
With eta=1, -V_2(T)<=M(T)/exp(1).

For 10/10 assets S_i(T)<=0.98F and F=eta=1:
-V_2(T)>=0.198; M(T)>=0.198*exp(1)=0.5382198020...
The M<=3 original resource budget is not excluded.

The 70%/20% and 90%/10% **partial coverage** cases are NOT given
M>=exp(1)*k(d-d^2/2), because compensators may push V_2(T) toward zero.
Existing coordinate-distance requirements M>=1.26 and M>=0.855 are
from the older Theorem 5.1, not the new aggregate inequality.

### Research status

The derived inequalities are necessary and conservative; their
constant is not shown optimal. No globally optimized control or
new interval-certified numerical witness is asserted. The original
19 numbered statements and 81 numbered equations are carried over from
V13 without modification. New proof material is unnumbered to preserve
the original formalization map. Not independently Lean-formalized.
