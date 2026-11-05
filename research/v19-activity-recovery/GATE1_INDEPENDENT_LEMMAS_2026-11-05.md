# V19 Gate 1 independent analytical audit (2026-11-05)

**Scope: four conditional lemmas; Gate 1 and Gate 2 remain OPEN.** All claims below concern the activity-driven event-completed model, not V16's calendar-time drift. Let `dX_i=Σ_e B_ie dz_e`, `dA_i=Σ_e|B_ie|dz_e`, `dz_e>=0`, positive prices and zero initial dollar ledgers. For power-law response, `dx_i=x_i^(p-1)du_i-K(x_i-1)da_i`. The listed nine-edge signs were independently checked by exact rational formal-series algebra.

## 1. C1 local all-asset fall for N>=3

Define `w_i=∫_1^{x_i}s^(1-p)ds`. Per unit incident edge-dollar amount, `dw_i/da=σ_i-K r_p(w_i)`, `r_p(w)=w+O(w²)`, where σ=+1 for buyer and -1 for seller. For six equal-size z incidences with Σσ=0,

`w(6z)=K z² Σ_{j=1}^6 jσ_j+O(z³)`.

Use nine ordered directed edges `(1→2),(2→3),(3→1),(2→3),(3→1),(1→2),(3→1),(1→2),(2→3)`. The incident sign lists are `(-,+,+,-,+,-)`, `(+,-,-,+,+,-)`, `(+,-,+,-,-,+)`. Each has Σσ=0 and Σ jσ=-1, hence each node ends with `w_i=-K z²+O(z³)<0` at sufficiently small z>0, with exact dollar closure. Edge events are sequential, so C1 is respected. Cover every node for N>3 by concatenating such cycles on triangles (1,2,j). The leading terms add and cross terms are O(z³). All intermediate prices stay positive for sufficiently small z; true seller-side holdings are finite. This is a **local** reachability statement, not arbitrary severity or a specified finite share-rate certificate.

## 2. Two-asset common-clock obstruction

For N=2 every edge incident activity increases both nodes' gross dollar clocks equally, including C0 opposite concurrent flows: `dA_1=dA_2=da`. Let `Φ(S)=∫_F^S u/g(u)du`, `R(S)=S(S-F)/g(S)`, `H=Φ(S_1)+Φ(S_2)`. Pairing yields `dH=-κ(R(S_1)+R(S_2))da`. On the attained positive-price domain, if `e(S)=Sg'(S)/g(S)>=1`, then `Φ''=(1-e)/g<=0` and `(R-Φ)'=(S-F)Φ''`. Integrate from F on both sides to conclude `R<=Φ`. Consequently `dH>=-κH da`, so `H>=0` from H(0)=0. Both prices ending below F would imply H<0, impossible.

If `e>=2`, set q=log(S/F), `G(q)=Φ(F exp(q))`; `G'>0`, `G''=S²[2-e(S)]/g(S)<=0`. Jensen gives `G((q_1+q_2)/2)>=H/2>=0=G(0)`. Thus mean log return >=0 and terminal systemic log-loss statistic cannot be positive. **Only N=2 is proved.**

## 3. All-asset necessary barrier for p<2

For `ν=2-p>0` let `Z=Σ_i x_i^ν`. Under pairing, `dZ=ν K Σ_i x_i^(ν-1)(1-x_i)da_i`. On the strictly positive boundary Z=1 (N>=2), all x_i<1 and the derivative points inward/nonnegative for every admissible gross activity. By the first-exit barrier theorem on compact positive-price regions, `Z>=1` from Z(0)=N. Thus if all N final prices are <=exp(-δ), `δ<=log(N)/(2-p)`. **Necessary only**: neither sharpness nor a time-horizon theorem follows.

## 4. Individual power-law positive floor

On x<1, `du>=-da` gives `dx/da>=K(1-x)-x^(p-1)=:f_-(x)`. For 0<=p<1, `K_c=(2-p)^(2-p)/(1-p)^(1-p)`, from minimizing `x^(p-1)/(1-x)` at `x_*=(1-p)/(2-p)`. For K>=Kc the largest zero of f_- (including the tangent K=Kc case) is an uncrossable downward barrier from x=1. For p=1 and K>1 the floor is 1-1/K. For p>1 and any K>0, f_- decreases strictly from K to -1 on (0,1), giving one positive floor. A floor is a necessary single-asset restriction; its absence does **not** certify the paired terminal-closed severe market construction.

## Exact-coefficient check / limitations

The independent exact-rational script `gate1_formal_coefficients.py` checks 9 edge signs, six-incidence `z²` coefficients, and the two-edge `H_3=-(2/3)K(1-p)z³` coefficient. Formal coefficient checks are not interval root certificates. The remaining V19 open register remains active: `T03 P02 T04 T05 P10 P11 P12 I01 I02 R01 R02 R03 A03 A04 A07`. This note alone does not clear either Gate 1 or Gate 2.
