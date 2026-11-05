# Gate 1 / P02: two-asset small-budget obstruction, 1<p<2 (2026-11-05)

**Internally proved conditional theorem; no global P02 or full Gate 1/2 clearance.**

Fix N=2, 1<p<2, K>0, normalized x_i(0)=1, strictly positive event-completed activity-driven trajectories in C0 (thus also C1), and exact per-node terminal dollar closure. There is an epsilon(p,K)>0 so that if the *total paired gross dollar amount* A<epsilon, then (log x_1(T)+log x_2(T))/2 >=0; hence the terminal C_(1/2) cannot be positive. This is an exclusion **for sufficiently small turnover only**.

## Proof

Put nu=2-p in (0,1), w_i=(x_i^nu-1)/nu. Every edge hits both nodes, hence they share the common gross-activity clock a in [0,A]. The activity ODE is w_i'=sigma_i-K r(w_i), where |sigma_i|<=1, sigma_1+sigma_2=0, and r(w)=x^(nu-1)(x-1)=w-(p-1)w²/2+O(w³). Individual terminal dollar closure gives integral_0^A sigma_i da=0.

Let b(w)=w-r(w). For a sufficiently small fixed neighborhood |w|<=r0, choose c,L,C>0 such that b(w)>=c w², |r(w)|<=L|w|, and ell(w):=log(x)=log(1+nu*w)/nu >=w-Cw². These follow from b(w)=(p-1)w²/2+O(w³), r'(0)=1, ell'(0)=1, ell''(0)=-nu.

Set H=w_1+w_2. Because the paired sigma values cancel,

H'=-K H+K (b(w_1)+b(w_2)),
H(A)=K integral_0^A exp[-K(A-s)] Σ_i b(w_i(s)) ds.          (1)

All admissible controls remain inside |w|<=r0 for sufficiently small A: Gronwall gives |w_i(a)|<=a exp(K L a), up to first exit, and choosing epsilon exp(KL epsilon)<r0 excludes an exit. With J=integral_0^A Σ_i w_i(s)^2 ds, (1) yields

H(A)>=K c exp(-K A) J.                                     (2)

Integrating the individual w equations and using terminal X_i=0,

w_i(A)=-K integral_0^A r(w_i(s))ds.

Cauchy–Schwarz gives Σ_i w_i(A)^2<=K² L² A J. Consequently

Σ_i log x_i(A)>=H(A)-C Σ_i w_i(A)^2
              >=K[c exp(-K A)-C K L² A] J.                 (3)

Decrease epsilon so that C K L² epsilon < c exp(-K epsilon). The bracket remains positive throughout (0,epsilon], hence the terminal mean log return is nonnegative; it is strictly positive unless the price trajectory is identically at benchmark. QED.

## Classification boundary / acceptance

Previous two-event local expansion for p<1 yields C_(1/2)>0 with mean log loss K(1-p) z³/3+O(z⁴)>0; p=1 follows from H=0 and strict AM–GM. The present result excludes positive C_(1/2) for all sufficiently small A when 1<p<2; p>=2 has the established global two-node obstruction. This completes the **infinitesimal turnover classification**, but does not decide reachability at larger finite turnover for 1<p<2, the sharp minimal amount, or the global P02 acceptance item. Preserve P02 as partially open and all 43 traceability IDs.

**Evidence:** analytic proof under the stated hypotheses; not an independent numerical/interval certificate nor external peer review.
