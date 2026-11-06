# Gate 3 mathematical audit — time reparameterization resolves T05 in the activity-only model

Date: 2026-11-06. Scope: absolutely continuous nonnegative paired-dollar edge rates, fixed response function and parameters, strictly positive price path on an arbitrary finite interval, with no fixed rate cap or imposed session-clock schedule.

## New exact statement

If an endpoint state is reachable at any positive physical duration T, it is reachable at every T'>0 by a positive time change. Define lambda=T/T' and transform every edge by z'_e(t)=lambda*z_e'(lambda*t). Then, with Snew(t)=S(lambda*t), Xnew(t)=X(lambda*t), and Anew(t)=A(lambda*t), every term of the event-completed differential law transforms by the same lambda, so the ODE and nonnegative edge constraints remain satisfied. C0 and C1 have the same instantaneous buyer/seller signs and sequencing; final prices, the individual executed-dollar ledgers, total paired-dollar turnover and actual seller-side share inventory are invariant under the change of integration variable.

In contrast, gross share execution rates scale by lambda. Therefore the same argument **does not** prove attainability on every horizon if a gross-share rate limit v is fixed, or if trading-session boundaries and explicit calendar restrictions are held fixed.

This proves that a **positive physical-time critical horizon from the old free-recovery V16 theorem cannot transfer** into the activity-clock model without additional rate/calendar hypotheses. It does not by itself prove any terminal all-asset loss state reachable; all-coverage amplitude sharpness belongs to the separate A04 research obligation.

## Gate 3 traceability

- `T05` now has an exact paper proposition `prop:time-change`, proof and source-side audit; manuscript status changes from `partial_open` to `drafted`.
- `A04` remains `partial_open` because sharp all-coverage **loss severity** is not obtained from time changes.
- `T08`, `P10`, `R03` retain fixed-speed or rolling-band hypotheses as appropriate; the new theorem must not be used to bypass a rate cap or session length.
- Original 43 IDs and original 40-page scientific questions are all preserved; no old theorem is silently deleted.

**Evidence level:** independent elementary analytic change-of-variable argument, not Lean kernel certification or external peer review. Gate 3 overall remains WIP.
