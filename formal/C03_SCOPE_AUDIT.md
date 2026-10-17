# C03: Theorem 6.3 original-scope audit

Source: `paper/main.tex:441`, `thm:finite-rate-construct`, and the analytic
bounded-control appendix. Canonical theorem: `theorem_6_3_original`;
quantified common-constant family: `theorem_6_3_original_family`.

| Original obligation | Proof correspondence |
|---|---|
| Every finite N≥2, T>0, v>0, positive band widths and positive initial shares | The canonical theorem quantifies all these parameters and an arbitrary vector H with every H_i>0. A finite minimum is derived from H, not assumed uniformly over changing H. |
| Only locally C³ response, g(F)>0 and elasticity e(F)<1 | A genuine positive local response strip and bounded globally Lipschitz clamped field are derived. Picard–Lindelöf constructs the actual three-bin nonlinear ODE solution. A real O(p³) residual comparison first keeps the solution in the strip, then removes the clamp. No parameter-flow expansion, FTC or endpoint equation is assumed. |
| Exact first-order cancellation and negative second-order endpoint | The same three-bin signal has exact unweighted and exponentially weighted zero integrals. Its integral-defined linear response has y(0)=y(T)=0. Lipschitz FTC and integration by parts give the strictly positive weighted energy and negative second response. The true nonlinear endpoint is below F by a common positive quadratic amount. |
| Actual absolutely continuous paired execution and before-net gross cap | Nonnegative complete directed edge rates realize the signed dollars exactly. Their actual cumulative integrals are globally Lipschitz monotone Stieltjes functions. The gross incident share rate is bounded before netting; the common family exposes cap C*a as well as the prescribed cap v. |
| Same control carries inventory, closure and cap | `RealizesACSession m P` explicitly identifies the same physical BV piece, full initial/terminal states, single continuous Type-valued trace, prices/parameters/time, cumulative executed-dollar increments and a.e. density of every edge with m. The cap is not attached to an unrelated session with merely the same terminal prices. |
| Arbitrary positive inventory and no shorts | Actual shares are H_i plus the integral of actual signed shares. A derived Lipschitz bound and a sufficiently small amplitude give nonnegativity for every physical time. The initial holding vector is exactly H. |
| Per-asset terminal dollars and strict price bands | The genuine edge-dollar primitives give every terminal ledger exactly zero. Every price visited by the actual trace lies strictly between F(1−βminus) and F(1+βplus), including bin boundaries. |
| Every terminal price below F, true C_1>0, arbitrarily small loss | Uniform positive individual log losses imply the true full-coverage quantile and mean bounds. For every ζ>0 the canonical witness has 0<C_1(T)<ζ. |

The full proof preserves finite original execution and uses no instantaneous
pulses for this witness. The common epsilon and positive c,C,D are chosen
before the amplitude; they support the subsequent attained-order theorem.
The main agent checked the complete manuscript statement and the explicit
physical-realization relation before integration.

C03 Theorem 6.3 PAPER_ACCEPTED；证明 SHA `937f8d2e1bb5a2556abeb793ab6aaca723b5ddf5`；本地完整构建、593项公理审计及269项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658676)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658720)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658705)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658632)。
