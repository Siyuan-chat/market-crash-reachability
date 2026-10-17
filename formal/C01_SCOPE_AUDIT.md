# C01: Proposition 4.2 original-scope audit

Source: `paper/main.tex`, `prop:three-pulse` and Appendix local expansions.
Full canonical family: `proposition_4_2_original_uniform`,
`proposition_4_2_original`, `original_three_pulse_from_chart`.

| Original obligation | Candidate proof |
| --- | --- |
| Every N≥2, positive F/rho/T, locally C³ g with e(F)<1 | Arbitrary finite asset type, positive benchmark/resilience/horizon, true `ContDiffAt` response near F and the actual derivative elasticity. No global curvature or impact bound. |
| Actual response flow | The inverse function theorem is applied to the genuine Phi integral. The resulting local inverse is positive, truly inverse and has derivative g(R)/R. Its first/second jets and C³ Taylor remainder are derived. No response-coordinate identity is assumed as a replacement physical law. |
| Zero-sum u, every component nonzero | An explicit hub vector has value 1 off the hub and 1−N at the hub. Its sum is zero and all entries are nonzero for N≥2. The sibling theorem also covers any selected all-nonzero zero-sum direction. |
| Three vector impulses h*u, −(1+r)h*u, r*h*u | Nonnegative directed dollar amounts realize each vector on a star, then embed exactly into the complete bidirectional network. Each vector impulse is expanded into a finite ordered list of original single-edge pulses, with every intermediate price positive. |
| Full economic trace, closure and inventory | Single-edge physical price/share/cash ODEs generate original pulses. A shared share primitive maintains exact economic joins. Two genuine zero-trading recovery pieces are inserted at 0,T/2,T. Inventory offsets are chosen finite and uniformly sufficient; every asset has no short sales and exactly zero terminal dollars. |
| Exact original coefficient | The true composed pulse/recovery map has loss second derivative (1−e(F))*c²*r*(1−r²)*u_i² and vanishing first derivative, with c=g(F)/F² and r=exp(−rho*T/2). Its Taylor coefficient is exactly half of that second derivative. |
| Uniform cubic remainder | `finite_cubic_remainders_uniform` chooses one positive neighborhood and one finite constant for every asset. `proposition_4_2_original_uniform` combines this with the complete physical construction. |
| Actual all-asset decline and crisis | The coefficient is strictly positive; the cubic remainder gives strictly positive actual log losses for all sufficiently small h>0. Positive terminal prices then imply each S_i(T)<F. The true full-coverage order statistic and mean give C_1(T)>0. |

The construction uses original ordered single-edge pulses rather than relying
on an enlarged simultaneous-vector pulse class. All source quantifiers and
the physical inventory, time, complete-network and closure constraints were
reviewed independently by the main agent. Shared two-pulse scalar helpers do
not count as Proposition 4.3 acceptance.

C01 Proposition 4.2 PAPER_ACCEPTED；证明 SHA `c58a3287c94d3bcc56386a7715657fad489ec8be`；本地全量构建、500项公理审计和264项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791535)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791496)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791519)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791505)。
