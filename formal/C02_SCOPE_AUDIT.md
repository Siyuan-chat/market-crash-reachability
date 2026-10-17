# C02: Proposition 4.3 original-scope audit

Source: `paper/main.tex`, `prop:two-pulse` and Appendix local expansions.
Canonical full-result theorem: `proposition_4_3_original`.

The theorem takes any selected zero-sum direction u with at least k positive
components, not just an existential special hub vector. It retains N≥2,
alpha∈(0,1], k=ceil(alpha*N)<N, positive F/rho/T, response locally C³,
e(F)<2, and r=exp(−rho*T)<2−e(F).

`two_pulse_original_path` realizes h*u and −h*u as finite ordered original
single-edge pulses on the complete bidirectional graph. Its middle segment
is the real no-trading recovery equation. The generic three-vector physical
construction is specialized with third input zero and second recovery of
zero duration. The extra chart-domain check proves the resulting true
inverse identity, so no global R(Phi(S)) premise is assumed. The resulting
admissible economic path has strictly positive prices, finite inventory,
no short sales, exact state joins and zero dollars for each terminal asset.

The genuine pulse endpoint is R(Phi(F+r*(R(h*u_i)−F))−h*u_i). Differentiating
the actual inverse, coordinate and log maps yields individual first loss
derivative c*(1−r)*u_i and second derivative
c²*(1−r)*(2−e(F)−r)*u_i². Finite summation uses sum u=0. The canonical
theorem gives the exact original mean-loss coefficient
c²*(1−r)*(2−e(F)−r)*sum u_i²/(2N) and one uniform C*h³ remainder bound
for the actual constructed terminal mean loss.

The positive coefficient gives a positive mean for all sufficiently small
h>0; every u_i>0 gives a strictly positive actual individual log loss.
The exact coverage-quantile threshold theorem then supplies positive Q and
positive actual C_alpha, rather than merely a favorable expansion coefficient.

Independent review checked the arbitrary-u quantifier, the degenerate
three-vector specialization, complete-network embedding, exact dollar
closure, no-short constraints and real crisis semantics. No omissions found.

C02 Proposition 4.3 PAPER_ACCEPTED；证明 SHA `e28dc8bb9eb415be3974a947aae7e4bc6361c7d3`；本地全量构建、502项公理审计和266项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534598)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534620)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534597)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534616)。
