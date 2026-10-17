# C06: Theorem 4.1 original-scope audit

Source: paper/main.tex, thm:ABC and app:severe. Canonical full-result
theorem: `theorem_4_1_original`; severe branch:
`theorem_4_1_C_original`.

| Original obligation | Proof correspondence |
|---|---|
| Same original market protocol, every finite N>=2 | The three responses are exactly constantResponse, linearResponse and quadraticResponse, representing eta*(S/F)^p for p=0,1,2. Every witness is an OriginalAdmissiblePhysicalPath with original marginal share/price/dollar primitives, positive visited prices, no shorts and terminal per-asset cash closure. |
| A: all paths, all horizons, all actual observations | OriginalABCBarrier quantifies arbitrary finite paired networks, every original BV/pulse path and all observations including within pulse execution. The existing full quadratic-response barrier supplies C_alpha<=0 for every valid breadth. |
| B: actual small positive partial crises | For every positive horizon and every zeta>0 the two-pulse construction gives an actual closed physical path with 0<C_alpha<zeta, for every valid k=ceil(alpha*N)<N. No fixed inventory cap is added to this existence premise. |
| B: any fixed finite starting inventory cap | Separately, for every fixed H0 and every original admissible linear-response path with initial shares<=H0, true inventory accounting and the exact linear cost potential give every individual terminal log loss and the actual crisis <=1+eta*H0/F. This is independent of the trade sequence and horizon. |
| C: fixed time and budgets before delta | OriginalABCSevere chooses finite T>0,M0>=0,H0>0 before k and delta. The same constants work for every 1<=k<N and every finite delta>0. It bounds actual paired turnover, actual Jordan negative share variation, and even initial shares by H0. There is no uniform claim as N changes. |
| Exact compensator closure | A genuine recovery integral has a proved explicit primitive. With fixed c=1/(100*N), the compensator ledger at b=0 is positive for all sufficiently small epsilon; at beta=1/5 it is negative for one fixed sufficiently long finite T, uniformly in epsilon. Continuity and the intermediate value theorem give an exact interior root for every small epsilon. No numerical root or terminal identity is assumed. |
| Closing all targets on the same trace | Every target is high in one of N-1 actual radial stages and low otherwise. A positive W primitive gives a true equal-integral time partition. Finite ordered positive-price pulses implement all reorientations. Actual per-asset recovery normal forms give equal target terminal cash; the compensator root and dollar pairing then force every cash ledger to vanish exactly. |
| Resources independent of epsilon, same actual execution | Ordered squared-price transport exposes the actual finite single-edge schedule and proves turnover<=2*N*X and each actual share-sales<=2*N*sqrt(2*eta*X)/eta. Actual radial edge cumulative integrals give a uniform total-dollar-rate bound, while the true signed-share rate is constant. The same raw piece is rebased to shares=1+V*T+q_i*t, with full original share primitive reproved, no shorts and shares<=1+2*V*T. Thus no 1/min(price) inventory reserve enters the final family. |
| Full economic joins preserve budgets | Explicit nonnegative stock lifts and cash translations match every full economic state. Negative variation and actual turnover are proved invariant under these translations and additive under finite trace concatenation. Exact max-formulas for the stock lifts bound all initial inventories uniformly. Resource bounds travel with the same actual trace through the finite-stage induction. |
| Arbitrarily severe actual crisis, not just small target prices | For every delta>0 a sufficiently small positive epsilon makes both the actual mean log loss and the k-th coverage quantile exceed delta; the compensator is bounded above by F*sqrt(N). This proved endpoint criterion is applied to the same uniformly bounded closed physical family. |

The severe family chooses all resource constants before epsilon. The final
canonical theorem combines the independently verified A/B branches with
this family; it does not take any reachability, expansion, normal-form or
resource assumption as a new premise. Extra isotropic transport stops are
finite legal zero-time pulses; their actual resource costs are included.
The constants are deliberately loose and are not an optimization claim.
In particular, this alternative finite construction proves the numbered
theorem's existential uniform budgets; it does not claim kernel
certification of the particular displayed appendix budget formulas.
Independent manuscript-versus-canonical review found no missing numbered
theorem clause or quantifier.

C06 Theorem 4.1 PAPER_ACCEPTED；证明 SHA `37e9c89c106cd85735ff2a500a922f32802f8d15`；本地完整构建、787项公理审计及291项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946468)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946511)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946465)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946461)。
