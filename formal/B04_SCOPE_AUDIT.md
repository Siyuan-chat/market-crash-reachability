# B04: Theorem 5.1 original-scope audit

Source: `paper/main.tex`, `thm:resource`, resource-lower and share-bound.
Canonical full-result candidate: `MarketCrash.theorem_5_1_original`.

The proof takes the genuine original finite economic trace, actual terminal
log prices, alpha∈(0,1], delta>0, k=ceil(alpha*N), and C_alpha(T)≥delta.
The actual threshold equivalence supplies at least k qualifying assets with
S_i(T)≤F exp(-delta). No assumed resource budget or hypothetical endpoint
configuration substitutes for the physical path.

| Original clause | Physical derivation |
| --- | --- |
| M≥k integral_s^F u/g(u) du | A last-zero Lipschitz FTC argument charges coordinate losses to the Jordan negative variation of each actual dollar ledger. A monotone control dominates each ledger's total variation. Summing over assets uses exact zero-sum ledgers and absolute incidence-column sum two, giving total negative cash variation≤paired turnover, counted once. |
| Sum H_i^-≥k integral_s^F 1/g(u) du | The share-response coordinate Psi is differentiated along the actual operational projection derived from the raw BV primitives. Recovery points inward whenever Psi<0. Last-zero FTC bounds the loss by the actual shares' negative variation. |
| Actual H_i^-, including netting | `actualNegativeVariation` is (total variation−net increment)/2, the real Jordan negative variation. Its equality under the genuine monotone inverse clock and its adjacent-interval additivity are proved. Finite trace sums include the actual pulse-parameter variation. Simultaneous buys and sells are netted; the proof does not replace this by larger gross edge sales. |
| Inventory condition for every qualifying asset | E=Phi−F Psi has derivative (S−F)/g(S). The genuine physical cost F theta+E−X is nonincreasing on continuous BV pieces and preserved in every pulse. Terminal X=0 and no short sales imply E(S_i(T))≤F theta_i(0)≤F H_i. Monotonicity below F yields the stated integral at s. |
| Original controls and budgets | Continuous singular-BV control and every finite pulse are included; shares, prices and cash join at all steps. The inventory conclusion is per qualifying asset with arbitrary admissible initial cap H_i, rather than an aggregate or average cap. |

The coordinate and inventory statements need only positive continuous g,
weaker than the manuscript's locally C² response. No curvature, rate cap,
price band, sufficiency, or closure of shares is added.

Status: all three clauses combined in one canonical theorem; formal integration
and full Lean 4.19.0 project build PASS; all 413 project declarations audited
with standard axioms only; 251 release SHA-256 entries PASS. B04 Theorem 5.1 PAPER_ACCEPTED；证明 SHA `a1415e9745b65581a3c3053cc45be56c3763181c`；本地全量构建、413项公理审计及251项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767964)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767913)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768014)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768057)。
