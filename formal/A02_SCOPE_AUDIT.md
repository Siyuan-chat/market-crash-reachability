# A02: Proposition 6.1 scope audit (2026-10-17)

Source: `paper/main.tex:365–395`. No manuscript change is made for A02.
The implementation uses the physical integrable-primitive AC session from
A01. Section 6's finite gross share-rate regime excludes instantaneous
pulses and singular execution; its AC price regularity is derived from
the physical integral law and the cap, not imposed as smoothness.

| Original clause | Lean coverage in `MarketCrash/RateBand.lean` |
| --- | --- |
| General positive response g≤G on the admissible price region | `ACPhysicalSession.rate_floor` uses only g bounded at actually visited prices, a weaker requirement. Asset-specific responses are allowed, so the common-g case is included |
| All t in [0,T], scalar price floor, without a band | `proposition_6_1_rate_only`, first conclusion; uses `rateBand_scalar_floor` and the original physical a.e. ODE |
| a.e. comparison genuinely propagates endpoints | `rateBand_nonnegative_of_derivative_ge_linear` proves local Lipschitz integrating-factor regularity and invokes the already proved Lipschitz FTC. No supplied FTC endpoint equation or everywhere derivative assumption |
| Positive max of band floor and horizon rate floor | `rateBand_max_floor` and `proposition_6_1_rate_band`; beta<1 is the paper's positive lower-band domain |
| Any breadth, any t≤T, actual mean, quantile and crisis | `rateBand_crisis_of_floor`, `proposition_6_1_rate_band`, using `requiredAssetCount = ceil(alpha*N)` and the actual finite-sample coverage quantile |
| Necessary speed for a positive crisis | `proposition_6_1_rate_only`, second conclusion, needs no band; inferred from an actual qualifying asset using the proved quantile semantics |
| Fixed one-session band excludes delta>−log(1−beta) | `rateBand_fixed_band_exclusion` and final clause of `proposition_6_1_rate_band` |
| Hypothetical D-session reset product and log-loss sum | `proposition_6_1_hypothetical_reset`, instantiated with factor d=1−beta d, derives both formulas from the actual finite reference-price recursion, including D=0. Conditions refer only to d<D |

F, rho, G are positive; positivity of G also follows from the original
positive impact at the initial attainable benchmark, so it is not an
additional restriction on a nonempty original market. The theorem does
not require terminal dollar closure or assume sufficient market matching.
Its scalar necessary bounds hold on a larger finite asset class than
the original N≥2 statement. Upper price bands, initial inventory and
no-shorting can be retained by original paths without affecting these
necessary inequalities. Hypothetical proportional resets are not applied
to a fixed-benchmark band regime, and no claim about exchange rules is
needed for these mathematical conclusions.

All three canonical branches (`proposition_6_1_rate_only`,
`proposition_6_1_rate_band`, `proposition_6_1_hypothetical_reset`) are required
for whole-result acceptance. Main-agent targeted Lean 4.19.0 compilation
passed; independent read-only scope review confirmed all original clauses
after removing future-session premises from the reset branch. Project
audit, hashes and same-SHA CI remain distinct gates in the authoritative
completion matrix.

PAPER_ACCEPTED at exact proof commit `de95f967b533794677012281432b401aab4517b3`: [lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011197787)；[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011197718)；[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011197705)；[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39011197714)。Full local build, 245-declaration permitted-axiom audit and 228 release hashes passed; this is the third accepted numbered result.
