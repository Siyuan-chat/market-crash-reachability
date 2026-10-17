# C05: Theorem 4.4 original-scope audit

Source: paper/main.tex, thm:critical and app:sharp. Canonical theorem:
`theorem_4_4_original`; explicit finite-resource sibling:
`theorem_4_4_original_finite_resources`.

| Original obligation | Proof correspondence |
|---|---|
| Arbitrary finite N>=2, positive F,rho,eta,T | All parameters are quantified before delta. The actual critical value is proved positive. |
| Every original admissible positive-price BV/pulse path | The strict upper bound accepts any finite paired network. The raw-trace theorem is stronger: it does not need terminal dollar closure. Actual primitive equations give a continuously differentiable total squared radius despite singular individual controls. The positive-price strict L1/radius inequality forces strict growth of the integrating factor over every positive physical-time interval; pulses preserve radius. Finite-trace induction includes zero-duration continuous pieces. |
| Exact critical threshold | The bound is exactly log(sqrt(N)/(1+(sqrt(N)-1)*exp(-rho*T))). The helper names originalSharpCriticalLoss and sharpCriticalLoss unfold to the identical expression. |
| Every 0<delta<critical has an actual control | A continuous parameter argument chooses positive low direction b. Each radial piece is constructed from nonnegative complete directed edge rates and true cumulative Stieltjes integrals, with actual no-short shares. It is restricted to the actual stage times. |
| Actual finite positive-price reorientations | A donor-then-receiver star schedule transports positive squared coordinates of equal sum. Every ordered single-edge prefix is proved positive. These are actual original pulses, not simultaneous vector jumps or an assumed endpoint relation. |
| Equal recovery weights and all cash ledgers zero | A strictly monotone genuine primitive of positive W yields a finite equal-integral partition. The finite physical trace assigns each asset exactly one high stage. Every zero-time transport contributes zero recovery integral. The actual normal form and paired-dollar sum then imply each final cash ledger is exactly zero. |
| Full economic state joins and no shorts | Finite concatenation matches time, price, shares and cash by explicit nonnegative share lifts and cash translations. Initial cash remains zero. The construction gives an actual OriginalAdmissiblePhysicalPath with all inventories nonnegative. |
| Finite turnover and sufficiently large finite inventory | The same finite trace exposes a finite paired-turnover cap and finite initial-inventory cap; the sibling also exposes a finite cap on actual cumulative net share sales, rather than substituting an edge-gross quantity. These caps may depend on delta, as allowed here. |
| True full-coverage crisis and unattained supremum | All terminal prices equal F*exp(-delta), hence the actual full-coverage crisis is at least delta. The actual feasible severity set is nonempty and bounded above; its real supremum equals critical. The universal strict bound excludes the critical value and every larger threshold. |

The main agent compared the complete original theorem and construction
appendix against the canonical theorem and its actual economic witness.
Additional zero-time isotropic transport stops simplify full-state joins;
they are finitely many legal original pulses and preserve every recovery
integral. No extra restriction is imposed on the universal path class.

Status: LEAN_PASS, pending exact proof-SHA four-CI. Full pinned Lean 4.19.0
integration build PASS (build/formal/c05-full-build/result.json, stdout
SHA-256 f5c699cf62a814355f3d7185762c3e9f0d94de55e0e0bfc3782edc76f403fbd3).
All 695 registered declarations pass the complete permitted-axiom audit:
build/formal/c05-integrity/result.json, stdout SHA-256
1b53245991d028a503769f5e2b8479162906058d9a380e054a169ea3e555ace2.
Only propext, Classical.choice and Quot.sound occur. Release hashes cover
281 artifacts. Full original-scope review completed. Not yet paper-accepted.
