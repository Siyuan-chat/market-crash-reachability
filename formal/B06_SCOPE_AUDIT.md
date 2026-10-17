# B06: Theorem 7.3 original-scope audit

Source: `paper/main.tex`, `thm:no-second-global`. Candidate canonical theorem
`MarketCrash.theorem_7_3_original` in `MarketCrash/OriginalSecondSession.lean`.

The second session is an arbitrary full-state `OriginalPhysicalReachable`
trace, with asset-specific positive F_i, positive rho_i, and positive
continuous g_i. There is no rate cap, terminal-dollar closure, common impact,
common fundamental, or elasticity hypothesis.

The initial second-session state is q_i F_i, with 0<q_i<1. The entire visited
price band, including every internal pulse price, is bounded above by
(1+beta_i) times that initial price. The original condition
(1+beta_i)q_i≤1 therefore makes every visited price at most F_i.

On a continuous piece the genuine physical normal form makes each recovery
contribution nonnegative; exact paired dollars cancel after summing over
assets. Every original pulse preserves the summed asset-specific coordinate.
Finite trace induction gives H(T2)≥H(T1). Strict monotonicity of each asset's
coordinate would make H(T2)<H(T1) if every terminal price were below its own
initial price. The conclusion therefore excludes all strict declines, and
in particular every second-day lower-limit close.

The proof covers a larger class than a complete bidirectional network and
does not require N≥2 for the sign argument. The positive q_i follows from the
original positive first close. Independent review found no omitted original
quantifier or hidden rate/closure premise.

Status: formal-module full pinned Lean 4.19.0 project build PASS; complete
436-declaration permitted-axiom audit PASS; 255 release SHA-256 entries PASS.
Exact-SHA four-CI remains pending. Not accepted.
