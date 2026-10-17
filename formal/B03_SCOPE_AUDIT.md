# B03: Theorem 3.2 original-scope audit

Source: `paper/main.tex`, `thm:barrier2`. Candidate canonical theorem:
`MarketCrash.theorem_3_2_original`, with
`OriginalPhysicalReachable.actual_crisis_nonpositive_observed`.

Original statement: If e(S)≥2 on the admissible price range, then for every
admissible control, N≥2, alpha∈(0,1] and t∈[0,T], C_alpha(t)≤0.
No strictly positive systemic terminal-crisis threshold can be reached.

The physical class is the same genuine finite continuous-BV/finite-pulse
economic trace audited in B02_SCOPE_AUDIT.md. The proof uses the derived normal
form and actual attained-price IVT; it does not assume a normal-form field or
reset later pieces to F. Elasticity≥2 is required only at this trace's actual
visited prices, a weaker hypothesis than the entire admissible price range.

The potential is nonnegative by the B02 proof with e≥1. The actual log price
is log(S/F), with F exp(log(S/F))=S proved from strict positive prices. Every
radial log price needed by the concavity argument corresponds to an actual
visited level price of this same trace. The radial concavity/Jensen inequality
therefore uses no global elasticity assumption. It forces nonnegative mean
log price, hence nonpositive mean log loss and nonpositive actual systemic
crisis. The public theorem retains k=ceil(alpha*N), all alpha∈(0,1], all
observations including pulse interiors, and every positive threshold delta.

No bandwidth, turnover, rate, curvature beyond the original elasticity, or
extra inventory premise is introduced. The original terminal dollar closure
is retained in the admissible economic path; the stronger barrier does not
need to use it.

Status: formal integration and full Lean 4.19.0 project build PASS; complete 362-declaration permitted-axiom audit PASS; 247 release hashes PASS. Exact-SHA four-CI remains pending. Not accepted.
