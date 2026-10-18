# Continuous power-law response spectrum — analytical audit

## Scope

The V14 working manuscript now discusses the continuation
`g_p(S)=eta*(S/F)^p` from the three representative cases p=0,1,2
to all real p in [0,2]. Theorem 4.1 retains its original three-point
statement and proof. This is an **analytical consequence** of previously
proved local reachability propositions, global elasticity barriers,
and the general resource integrals, **not a new theorem claiming
global unbounded severity for every p<1**.

## Exact formulas

For 0<=p<2,
`-Phi_p(0+) = F^2/[eta*(2-p)]`. At p=2 the value diverges.
For 0<=p<1, `-Psi_p(0+) = F/[eta*(1-p)]`; at p>=1
the zero-price share distance diverges.

Writing L=log(F/S), the inventory potential is

    E_p(F*exp(-L)) = F^2/eta *
       [expm1((p-1)*L)/(p-1) - (1-exp(-(2-p)*L))/(2-p)]

for p in [0,2) other than 1. At p=1 the continuous limit equals
`F^2/eta*(L+exp(-L)-1)`.
Thus for p<1, `E_p(0+)=F^2/[eta*(1-p)*(2-p)]`;
for fixed 1<p<2, `E_p` grows asymptotically like
`F^2*exp((p-1)*L)/[eta*(p-1)]`.

If terminal dollar ledger closes and initial sellable inventory is
bounded by H0, the established bound `E_p(S(T))<=F*H0`
yields for 1<p<2 the explicit inequality

    L <= log(1+(p-1)*(eta*H0/F+1/(2-p)))/(p-1).

For p=1, L<=1+eta*H0/F follows from the known E1 expression.
These are necessary severity ceilings, not optimized maxima.

## Reachability classification and logical boundary

- p in [0,1): Proposition 4.2 (three-pulse, e(F)<1) proves a
  **small** terminally dollar-closed simultaneous decline of all assets.
  Resource integrals to zero are finite, but **finiteness alone
  does not establish uniform-budget arbitrarily severe losses**.
  Theorem 4.1(C)'s global severe-loss construction is proven for p=0.
- p=1: Theorem 3.1 globally excludes simultaneous declines;
  Proposition 4.3 allows a small partial-coverage crisis for any T>0.
  Inventory potential diverges linearly in log severity.
- 1<p<2: all-asset simultaneous decline excluded; Proposition 4.3
  supports small partial-coverage loss when exp(-rho*T)<2-p.
  The sufficient horizon grows without bound as p approaches 2.
  Initial share inventory bounds severity logarithmically in H0
  for any fixed p strictly above 1.
- p=2: Theorem 3.2 excludes a positive systemic-crisis functional
  at any horizon. It does not assert that each asset cannot fall.

The thresholds at p=1 (all-asset reachability and share/inventory
singularity) and p=2 (systemic exclusion and dollar-distance
singularity) are precise for the stated deterministic model.
They must not be interpreted as empirical universal market
phase transitions or as finite-rate feasibility statements.

## Verification gates

`scripts/check_v14_resource_bound.py` preserves original V13
19 mathematical statements and 81 numbered equations, plus only
the previously-added V14 Proposition 5.2 and two numbered equations.
It also checks the new discussion's local-horizon condition and
performs independent Simpson numerical quadrature against the
closed-form inventory-potential formulas for representative
exponents. These checks complement—but do not replace—formal
mathematical proof and journal review.
