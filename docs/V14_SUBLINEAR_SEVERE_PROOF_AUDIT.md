# Uniform-budget severe drawdowns for every fixed 0 <= p < 1

This file audits the NEW V14 theorem thm:sublinear-severe.
It complements, and does not alter, Theorem 4.1(C)'s original p=0 result.

## Exact theorem scope

For each fixed exponent p in [0,1), N>=2, k=ceil(alpha*N)<N,
and positive F, eta, rho, there are ONE finite T, ONE finite total
paired-dollar turnover bound M0, and ONE finite per-asset sale-share
bound H0, independent of the target logarithmic loss threshold.
Every selected path uses strictly positive prices, finitely many
flow-completed instantaneous pulses plus absolutely continuous
paired-dollar trading, a complete bidirectional matching network,
and each asset's terminal executed-dollar ledger closes to zero.

The result does not assert uniform bounds as p tends to 1, finite
gross-rate feasibility, a market calibration, or a crisis probability.

## Generalized radial identity

Put nu=2-p in (1,2]. For a direction u with sum_i u_i^nu=1,
write H=sum_i u_i^(nu-1), S_i(t)=u_i R(t). Then

    R(t)=F*[H+(N^(1/nu)-H)*exp(-rho*t)]
    dot X_i=(rho*F^(p+1)/eta)*R^(nu-1)*u_i^(nu-1)*(H*u_i-1).

Dollar pairing follows from sum_i u_i^nu=1 and the definition of H.
Holder implies 1<=H<=N^(1/nu), whence F<=R<=F*N^(1/nu).
Paired pulses preserve sum_i S_i^nu and can interpolate all
positive power coordinates monotonically.

## Closing ALL terminal dollar accounts

Use m=N-1 target directions with one high weight a, remaining
low weights c, and one compensator weight b. The same H_b
applies to all m stages. The compensator ledger is

    F_eps(b) =
      F^p/(eta*nu)*(R_b(T)^nu-m*eps^nu-F^nu)
      + rho*F^p/eta*int_0^T (bR_b)^(nu-1)*(bR_b-F)dt.

For b=0 its continuous extension is positive at eps=0.
This requires nu-1>0. At bbar=1/5 the long-horizon
recovery term is negative, so choose one large finite T
making F_0(bbar)<0. Continuity fixes bminus>0 and permits
b_eps in (bminus,bbar) for all small eps, closing the
compensator's dollar ledger.

The high-minus-low target restoring difference equals

    W=R^(nu-1)*[(a^nu-c^nu)*R-F*(a^(nu-1)-c^(nu-1))],

which is positive by aH>1, cH<1, and R>=F*H.
Partition [0,T] into m successive equal-W-integral stages.
All targets have the same terminal price eps and identical
recovery integrals, and hence equal dollar ledgers. Their
sum vanishes because the compensator is already closed
and every execution is zero-sum. Thus EVERY X_i(T)=0.

## Uniform finite resources

The path has N pulses. Each pulse costs no more than
N^2*F^2/(2*eta*nu). Controlled stages have turnover rate
bounded above by rho*N*F^2/eta. One valid total bound is

    M0=N^3*F^2/(2*eta*nu)+rho*N*F^2*T/eta.

Pulse share changes obey

    dtheta_i=(F^p/eta)*S_i^(-p)*dS_i.

Since p<1, integrating down to an arbitrarily small
positive endpoint yields a finite total share change.
With dstar=min(c,bminus)>0 and N pulses, a valid per-asset
sales bound independent of eps is

    H0=N*F*N^((nu-1)/nu)/(eta*(nu-1))
       +rho*F*T*dstar^(-p)*(1+N^(1/nu))/eta.

The compensator terminal price is bounded by F*N^(1/nu).
The m target log losses grow like log(F/eps), so the
k-th largest and mean log losses tend to +infinity
for k<=m. All constants remain fixed as eps decreases.

## Independent numeric checks and verification scope

scripts/check_sublinear_severe_extension.py is a stdlib-only
floating-point cross-check for p=0, .25, .5, .75 and .9
with two target terminal prices at N=3. Its ledger residuals
check the pairing/closure derivation; they are NOT a rigorous
existence certificate or replacement for the analytic proof.

A separate high-precision exploratory calculation at p=.975
produced a very small compensator weight (approximately
3.95e-40) and near-zero individual ledger residuals.
It illustrates worsening numerical conditioning near p=1,
not a claim of universal resource constants.

The new V14 theorem has NOT been independently Lean-verified.
Historical published V13 and its formalization and numerical
certificates are preserved. The original 19 mathematical statements
and 81 numbered equations are retained. V14 now contains the
extra turnover-dissipation Proposition and this theorem,
and five additional labelled equations in total.
