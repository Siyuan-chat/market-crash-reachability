# V19 Gate 2: exact inverse bounds for role-stage Jacobians and uniform root continuation

**Analytic sublemma, 2026-11-05. Gates 1/2 remain OPEN; cached numerical roots remain uncertified.**

## Exact discrete Green matrix

For m role stages let L_(m-1) be the Dirichlet tridiagonal matrix with 2 on the diagonal and -1 on adjacent diagonals. Its inverse has exact entries

`(L^(-1))_(ij) = min(i,j)*(m-max(i,j))/m, 1<=i,j<=m-1`.

Taking second differences proves this formula. Summing a row gives `i*(m-i)/2`, so
- m=9 (nine targets in Construction II): `||L_8^(-1)||_inf=10`.
- m=10 (ten equal roles in Construction I): `||L_9^(-1)||_inf=25/2`.

At sharp role cuts the adjacent-account Jacobian is `J_0(b)=rho L_(m-1) diag(W_b(t_j^0))`. On the fixed compact compensator interval B the strictly positive role weight satisfies `W_b(t)>=w_*>0`, giving

`||J_0(b)^(-1)||_inf <= 10/(rho*w_*)` (II),
`||J_0(b)^(-1)||_inf <= (25/2)/(rho*w_*)` (I).

Also `det J_0=m*rho^(m-1)*product_j W_b(t_j^0)>0`. This replaces an unquantified compactness assertion with an exact inverse bound.

## Severity-uniform moving-cut estimate (II)

All sharp internal role stages have the same radial source H_b. Translating internal cut tau modifies the forcing by a compact pulse `Delta_h(t;tau)=d_b((t-tau)/h)`, supported in an h-wide interior window and zero at its endpoints. For b in a fixed positive compact interval, `|d_b|<=D_*`, independent of q (the terminal target direction). Differentiating `R'=-rho R+rho H` gives the exact identity

`partial_tau R(t)=-rho Delta_h(t;tau)+rho² int_0^t exp[-rho(t-s)]Delta_h(s;tau)ds`.

Thus `||partial_tau R||_L1<=2rho*h*D_*` and `|partial_tau R(T)|<=rho²*h*D_*`. **No global pointwise O(h) bound is claimed** inside the moving ramp.

The remaining direct cut derivative of the target-ledger integral converges to the adjacent sharp-stage integrand difference, with O(h) error: rescale the ramp variable to [0,1], integrate the exact gradient along its strictly positive interpolation, and use the uniform Lipschitz bound on R. The radial derivative contribution is O(h) by the preceding L1 estimate. The terminal target ramp has fixed location and, even at q=0, bounded R-derivatives of the ledger integrand for nu=2-p>1. Therefore the full target-difference Jacobian converges uniformly to J_0 in b, q and cut neighborhoods as h->0, without demanding differentiability with respect to q at zero.

## Uniform quantitative contraction

Write `D^(h,q)(b,t)` for adjacent target-ledger differences; for the sharp stages `D^(0,q)(b,t^0(b))=0` uniformly and the Jacobian is J_0(b). The sharp roots have a uniform positive distance from crossing/end-stage cuts. Choose a uniform ball radius r small enough that `||I-J_0(b)^(-1)partial_t D^(0,q)(b,t)||_inf<1/4` throughout all balls about t^0(b). For sufficiently small **single fixed h>0**, the uniform estimates yield

`||J_0(b)^(-1)(partial_tD^(h,q)-partial_tD^(0,q))||_inf<1/4` and
`||J_0(b)^(-1)D^(h,q)(b,t^0(b))||_inf<r/2`

for all b in B and all 0<=q<=q0. The map `t -> t-J_0(b)^(-1)D^(h,q)(b,t)` contracts these balls with factor <=1/2 and maps each into itself. The unique local cut root is continuous in b,q. No `h=h(q)` selection is necessary. Compensation account bracketing, exact total flow closure, graph decomposition and fixed gross-share inventory integrability must still be applied as separate parts of the full Construction II proof.

This result does NOT certify the specific cached values h=.012, T=4, K=.002 for II or h=.2 for I, and cannot be extended to moving zero-component ramps without new estimates. It closes a **quantitative inverse-Jacobian proof obligation only**, not T04/I02 as a whole or Gate 2.
