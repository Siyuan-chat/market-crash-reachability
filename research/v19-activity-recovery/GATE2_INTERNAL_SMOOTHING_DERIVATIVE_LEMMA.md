# Gate 2 technical note — uniform cut-time derivative of activity-driven radial smoothing

**Status:** proved technical lemma for the *internal switching ramps* in Construction II, conditional on the fixed positive interior composition domain. It does **not** certify the full `forall delta` construction, its cached numerical witness, or Gate 2 as a whole.

## Setup and exact identity

Write `R'(t)=-rho R(t)+rho H(t)`, with `rho>0`, on a fixed horizon `[0,T]`. In Construction II, an internal cut between successive target stages only interchanges the high and low direction components. Both constant stages have the **same** `H_b`. For a fixed positive smoothing half-width `h/2`, this cut contributes to the radial forcing a localized pulse

```text
Delta_h(t;tau) = d_b((t-tau)/h) on |t-tau| <= h/2, and 0 outside,
d_b(-1/2)=d_b(1/2)=0.
```

At fixed `b` in a compact interval away from zero, all internal component weights are uniformly positive, so `d_b` is continuous, piecewise continuously differentiable, and `|d_b|<=D_*` uniformly in b. Other cuts and the initial/final ramps are independent of this particular cut time `tau`. Their contributions are irrelevant for differentiation in `tau`.

Define `R_tau(t)=partial R(t)/partial tau`. Since `partial_tau Delta_h=-partial_t Delta_h` in its weak (equivalently, a.e. piecewise classical) sense, differentiation of the variation-of-constants formula and integration by parts give the **exact** identity

```text
R_tau(t)
 = -rho Delta_h(t;tau)
   + rho^2 integral_0^t exp[-rho(t-s)] Delta_h(s;tau) ds.      (*)
```

There are no endpoint boundary terms because `Delta_h(0)=0` and the ramp is compactly supported in `(0,T)`.

## Uniform bounds with the correct norm

For all allowed b, cut times with the entire h-ramp internal, and `0<h<min(tau,T-tau)*2`,

```text
||Delta_h||_L1(0,T) <= h D_*;
||R_tau||_L1(0,T) <= 2 rho h D_*;                          (1)
|R_tau(T)| <= rho^2 h D_*;                                (2)
||R_tau||_Linfty(0,T) <= rho D_* + rho^2 h D_*.            (3)
```

To establish (1), use Tonelli and
`integral_s^T exp[-rho(t-s)]dt <= 1/rho` on the convolution term in (*).
For (2), the pulse vanishes at `T` and the remaining convolution is bounded by its L1 norm. Statement (3) shows why the stronger assertion `||R_tau||_Linfty=O(h)` would be false in general: inside the moving ramp, `-rho Delta_h` has order one. The **L1** derivative and the **terminal** derivative have order h with constants independent of terminal severity `q`, because the pulse contains only strictly positive *internal* high/low compositions.

## Consequence for the cut-time ledger Jacobian

For any ledger residual of the form
```text
X_i(T)= [x_i(T)^nu-1]/nu
        +rho integral_0^T x_i(t)^(nu-1)(x_i(t)-1)dt,
x_i=R(t)Y_i(t)^(1/nu), nu=2-p>1,
```
the derivative contribution caused *only* by the induced radial variation is `O(h)` uniformly in `b` and `q`: `R>=1`, `R<=N^(1/nu)`, `0<=Y_i<=1` give bounded partial derivatives of the ledger integrand with respect to `R`, and (1) controls their integrated product; (2) controls the terminal `R(T)` contribution. This does **not** assume differentiability in q at q=0. The direct variation of the moving internal interpolation in `Y_i` is order one and converges to the difference of its neighboring constant-stage integrands as `h->0`; this term is precisely the sharp-limit switching contribution.

Consequently the cut-time Jacobian has a valid route to the limit
```text
partial_t D^(h,q) -> rho L_8 diag(W_b(t_1),...,W_b(t_8)),
det = 9 rho^8 product_j W_b(t_j) > 0
```
uniformly on compact interior parameter neighborhoods, **provided** the remaining direct interpolation-derivative convergence and endpoint-map regularity are proved as stated. Equation (*) and (1)-(3) alone are **not** that entire proof.

## Audit scope and exclusions

- Applies to movable *interior* ramps between permutations of the same constant direction multiset; their `H` forcing has identical stage endpoints.
- Does not apply without modification to a ramp where the constant `H` genuinely changes across the cut.
- Does not claim `C1` admissibility; Construction II remains a `C0` analytic existence problem.
- Does not infer a uniform gross **share-rate** bound from an L1 inventory estimate.
- Does not upgrade the `T=4,K=.002,h=.012` floating-point root to an exact certificate.

This note repairs an important possible overstatement in earlier proof prose and is a reusable sublemma for the full proof audit of `T04/I02/A03/A07`.
