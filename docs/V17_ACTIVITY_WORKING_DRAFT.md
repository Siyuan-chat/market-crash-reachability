# V17 · Activity-driven recovery — mathematical and evidence register

**Edition:** independently developed working manuscript, 5 November 2026. This is neither a peer-reviewed publication nor the historical V16 time-recovery result. **The model changed.** Do not cite V16's time-dependent price barriers or V16's interval certificate as verifying V17.

## Frozen model and admissibility

For positive prices $S_i(0)=F$ and paired directed dollar executions $dz_e\ge0$,

$$dS_i=\frac{g(S_i)}{S_i}\,dX_i-\kappa(S_i-F)\,dA_i,\quad dX=Bdz,\quad dA_i=\sum_e|B_{ie}|dz_e.$$

Within each directed edge dollar event, **both** impact and activity recovery are integrated; inactivity leaves prices fixed. Terminal executed-dollar closure is $X_i(T)=0$ assetwise. Initial sale inventory is sufficient, so shorts are forbidden. $M=\sum_e\int dz_e$ counts each paired transfer once. $\mathsf C_0$ allows simultaneous gross offsetting flow at one asset; $\mathsf C_1$ forbids it but permits direction switches at separate times. All three examples use a full bidirectional ten-node graph.

## Gate / theorem / evidence matrix

| Claim | Control scope | Evidence completed in this working draft | What is **not** established |
|---|---|---|---|
| Exact $\Phi,\Psi,E,R$ activity and share-cost identities | $\mathsf C_0$; flow-completed BV/AC | Direct chain-rule derivation in paper §2 | Independent formal proof |
| Nine-edge local simultaneous declines, $N\ge3$, arbitrary smooth positive $g$ | Explicit finite $\mathsf C_1$ sequence | Analytic $-\kappa z^2+O(z^3)$ expansion, independent RK4 regression | Full two-node phase diagram |
| Positive scalar floors; $p<1$ at $K\ge K_c(p)$, $p=1$ at $K>1$, $p>1$ at every $K>0$ | $\mathsf C_0$ (thus $\mathsf C_1$) | Scalar drift comparison | Sharp reachability thresholds in all remaining $K$ regimes |
| $\sum_i x_i^{2-p}\ge1$ ($p<2$), $M/H$ necessary bounds, $K$-dependent turnover for $p=0$ | $\mathsf C_0$ | Integral and invariant-region proofs | Sufficiency or optimality |
| Construction I: all ten exactly $x_i(T)=1/2$ | $\mathsf C_0$; AC; finite resources | **Analytic existence via radial paths, equal-weight cuts and a nondegenerate $C^1$ smoothing/IFT argument**; no numerical parameters claimed certified | A certified explicit numerical witness or optimized turnover |
| Construction II: for all $\delta$, nine terminal losses exceed $\delta$ under the **same** finite $M,H,T,K$ | $\mathsf C_0$; AC; finite uniform resources | **Analytic existence via a parameter-uniform IFT, explicit compensator sign bounds at $T=40$, and an integrable $1/\sqrt{1-\lambda}$ inventory bound** | Numerically fixed $h,K,M_0,H_0$ values or the same claim in $\mathsf C_1$ |
| Construction III: five successive $-25\%$ lower closes; $G(40)<.84$ | $\mathsf C_1$; AC; 2×20 sessions | **Internally directed interval** sign bracket, exact ledger-root IVT, all path-event bounds, $M<11.261627$, $H_i^-<2$, rate $<.133$ | Externally certified interval checker; optimality of five assets |
| All-node second session continuation while all $S_i\le F$ | Both | Monotonicity of $\sum\Phi$ in second session | Any old-model upper bound of seven consecutive lower-limit assets |

**Evidence distinctions:** Constructions I and II are *analytical nonconstructive existence arguments*, not explicit interval-certified example files. The paper gives an explicit base family and verifies Jacobian nondegeneracy; its parameter-stability/smoothing argument should receive independent mathematical review before journal submission. Construction III is an internally authored enclosure algorithm using `mpmath.iv` and rational inverse brackets. Its JSON display approximations are not used as proof bounds; acceptance comparisons use `Fraction` endpoints and strict inequalities. None of this is independent external certification.

## Main open questions and audit priorities

1. Independently review the equal-activity graph completion, including measurable edge-rate selection and event-flow convergence.
2. Independently check the parameter-uniform $C^1$ continuation argument in Construction II at $q\downarrow0$, including derivatives with respect to stage cuts and endpoint transitions. The $q=0$ limit is only used to determine signs and continuation: no executed path is permitted to hit zero price.
3. Independently audit the `mpmath.iv` implementation, arctangent remainder, inverse-bracketing rigor and all rolling-band/initial-share constraints for Construction III. Internal implementation coverage alone is not a machine-checked theorem.
4. Determine whether the same severe nine-target severity family exists for the restrictive $\mathsf C_1$ controls and classify the price-floor transition region. Do not infer either from the present $\mathsf C_0$ proof.
5. The maximum number of assets which can meet two lower-limit closes under the new model is not known; **five are exhibited**, with no claim of optimality.

## Reproduce independently of V16

```bash
python -m pip install mpmath==1.3.0
python verification/activity_driven/test_activity.py
python verification/activity_driven/certify_five_targets.py
python scripts/check_v17_activity.py
python scripts/build_v17_activity.py  # requires repository SIAM ZIP, pdflatex and bibtex
```

The V17 workflow `.github/workflows/v17.yml` also runs the historical V16 checks **unchanged**. A successful V16 job is a regression on the older model, not a certificate for V17. The strict build puts its PDF in ignored `build/v17-activity-driven-recovery/main.pdf` and uploads a CI artifact. It does not replace V16, the fixed Zenodo records, `paper/main.tex` or historical provenance manifests.
