import MarketCrash.RecoveryPotential
import MarketCrash.Conservation
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
Continuous-time comparison for a price-coordinate potential.

The two declarations do NOT yet establish the full paper barriers:
the "restoring term ≤ potential" inequality is an explicit hypothesis
to be discharged by a separate concavity/tangent argument, and here
solutions are differentiable on the whole real line. This module is
an exact continuous ODE comparison rather than a finite-step surrogate.
-/
noncomputable section
namespace MarketCrash

/-- Integrating-factor comparison: if H'(t) ≥ -ρ H(t) and H(0) ≥ 0,
then H(t) ≥ 0 at all times t ≥ 0. -/
theorem nonnegative_of_derivative_ge_linear
    (H slope : ℝ → ℝ) (rho : ℝ)
    (hderiv : ∀ t, HasDerivAt H (slope t) t)
    (hbound : ∀ t, -rho * H t ≤ slope t)
    (hzero : 0 ≤ H 0) (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ H t := by
  let J : ℝ → ℝ := fun u => Real.exp (rho * u) * H u
  have hJ (u : ℝ) :
      HasDerivAt J (Real.exp (rho * u) * (rho * H u + slope u)) u := by
    have hlinear : HasDerivAt (fun v : ℝ => rho * v) rho u := by
      convert (hasDerivAt_id u).const_mul rho using 1 <;> ring
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (rho * v))
        (Real.exp (rho * u) * rho) u :=
      (Real.hasDerivAt_exp (rho * u)).comp u hlinear
    convert (hexp.mul (hderiv u)) using 1 <;> ring
  have hnonneg : ∀ u : ℝ, 0 ≤ deriv J u := by
    intro u
    rw [(hJ u).deriv]
    have hlocal : 0 ≤ rho * H u + slope u := by
      have hb := hbound u
      linarith
    exact mul_nonneg (Real.exp_pos _).le hlocal
  have hmono : Monotone J :=
    monotone_of_deriv_nonneg (fun u => (hJ u).differentiableAt) hnonneg
  have hJzero : 0 ≤ J 0 := by simpa [J] using hzero
  have hJt : 0 ≤ J t := hJzero.trans (hmono ht)
  classical
  by_contra hfail
  have hneg : H t < 0 := lt_of_not_ge hfail
  have hJneg : J t < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  exact (not_lt_of_ge hJt) hJneg

/-- A true continuous paired-dollar normal-form trajectory maintains
nonnegative potential whenever the restoring sum is bounded by H.
The trading cancellation is proved from the incidence matrix. -/
theorem nonnegative_potential_of_normal_form
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι)
    (y : ℝ → ι → ℝ) (rates : ℝ → κ → ℝ)
    (R : ℝ → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hy : ∀ t i, HasDerivAt (fun u => y u i)
      (tradingInput (pairedMatrix edges) (rates t) i - rho * R (y t i)) t)
    (hrestore : ∀ t, (∑ i, R (y t i)) ≤ potential (y t))
    (hzero : 0 ≤ potential (y 0))
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ potential (y t) := by
  have hd (u : ℝ) : HasDerivAt (fun v => potential (y v))
      (-rho * ∑ i, R (y u i)) u :=
    normal_form_sum_derivative edges y (rates u) R rho u (hy u)
  have hb (u : ℝ) :
      -rho * potential (y u) ≤ -rho * ∑ i, R (y u i) := by
    have hnonneg : 0 ≤ rho * (potential (y u) - ∑ i, R (y u i)) :=
      mul_nonneg hrho (sub_nonneg.mpr (hrestore u))
    nlinarith
  exact nonnegative_of_derivative_ge_linear
    (fun u => potential (y u)) (fun u => -rho * ∑ i, R (y u i))
    rho hd hb hzero t ht

end MarketCrash
