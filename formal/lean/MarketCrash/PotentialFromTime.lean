import MarketCrash.ContinuousInvariant

/-!
Time-shifted continuous ODE comparison used for concatenating market segments.

Unlike a theorem tied to H(0), these statements allow a nonnegative
transformed potential at *any* starting time a, and prove the same property
at a later t. The global differentiability hypothesis remains stronger
than piecewise absolutely continuous market execution; a subsequent
segment abstraction must address that distinction.
-/
noncomputable section
namespace MarketCrash

/-- Positivity of the integrating-factor comparison propagates from
any start a to a later time t. -/
theorem nonnegative_of_derivative_ge_linear_from
    (H slope : ℝ → ℝ) (rho : ℝ)
    (hderiv : ∀ u, HasDerivAt H (slope u) u)
    (hbound : ∀ u, -rho * H u ≤ slope u)
    (a t : ℝ) (hat : a ≤ t) (hstart : 0 ≤ H a) :
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
  have hJa : 0 ≤ J a := by
    change 0 ≤ Real.exp (rho * a) * H a
    exact mul_nonneg (Real.exp_pos _).le hstart
  have hJt : 0 ≤ J t := hJa.trans (hmono hat)
  classical
  by_contra hfail
  have hneg : H t < 0 := lt_of_not_ge hfail
  have hJneg : J t < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  exact (not_lt_of_ge hJt) hJneg

/-- The potential of a smooth paired-dollar normal-form segment
is nonnegative at its end whenever it was nonnegative at its start.
The normal form eliminates the trading sum exactly. -/
theorem nonnegative_potential_of_normal_form_from
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι)
    (y : ℝ → ι → ℝ) (rates : ℝ → κ → ℝ)
    (R : ℝ → ℝ) (rho : ℝ) (hrho : 0 ≤ rho)
    (hy : ∀ u i, HasDerivAt (fun v => y v i)
      (tradingInput (pairedMatrix edges) (rates u) i - rho * R (y u i)) u)
    (hrestore : ∀ u, (∑ i, R (y u i)) ≤ potential (y u))
    (a t : ℝ) (hat : a ≤ t)
    (hstart : 0 ≤ potential (y a)) :
    0 ≤ potential (y t) := by
  have hd (u : ℝ) : HasDerivAt (fun v => potential (y v))
      (-rho * ∑ i, R (y u i)) u :=
    normal_form_sum_derivative edges y (rates u) R rho u (hy u)
  have hb (u : ℝ) :
      -rho * potential (y u) ≤ -rho * ∑ i, R (y u i) := by
    have hnonneg : 0 ≤ rho * (potential (y u) - ∑ i, R (y u i)) :=
      mul_nonneg hrho (sub_nonneg.mpr (hrestore u))
    nlinarith
  exact nonnegative_of_derivative_ge_linear_from
    (fun u => potential (y u)) (fun u => -rho * ∑ i, R (y u i))
    rho hd hb a t hat hstart

end MarketCrash
