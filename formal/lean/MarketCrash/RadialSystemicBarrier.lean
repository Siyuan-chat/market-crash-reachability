import MarketCrash.CountablePhysicalClosure
import Mathlib.Analysis.Convex.Deriv

/-!
# Localized log-price curvature and original crisis functional

Theorem 3.2 must use the response elasticity only on prices reachable
by the market, not for all S>0. A per-asset radial tangent inequality
for G(q)=Phi(F*exp q) is sufficient for the crisis mean-loss bound:
G(q_i) <= G'(0)*q_i, with G'(0)>0.

We derive the radial tangent from the SECOND physical response curvature
(2 - e(S)) on [min 0 q_i, max 0 q_i] in log-price coordinates, not
from a global concavity assertion or postulated invariant.

This file closes the finite-dimensional localized 3.2 endpoint step
but not the all-BV physical potential-invariance/existence proof.
-/

noncomputable section
namespace MarketCrash

/-- Elasticity e>=2 restricted to a compact log-price interval
implies concavity of the transformed log-price response G there. -/
theorem logCoordinate_concaveOn_Icc_of_local_elasticity
    (F : ℝ) (g : Response) (hF : 0 < F)
    (a b : ℝ) (hab : a ≤ b)
    (hdiff : ∀ x ∈ Set.Icc a b,
      DifferentiableAt ℝ g.impact (F * Real.exp x))
    (hel : ∀ x ∈ Set.Icc a b,
      2 ≤ responseElasticity g.impact (F * Real.exp x)) :
    ConcaveOn ℝ (Set.Icc a b) (logCoordinate F g.impact) := by
  let d : ℝ → ℝ := fun x =>
    (F * Real.exp x) ^ 2 / g.impact (F * Real.exp x)
  let dd : ℝ → ℝ := fun x =>
    d x * (2 - responseElasticity g.impact (F * Real.exp x))
  have hcont : ContinuousOn (logCoordinate F g.impact) (Set.Icc a b) := by
    intro x _
    exact (logCoordinate_hasDerivAt F g hF x).continuousAt.continuousWithinAt
  have hfirst : ∀ x ∈ interior (Set.Icc a b),
      HasDerivWithinAt (logCoordinate F g.impact) (d x)
        (interior (Set.Icc a b)) x := by
    intro x _
    exact (logCoordinate_hasDerivAt F g hF x).hasDerivWithinAt
  have hsecond : ∀ x ∈ interior (Set.Icc a b),
      HasDerivWithinAt d (dd x) (interior (Set.Icc a b)) x := by
    intro x hx
    have hmem : x ∈ Set.Icc a b := interior_subset hx
    have hs : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
    simpa only [d, dd, responseElasticity] using
      ((log_slope_hasDerivAt F x (deriv g.impact (F * Real.exp x))
        g.impact (hdiff x hmem).hasDerivAt
        (g.positive (F * Real.exp x) hs).ne').hasDerivWithinAt)
  have hsign : ∀ x ∈ interior (Set.Icc a b), dd x ≤ 0 := by
    intro x hx
    have hmem : x ∈ Set.Icc a b := interior_subset hx
    have hs : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
    have hp : 0 ≤ d x :=
      div_nonneg (sq_nonneg _) (g.positive (F * Real.exp x) hs).le
    exact mul_nonpos_of_nonneg_of_nonpos hp
      (sub_nonpos.mpr (hel x hmem))
  exact concaveOn_of_hasDerivWithinAt2_nonpos
    (convex_Icc a b) hcont hfirst hsecond hsign

/-- For the benchmark-to-final-price radial log interval alone,
e(S)>=2 implies that G(q) lies below the tangent at q=0. -/
theorem logCoordinate_le_benchmark_tangent_of_radial_elasticity
    (F : ℝ) (g : Response) (hF : 0 < F)
    (q : ℝ)
    (hdiff : ∀ x ∈ Set.Icc (min 0 q) (max 0 q),
      DifferentiableAt ℝ g.impact (F * Real.exp x))
    (hel : ∀ x ∈ Set.Icc (min 0 q) (max 0 q),
      2 ≤ responseElasticity g.impact (F * Real.exp x)) :
    logCoordinate F g.impact q ≤ (F ^ 2 / g.impact F) * q := by
  have hab : min 0 q ≤ max 0 q :=
    (min_le_left 0 q).trans (le_max_left 0 q)
  have hconc : ConcaveOn ℝ (Set.Icc (min 0 q) (max 0 q))
      (logCoordinate F g.impact) :=
    logCoordinate_concaveOn_Icc_of_local_elasticity
      F g hF (min 0 q) (max 0 q) hab hdiff hel
  have hmem0 : (0 : ℝ) ∈ Set.Icc (min 0 q) (max 0 q) :=
    ⟨min_le_left 0 q, le_max_left 0 q⟩
  have hmemq : q ∈ Set.Icc (min 0 q) (max 0 q) :=
    ⟨min_le_right 0 q, le_max_right 0 q⟩
  have hG0 : logCoordinate F g.impact 0 = 0 := by
    simp [logCoordinate, coordinate_at_benchmark]
  have hd0 : HasDerivAt (logCoordinate F g.impact)
      (F ^ 2 / g.impact F) 0 := by
    simpa only [Real.exp_zero, mul_one] using
      (logCoordinate_hasDerivAt F g hF 0)
  rcases lt_trichotomy q 0 with hlt | heq | hgt
  · have hslope := hconc.le_slope_of_hasDerivAt
      hmemq hmem0 hlt hd0
    rw [slope_def_field, hG0] at hslope
    have hn : 0 < (0 : ℝ) - q := sub_pos.mpr hlt
    have hm := (le_div_iff₀ hn).mp hslope
    nlinarith
  · subst q
    simp [hG0]
  · have hslope := hconc.slope_le_of_hasDerivAt
      hmem0 hmemq hgt hd0
    rw [slope_def_field, hG0] at hslope
    have hn : 0 < q - (0 : ℝ) := sub_pos.mpr hgt
    have hm := (div_le_iff₀ hn).mp hslope
    nlinarith

/-- A nonnegative physical potential implies nonnegative sum of
log-prices under e>=2 ONLY on each benchmark-to-actual-price radial
interval, rather than all S>0. -/
theorem nonnegative_log_sum_of_radial_elasticity_ge_two
    {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (q : ι → ℝ)
    (hdiff : ∀ i x, x ∈ Set.Icc (min 0 (q i)) (max 0 (q i)) →
      DifferentiableAt ℝ g.impact (F * Real.exp x))
    (hel : ∀ i x, x ∈ Set.Icc (min 0 (q i)) (max 0 (q i)) →
      2 ≤ responseElasticity g.impact (F * Real.exp x))
    (hPotential : 0 ≤ ∑ i, logCoordinate F g.impact (q i)) :
    0 ≤ ∑ i, q i := by
  have hsum : (∑ i, logCoordinate F g.impact (q i)) ≤
      (F ^ 2 / g.impact F) * ∑ i, q i := by
    rw [← Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact logCoordinate_le_benchmark_tangent_of_radial_elasticity
      F g hF (q i) (hdiff i) (hel i)
  have hcoef : 0 < F ^ 2 / g.impact F :=
    div_pos (sq_pos_of_pos hF) (g.positive F hF)
  by_contra hbad
  have hneg : (∑ i, q i) < 0 := lt_of_not_ge hbad
  have hlt : (F ^ 2 / g.impact F) * ∑ i, q i < 0 :=
    mul_neg_of_pos_of_neg hcoef hneg
  exact (not_lt_of_ge (hPotential.trans hsum)) hlt

/-- Localized, exact physical crisis endpoint: only radial prices
reached between F and each final asset price need satisfy e>=2. -/
theorem no_positive_crisis_of_radial_elasticity_ge_two_and_potential
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (q : ι → ℝ) (k : ℕ)
    (hdiff : ∀ i x, x ∈ Set.Icc (min 0 (q i)) (max 0 (q i)) →
      DifferentiableAt ℝ g.impact (F * Real.exp x))
    (hel : ∀ i x, x ∈ Set.Icc (min 0 (q i)) (max 0 (q i)) →
      2 ≤ responseElasticity g.impact (F * Real.exp x))
    (hPotential : 0 ≤ ∑ i, logCoordinate F g.impact (q i)) :
    systemicCrisis q k ≤ 0 := by
  exact no_positive_crisis_of_nonnegative_log_sum q k
    (nonnegative_log_sum_of_radial_elasticity_ge_two
      F g hF q hdiff hel hPotential)

end MarketCrash
