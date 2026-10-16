import MarketCrash.BarrierEndpoint
import Mathlib.Analysis.Convex.Deriv

/-!
The curvature step in the exclusion proofs from V12 Final.

These results genuinely deduce concavity from a *global* response-elasticity
hypothesis over positive prices. The dynamical invariant H ≥ 0 has NOT yet
been deduced from the admissible resilient-market execution model.
-/
noncomputable section
namespace MarketCrash

/-- Elasticity at least one implies concavity of the dollar-normalized
    price coordinate on the whole positive-price domain. -/
theorem coordinate_concaveOn_of_elasticity_ge_one
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hElasticity : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S) :
    ConcaveOn ℝ positivePrices (coordinate F g.impact) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (D := positivePrices)
    (f' := fun S => S / g.impact S)
    (f'' := fun S => (1 - responseElasticity g.impact S) / g.impact S)
  · exact convex_Ioi 0
  · intro S hS
    exact (coordinate_hasDerivAt F g hF hS).continuousAt.continuousWithinAt
  · intro S hS
    have hs : 0 < S := by simpa [positivePrices] using hS
    exact (coordinate_hasDerivAt F g hF hs).hasDerivWithinAt
  · intro S hS
    have hs : 0 < S := by simpa [positivePrices] using hS
    exact (coordinate_slope_elasticity g.impact S
      (hdiff S hs) (g.positive S hs).ne').hasDerivWithinAt
  · intro S hS
    have hs : 0 < S := by simpa [positivePrices] using hS
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hElasticity S hs)) (g.positive S hs).le

/-- Elasticity at least two implies global concavity of the generalized
    coordinate G(x) = Φ(F exp x) in log-price space. -/
theorem logCoordinate_concaveOn_of_elasticity_ge_two
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hElasticity : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S) :
    ConcaveOn ℝ Set.univ (logCoordinate F g.impact) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos
    (D := Set.univ)
    (f' := fun x => (F * Real.exp x) ^ 2 / g.impact (F * Real.exp x))
    (f'' := fun x => ((F * Real.exp x) ^ 2 / g.impact (F * Real.exp x)) *
      (2 - responseElasticity g.impact (F * Real.exp x)))
  · exact convex_univ
  · intro x _
    exact (logCoordinate_hasDerivAt F g hF x).continuousAt.continuousWithinAt
  · intro x _
    exact (logCoordinate_hasDerivAt F g hF x).hasDerivWithinAt
  · intro x _
    have hs : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
    simpa only [responseElasticity] using
      ((log_slope_hasDerivAt F x (deriv g.impact (F * Real.exp x))
        g.impact (hdiff (F * Real.exp x) hs).hasDerivAt
        (g.positive (F * Real.exp x) hs).ne').hasDerivWithinAt)
  · intro x _
    have hs : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
    have hp : 0 ≤ (F * Real.exp x) ^ 2 / g.impact (F * Real.exp x) :=
      div_nonneg (sq_nonneg _) (g.positive (F * Real.exp x) hs).le
    exact mul_nonpos_of_nonneg_of_nonpos hp
      (sub_nonpos.mpr (hElasticity (F * Real.exp x) hs))

/-- The elasticity-2 hypothesis no longer needs an assumed concavity
    theorem here: it yields an endpoint crisis bound from H ≥ 0. The
    trajectory proof of H ≥ 0 is a separate remaining obligation. -/
theorem no_positive_crisis_of_elasticity_ge_two_and_potential
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hElasticity : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S)
    (q : ι → ℝ) (k : ℕ)
    (hPotential : 0 ≤ ∑ i, logCoordinate F g.impact (q i)) :
    systemicCrisis q k ≤ 0 := by
  exact no_positive_crisis_of_concave_potential
    (logCoordinate F g.impact) q k
    (logCoordinate_concaveOn_of_elasticity_ge_two F g hF hdiff hElasticity)
    (logCoordinate_strictMono F g hF)
    (by simp [logCoordinate, coordinate_at_benchmark])
    hPotential

end MarketCrash
