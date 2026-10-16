import MarketCrash.ElasticityConcavity

/-!
The actual restoring-force inequality used by the barrier proofs.

For a globally concave price coordinate Φ, its tangent at S dominates
the benchmark Φ(F)=0. Hence S(S-F)/g(S) ≤ Φ(S) for S>0.
This is a mathematical implication of concavity, NOT an assumed
inequality. Coupling it to all continuous market paths is a separate gate.
-/
noncomputable section
namespace MarketCrash

/-- Concavity implies the recovery drift's scalar term is at most the
    response-adapted price coordinate. -/
theorem restoring_drain_le_coordinate
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hConcave : ConcaveOn ℝ positivePrices (coordinate F g.impact))
    (S : ℝ) (hS : 0 < S) :
    S * (S - F) / g.impact S ≤ coordinate F g.impact S := by
  have hderiv := coordinate_hasDerivAt F g hF hS
  have hrearrange :
      S * (S - F) / g.impact S = (S / g.impact S) * (S - F) := by
    ring
  rcases lt_trichotomy S F with hlt | heq | hgt
  · have hslope := hConcave.slope_le_of_hasDerivAt hS hF hlt hderiv
    rw [slope_def_field, coordinate_at_benchmark] at hslope
    have hm := (div_le_iff₀ (sub_pos.mpr hlt)).mp hslope
    rw [hrearrange]
    nlinarith
  · subst S
    simp [coordinate_at_benchmark]
  · have hslope := hConcave.le_slope_of_hasDerivAt hF hS hgt hderiv
    rw [slope_def_field, coordinate_at_benchmark] at hslope
    have hm := (le_div_iff₀ (sub_pos.mpr hgt)).mp hslope
    rw [hrearrange]
    nlinarith

/-- The scalar restoring contribution summed across any finite asset set
    is bounded by the aggregate transformed potential. -/
theorem restoring_drain_sum_le_potential
    {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hConcave : ConcaveOn ℝ positivePrices (coordinate F g.impact))
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) :
    (∑ i, S i * (S i - F) / g.impact (S i)) ≤
      potential (fun i => coordinate F g.impact (S i)) := by
  unfold potential
  apply Finset.sum_le_sum
  intro i _
  exact restoring_drain_le_coordinate F g hF hConcave (S i) (hS i)

/-- Derive the recovery bound from the response-elasticity condition
    rather than asserting it as a new market assumption. -/
theorem restoring_drain_sum_le_potential_of_elasticity_ge_one
    {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hElasticity : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (S : ι → ℝ) (hS : ∀ i, 0 < S i) :
    (∑ i, S i * (S i - F) / g.impact (S i)) ≤
      potential (fun i => coordinate F g.impact (S i)) := by
  exact restoring_drain_sum_le_potential F g hF
    (coordinate_concaveOn_of_elasticity_ge_one F g hF hdiff hElasticity) S hS

end MarketCrash
