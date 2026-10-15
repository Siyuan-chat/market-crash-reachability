import MarketCrash.Definitions

noncomputable section
open Set MeasureTheory
namespace MarketCrash

theorem coordinate_at_benchmark (F : ℝ) (g : ℝ → ℝ) : coordinate F g F = 0 := by
  simp [coordinate]

theorem coordinate_hasDerivAt (F : ℝ) (g : Response) (hF : 0 < F)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (coordinate F g.impact) (S / g.impact S) S := by
  have hc : ContinuousOn (fun u : ℝ => u / g.impact u) (Ioi 0) :=
    continuousOn_id.div g.continuousOn_positive (fun u hu => (g.positive u hu).ne')
  have hsub : uIcc F S ⊆ Ioi (0 : ℝ) := by
    intro u hu
    exact lt_of_lt_of_le (lt_min hF hS) hu.1
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.mono hsub).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc S hS)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hS))

theorem coordinate_strictMonoOn (F : ℝ) (g : Response) (hF : 0 < F) :
    StrictMonoOn (coordinate F g.impact) positivePrices := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro S hS
    exact (coordinate_hasDerivAt F g hF hS).continuousAt.continuousWithinAt
  · intro S hS
    have hs : 0 < S := by simpa [positivePrices, interior_Ioi] using hS
    rw [(coordinate_hasDerivAt F g hF hs).deriv]
    exact div_pos hs (g.positive S hs)

theorem normalized_trade_coefficient (F : ℝ) (g : Response) (hF : 0 < F)
    {S : ℝ} (hS : 0 < S) :
    deriv (coordinate F g.impact) S * g.impact S = S := by
  rw [(coordinate_hasDerivAt F g hF hS).deriv]
  exact div_mul_cancel₀ S (g.positive S hS).ne'

theorem coordinate_unique (F : ℝ) (g : Response) (hF : 0 < F)
    (ψ : ℝ → ℝ) (hψ : ∀ S ∈ positivePrices, DifferentiableAt ℝ ψ S)
    (hnorm : ψ F = 0)
    (htrade : ∀ S ∈ positivePrices, deriv ψ S * g.impact S = S) :
    EqOn ψ (coordinate F g.impact) positivePrices := by
  apply isOpen_Ioi.eqOn_of_deriv_eq isPreconnected_Ioi
    (fun S hS => (hψ S hS).differentiableWithinAt)
    (fun S hS => (coordinate_hasDerivAt F g hF hS).differentiableAt.differentiableWithinAt)
  · intro S hS
    rw [(coordinate_hasDerivAt F g hF hS).deriv]
    exact (eq_div_iff (g.positive S hS).ne').2 (htrade S hS)
  · exact hF
  · rw [hnorm, coordinate_at_benchmark]

noncomputable def inverseOnImage (F : ℝ) (g : ℝ → ℝ)
    (y : coordinateImage F g) : ℝ := Classical.choose y.property

theorem inverseOnImage_spec (F : ℝ) (g : ℝ → ℝ) (y : coordinateImage F g) :
    inverseOnImage F g y ∈ positivePrices ∧
      coordinate F g (inverseOnImage F g y) = y.val :=
  Classical.choose_spec y.property

theorem inverseOnImage_left (F : ℝ) (g : Response) (hF : 0 < F)
    (S : ℝ) (hS : S ∈ positivePrices) :
    inverseOnImage F g.impact ⟨coordinate F g.impact S, ⟨S, hS, rfl⟩⟩ = S := by
  have hi := inverseOnImage_spec F g.impact
    ⟨coordinate F g.impact S, ⟨S, hS, rfl⟩⟩
  exact (coordinate_strictMonoOn F g hF).injOn hi.1 hS hi.2

end MarketCrash
