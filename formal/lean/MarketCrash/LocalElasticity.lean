import MarketCrash.RestoringTangent

/-!
Local response-elasticity lemmas for paper Theorem 3.1.

Unlike the earlier global curvature result, these theorems require
elasticity only between the benchmark F and the observed price S.
They remove the unnecessary global-positive-domain premise from the
SCALAR restoring-force inequality.

The final model-fidelity step is to show this benchmark-to-price
interval belongs to the price range *attainable by original M1–M5 paths*.
That interval-inclusion statement is not assumed to be already proved.
-/
noncomputable section
namespace MarketCrash

/-- On an arbitrary positive compact interval, elasticity at least
one implies concavity of the response-adapted coordinate on THAT
interval, without a global derivative or elasticity requirement. -/
theorem coordinate_concaveOn_Icc_of_local_elasticity
    (F : ℝ) (g : Response) (hF : 0 < F)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hdiff : ∀ S ∈ Set.Icc a b, DifferentiableAt ℝ g.impact S)
    (hel : ∀ S ∈ Set.Icc a b,
      1 ≤ responseElasticity g.impact S) :
    ConcaveOn ℝ (Set.Icc a b) (coordinate F g.impact) := by
  have hcont : ContinuousOn (coordinate F g.impact) (Set.Icc a b) := by
    intro S hS
    have hs : 0 < S := ha.trans_le hS.1
    exact (coordinate_hasDerivAt F g hF hs).continuousAt.continuousWithinAt
  have hfirst : ∀ S ∈ interior (Set.Icc a b),
      HasDerivWithinAt (coordinate F g.impact) (S / g.impact S)
        (interior (Set.Icc a b)) S := by
    intro S hS
    have hmem : S ∈ Set.Icc a b := interior_subset hS
    have hs : 0 < S := ha.trans_le hmem.1
    exact (coordinate_hasDerivAt F g hF hs).hasDerivWithinAt
  have hsecond : ∀ S ∈ interior (Set.Icc a b),
      HasDerivWithinAt (fun u : ℝ => u / g.impact u)
        ((1 - responseElasticity g.impact S) / g.impact S)
        (interior (Set.Icc a b)) S := by
    intro S hS
    have hmem : S ∈ Set.Icc a b := interior_subset hS
    have hs : 0 < S := ha.trans_le hmem.1
    exact (coordinate_slope_elasticity g.impact S
      (hdiff S hmem) (g.positive S hs).ne').hasDerivWithinAt
  have hsign : ∀ S ∈ interior (Set.Icc a b),
      (1 - responseElasticity g.impact S) / g.impact S ≤ 0 := by
    intro S hS
    have hmem : S ∈ Set.Icc a b := interior_subset hS
    have hs : 0 < S := ha.trans_le hmem.1
    exact div_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hel S hmem)) (g.positive S hs).le
  exact concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
    hcont hfirst hsecond hsign

/-- The restoring-force inequality only uses elasticity on
[min F S,max F S]. This includes the benchmark endpoint and no
other unvisited prices outside the benchmark-to-price interval. -/
theorem restoring_drain_le_coordinate_of_radial_elasticity
    (F : ℝ) (g : Response) (hF : 0 < F)
    (S : ℝ) (hS : 0 < S)
    (hdiff : ∀ u ∈ Set.Icc (min F S) (max F S),
      DifferentiableAt ℝ g.impact u)
    (hel : ∀ u ∈ Set.Icc (min F S) (max F S),
      1 ≤ responseElasticity g.impact u) :
    S * (S - F) / g.impact S ≤ coordinate F g.impact S := by
  have ha : 0 < min F S := lt_min hF hS
  have hab : min F S ≤ max F S :=
    (min_le_left F S).trans (le_max_left F S)
  have hconcave : ConcaveOn ℝ (Set.Icc (min F S) (max F S))
      (coordinate F g.impact) :=
    coordinate_concaveOn_Icc_of_local_elasticity
      F g hF (min F S) (max F S) ha hab hdiff hel
  have hmemF : F ∈ Set.Icc (min F S) (max F S) :=
    ⟨min_le_left F S, le_max_left F S⟩
  have hmemS : S ∈ Set.Icc (min F S) (max F S) :=
    ⟨min_le_right F S, le_max_right F S⟩
  have hderiv := coordinate_hasDerivAt F g hF hS
  have hrearrange :
      S * (S - F) / g.impact S =
        (S / g.impact S) * (S - F) := by ring
  rcases lt_trichotomy S F with hlt | heq | hgt
  · have hslope :=
      hconcave.slope_le_of_hasDerivAt hmemS hmemF hlt hderiv
    rw [slope_def_field, coordinate_at_benchmark] at hslope
    have hm := (div_le_iff₀ (sub_pos.mpr hlt)).mp hslope
    rw [hrearrange]
    nlinarith
  · subst S
    simp [coordinate_at_benchmark]
  · have hslope :=
      hconcave.le_slope_of_hasDerivAt hmemF hmemS hgt hderiv
    rw [slope_def_field, coordinate_at_benchmark] at hslope
    have hm := (le_div_iff₀ (sub_pos.mpr hgt)).mp hslope
    rw [hrearrange]
    nlinarith

/-- Local radial elasticity for each actual price suffices for the
aggregate recovery inequality; no global e(S) lower bound is needed. -/
theorem restoring_drain_sum_le_potential_of_radial_elasticity
    {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hdiff : ∀ i u, u ∈ Set.Icc (min F (S i)) (max F (S i)) →
      DifferentiableAt ℝ g.impact u)
    (hel : ∀ i u, u ∈ Set.Icc (min F (S i)) (max F (S i)) →
      1 ≤ responseElasticity g.impact u) :
    (∑ i, S i * (S i - F) / g.impact (S i)) ≤
      potential (fun i => coordinate F g.impact (S i)) := by
  unfold potential
  apply Finset.sum_le_sum
  intro i _
  exact restoring_drain_le_coordinate_of_radial_elasticity
    F g hF (S i) (hS i) (hdiff i) (hel i)

end MarketCrash
