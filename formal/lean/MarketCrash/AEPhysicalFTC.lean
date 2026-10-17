import MarketCrash.AEAttainableBarrier
import MarketCrash.LipschitzFTC
import MarketCrash.RateBand

/-! Analysis for an already supplied Lipschitz operational segment.
This does not construct that segment from an original BV physical path. -/
noncomputable section
namespace MarketCrash
open MeasureTheory Set
open scoped NNReal
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}

theorem AEOperationalClockSegment.coordinate_lipschitz_on
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) (i : ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun t => coordinate F g.impact (m.prices t i)) (Icc m.a m.b) := by
  obtain ⟨C, hC⟩ := m.prices_lipschitz i
  have hc := hC.continuous.continuousOn (s := Icc m.a m.b)
  have hne : (Icc m.a m.b).Nonempty := ⟨m.a, le_rfl, m.time_order⟩
  obtain ⟨l, hl, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  let L := m.prices l i
  let U := m.prices u i
  have hL : 0 < L := m.positive_prices l hl i
  have hsub : Icc L U ⊆ positivePrices := fun x hx => hL.trans_le hx.1
  have hg := g.continuousOn_positive.mono hsub
  have hn : ContinuousOn (fun x : ℝ => ‖x / g.impact x‖) (Icc L U) :=
    (continuousOn_id.div hg (fun x hx => (g.positive x (hsub hx)).ne')).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hn
  let D : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hphi : LipschitzOnWith D (coordinate F g.impact) (Icc L U) := by
    apply (convex_Icc L U).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (coordinate_hasDerivAt F g hF (hsub hx)).hasDerivWithinAt)
    intro x hx
    change ‖x / g.impact x‖ ≤ max B 0
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  exact ⟨D * C, hphi.comp hC.lipschitzOnWith (fun t ht => ⟨hmin ht, hmax ht⟩)⟩

theorem AEOperationalClockSegment.potential_lipschitz_on
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun t => potential (fun i => coordinate F g.impact (m.prices t i)))
      (Icc m.a m.b) := by
  classical
  have hsum : ∀ s : Finset ι, ∃ C : ℝ≥0, LipschitzOnWith C
      (fun t => ∑ i ∈ s, coordinate F g.impact (m.prices t i)) (Icc m.a m.b) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simpa using (LipschitzWith.const (0 : ℝ)).lipschitzOnWith⟩
    | @insert i s hi ih =>
      obtain ⟨C, hC⟩ := m.coordinate_lipschitz_on hF i
      obtain ⟨D, hD⟩ := ih
      exact ⟨C + D, by simpa [Finset.sum_insert hi] using hC.add hD⟩
  simpa only [potential] using hsum Finset.univ

theorem AEOperationalClockSegment.integrating_factor_lipschitz_on
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun t => Real.exp (rho * m.physicalTime t) *
        potential (fun i => coordinate F g.impact (m.prices t i))) (Icc m.a m.b) := by
  obtain ⟨C, hC⟩ := m.physical_time_lipschitz
  have hc := hC.continuous.continuousOn (s := Icc m.a m.b)
  have hne : (Icc m.a m.b).Nonempty := ⟨m.a, le_rfl, m.time_order⟩
  obtain ⟨l, hl, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  obtain ⟨D, hD⟩ := rateBand_exp_lipschitz rho (m.physicalTime l) (m.physicalTime u)
  have he := hD.comp hC.lipschitzOnWith (fun t ht => ⟨hmin ht, hmax ht⟩)
  obtain ⟨E, hE⟩ := m.potential_lipschitz_on hF
  exact rateBand_lipschitz_mul he hE

theorem AEOperationalClockSegment.integrating_factor_FTC
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) :
    (∫ u in m.a..m.b,
      deriv (fun t => Real.exp (rho * m.physicalTime t) *
        potential (fun i => coordinate F g.impact (m.prices t i))) u) =
      Real.exp (rho * m.physicalTime m.b) *
        potential (fun i => coordinate F g.impact (m.prices m.b i)) -
      Real.exp (rho * m.physicalTime m.a) *
        potential (fun i => coordinate F g.impact (m.prices m.a i)) := by
  obtain ⟨C, hC⟩ := m.integrating_factor_lipschitz_on hF
  exact (lipschitzOn_integral_deriv_eq_sub hC m.time_order).2

theorem AEOperationalClockSegment.potential_nonnegative_of_visited_elasticity
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i)) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  exact m.potential_nonnegative_of_FTC_and_visited_elasticity
    F rho g edges hF hrho hdiff hinit hel (m.integrating_factor_FTC hF)

theorem AEOperationalClockSegment.no_systemic_crisis_of_visited_elasticity
    [Nonempty ι] (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Icc m.a m.b, ∀ i,
      2 ≤ responseElasticity g.impact (m.prices u i))
    (q : ι → ℝ) (hq : ∀ i, m.prices m.b i = F * Real.exp (q i)) (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  exact m.no_systemic_crisis_of_FTC_and_visited_elasticity
    F rho g edges hF hrho hdiff hinit hel (m.integrating_factor_FTC hF) q hq k

end MarketCrash
