import MarketCrash.OriginalBarrier

noncomputable section
namespace MarketCrash
open Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
variable {edges : κ → PairedEdge ι}

theorem OriginalPhysicalReachable.actual_crisis_nonpositive_observed
    (F rho : ℝ) (g : Response) (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g.impact x)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => rho) (fun _ => g) edges s t)
    (hinit : ∀ i, s.prices i = F)
    (hel : ∀ i x, trace.Visited i x → 2 ≤ responseElasticity g.impact x)
    (o : PhysicalMarketState ι) (ho : trace.Observes o) (k : ℕ) :
    systemicCrisis (logPriceFromBenchmark F o.prices) k ≤ 0 := by
  have hp : ∀ i, 0 < o.prices i := fun i =>
    trace.visited_positive (fun j => by rw [hinit j]; exact hF) i _
      (trace.observed_prices_visited o ho i)
  have hpot := trace.potential_nonnegative_observed F rho g hF hrho hdiff hinit
    (fun i x hx => le_trans (by norm_num) (hel i x hx)) o ho
  have hq (i : ι) : F * Real.exp (logPriceFromBenchmark F o.prices i) = o.prices i :=
    exp_logPrice_eq_price F o.prices hF hp i
  have hlogpot : 0 ≤ ∑ i, logCoordinate F g.impact (logPriceFromBenchmark F o.prices i) := by
    have he : (∑ i, logCoordinate F g.impact (logPriceFromBenchmark F o.prices i)) =
        potential (fun i => coordinate F g.impact (o.prices i)) := by
      unfold potential
      apply Finset.sum_congr rfl
      intro i _
      change coordinate F g.impact (F * Real.exp (logPriceFromBenchmark F o.prices i)) = _
      rw [hq]
    rw [he]
    exact hpot
  apply no_positive_crisis_of_radial_elasticity_ge_two_and_potential
    F g hF (logPriceFromBenchmark F o.prices) k
    (hPotential := hlogpot)
  · intro i x _
    exact hdiff _ (mul_pos hF (Real.exp_pos x))
  · intro i x hx
    have hm : Monotone (fun y : ℝ => F * Real.exp y) :=
      fun u v huv => mul_le_mul_of_nonneg_left (Real.exp_monotone huv) hF.le
    have hb : F * Real.exp x ∈ uIcc F (o.prices i) := by
      have hbetween : F * Real.exp x ∈
          uIcc (F * Real.exp (0 : ℝ)) (F * Real.exp (logPriceFromBenchmark F o.prices i)) := by
        rcases le_total (0 : ℝ) (logPriceFromBenchmark F o.prices i) with hq0 | hq0
        · have hx' : 0 ≤ x ∧ x ≤ logPriceFromBenchmark F o.prices i := by
            simpa only [min_eq_left hq0, max_eq_right hq0] using hx
          rw [uIcc_of_le (hm hq0)]
          exact ⟨hm hx'.1, hm hx'.2⟩
        · have hx' : logPriceFromBenchmark F o.prices i ≤ x ∧ x ≤ 0 := by
            simpa only [min_eq_right hq0, max_eq_left hq0] using hx
          rw [uIcc_of_ge (hm hq0)]
          exact ⟨hm hx'.1, hm hx'.2⟩
      simpa only [Real.exp_zero, mul_one, hq] using hbetween
    exact trace.property_on_radial_at_observation
      (fun _ z => 2 ≤ responseElasticity g.impact z) hel hinit o ho i _ hb

/-- Original Theorem 3.2: If e(S) ≥ 2 on the admissible price range, then
for every admissible control, N ≥ 2, alpha in (0,1] and t in [0,T],
C_alpha(t) ≤ 0. Thus no strictly positive systemic terminal-crisis
threshold can be reached.

Original positive physical prices, exact ceiling coverage,
all physical times and every intermediate pulse observation of any finite trace.
Elasticity is imposed only on actual visited prices, never on all positive prices. -/
theorem theorem_3_2_original
    (F rho : ℝ) (g : Response) (hF : 0 < F) (hrho : 0 < rho)
    (_hN : 2 ≤ Fintype.card ι)
    (p : OriginalAdmissiblePhysicalPath (fun _ => F) (fun _ => rho) (fun _ => g) edges)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g.impact x)
    (hel : ∀ i x, p.trace.Visited i x → 2 ≤ responseElasticity g.impact x) :
    ∀ o, p.trace.Observes o → ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
      systemicCrisis (logPriceFromBenchmark F o.prices) (requiredAssetCount (ι := ι) alpha) ≤ 0 ∧
      ∀ δ : ℝ, 0 < δ →
        ¬ δ ≤ systemicCrisis (logPriceFromBenchmark F o.prices) (requiredAssetCount (ι := ι) alpha) := by
  intro o ho alpha _ _
  have hh := p.trace.actual_crisis_nonpositive_observed F rho g hF hrho.le hdiff
    p.initial_prices hel o ho (requiredAssetCount (ι := ι) alpha)
  exact ⟨hh, fun δ hδ hreach => (not_lt_of_ge hh) (hδ.trans_le hreach)⟩

end MarketCrash
