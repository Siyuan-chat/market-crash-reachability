import MarketCrash.PhysicalBVNormalForm
import MarketCrash.OriginalVisitedPrices
import MarketCrash.CrisisQuantile

noncomputable section
namespace MarketCrash
open Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

/-- The global radial condition is inherited by every piece; no piece is reset to F. -/
theorem OriginalPhysicalReachable.potential_nonnegative_observed_of_radial
    (F rho : ℝ) (g : Response) (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g.impact x)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => rho) (fun _ => g) edges s t)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (s.prices i)))
    (hrad : ∀ o, trace.Observes o → ∀ i x, x ∈ uIcc F (o.prices i) →
      1 ≤ responseElasticity g.impact x) :
    ∀ o, trace.Observes o → 0 ≤ potential (fun i => coordinate F g.impact (o.prices i)) := by
  induction trace with
  | refl =>
    intro o ho
    change o = s at ho
    subst o
    exact hstart
  | @append mid t previous step ih =>
    have hprev := ih (fun o ho => hrad o (Or.inl ho))
    have hmid := hprev mid previous.observes_terminal
    intro o ho
    rcases ho with ho | ho
    · exact hprev o ho
    · cases step with
      | continuous m hbm hrm hgm hvar =>
        obtain ⟨u, hu, rfl⟩ := ho
        let w := m.toWeak F rho g (fun i => congrFun hbm i)
          (fun i => congrFun hrm i) (fun i => congrFun hgm i)
        apply w.potential_nonnegative_of_radial_elasticity F rho g edges hF hrho hdiff
          (hstart := hmid) (t := u) (ht := hu)
        intro v hv i x hx
        exact hrad ⟨v, m.prices v, m.shares v, m.dollarLedger v⟩
          (Or.inr ⟨v, hv, rfl⟩) i x hx
      | pulse p hbm hgm hvar =>
        obtain ⟨u, hu, rfl⟩ := ho
        have hh := p.potential_at_parameter u hu
        have he : potential (fun i => coordinate F g.impact (p.prices u i)) =
            potential (fun i => coordinate F g.impact (p.prices 0 i)) := by
          simpa only [hbm, hgm] using hh
        rw [he]
        exact hmid

theorem OriginalPhysicalReachable.potential_nonnegative_observed
    (F rho : ℝ) (g : Response) (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g.impact x)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => rho) (fun _ => g) edges s t)
    (hinit : ∀ i, s.prices i = F)
    (hel : ∀ i x, trace.Visited i x → 1 ≤ responseElasticity g.impact x) :
    ∀ o, trace.Observes o → 0 ≤ potential (fun i => coordinate F g.impact (o.prices i)) := by
  apply trace.potential_nonnegative_observed_of_radial F rho g hF hrho hdiff
  · simp [hinit, potential, coordinate_at_benchmark]
  · intro o ho i x hx
    exact trace.property_on_radial_at_observation
      (fun _ x => 1 ≤ responseElasticity g.impact x) hel hinit o ho i x hx

omit [DecidableEq ι] in
theorem actual_full_coverage_crisis_nonpositive [Nonempty ι]
    (F : ℝ) (prices : ι → ℝ) (hF : 0 < F) (hp : ∀ i, 0 < prices i)
    (hnot : ¬ ∀ i, prices i < F)
    (alpha : ℝ) (hα : 0 < alpha) (hα1 : alpha ≤ 1)
    (hk : requiredAssetCount (ι := ι) alpha = Fintype.card ι) :
    systemicCrisis (logPriceFromBenchmark F prices) (requiredAssetCount (ι := ι) alpha) ≤ 0 := by
  classical
  by_contra hbad
  have hδ : 0 < systemicCrisis (logPriceFromBenchmark F prices) (requiredAssetCount (ι := ι) alpha) :=
    lt_of_not_ge hbad
  have hh := (actual_systemic_crisis_threshold_iff F prices hF hp alpha hα hα1 _).mp le_rfl
  rw [hk] at hh
  have he : (Finset.univ.filter (fun i : ι =>
      systemicCrisis (logPriceFromBenchmark F prices) (Fintype.card ι) ≤ actualLogLoss F prices i)) =
      Finset.univ := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa using hh.2)
  apply hnot
  intro i
  have hi : systemicCrisis (logPriceFromBenchmark F prices) (Fintype.card ι) ≤ actualLogLoss F prices i := by
    have hm : i ∈ Finset.univ.filter (fun j : ι =>
        systemicCrisis (logPriceFromBenchmark F prices) (Fintype.card ι) ≤ actualLogLoss F prices j) := by
      rw [he]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hm).2
  rw [hk] at hδ
  have hl : 0 < Real.log (F / prices i) := hδ.trans_le hi
  have hg : 1 < F / prices i := (Real.log_pos_iff (div_pos hF (hp i)).le).mp hl
  simpa using (lt_div_iff₀ (hp i)).mp hg

/-- Original Theorem 3.1: If e(S) ≥ 1 at all prices attainable by admissible
paths, then S_i(t) < F for every i is impossible at any time t. In particular,
no positive crisis with k = N is reachable.

Full original physical trace, all continuous and pulse-interior observations.
Elasticity is required only at prices actually visited by this same path. -/
theorem theorem_3_1_original [Nonempty ι]
    (F rho : ℝ) (g : Response) (hF : 0 < F) (hrho : 0 < rho)
    (_hN : 2 ≤ Fintype.card ι)
    (p : OriginalAdmissiblePhysicalPath (fun _ => F) (fun _ => rho) (fun _ => g) edges)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g.impact x)
    (hel : ∀ i x, p.trace.Visited i x → 1 ≤ responseElasticity g.impact x) :
    ∀ o, p.trace.Observes o →
      0 ≤ potential (fun i => coordinate F g.impact (o.prices i)) ∧
      (¬ ∀ i, o.prices i < F) ∧
      (∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
        requiredAssetCount (ι := ι) alpha = Fintype.card ι →
        systemicCrisis (logPriceFromBenchmark F o.prices) (requiredAssetCount (ι := ι) alpha) ≤ 0 ∧
        ∀ δ : ℝ, 0 < δ →
          ¬ δ ≤ systemicCrisis (logPriceFromBenchmark F o.prices) (requiredAssetCount (ι := ι) alpha)) := by
  intro o ho
  have hpot := p.trace.potential_nonnegative_observed F rho g hF hrho.le hdiff p.initial_prices hel o ho
  have hp : ∀ i, 0 < o.prices i := fun i =>
    p.trace.visited_positive (fun j => by rw [p.initial_prices j]; exact hF) i _
      (p.trace.observed_prices_visited o ho i)
  have hnot := not_all_below_benchmark F g hF o.prices hp hpot
  refine ⟨hpot, hnot, ?_⟩
  intro alpha hα hα1 hk
  have hh := actual_full_coverage_crisis_nonpositive F o.prices hF hp hnot alpha hα hα1 hk
  exact ⟨hh, fun δ hδ hreach => (not_lt_of_ge hh) (hδ.trans_le hreach)⟩

end MarketCrash
