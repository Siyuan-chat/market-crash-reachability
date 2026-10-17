import MarketCrash.OriginalResources

noncomputable section
namespace MarketCrash
open Set MeasureTheory

theorem variation_dominated_by_monotone_control (f G : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hG : MonotoneOn G (Icc a b))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → |f t - f s| ≤ G t - G s) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (G b - G a) := by
  have hmono : eVariationOn G (Icc a b) ≤ ENNReal.ofReal (G b - G a) := by
    simpa only [inter_self] using hG.eVariationOn_le ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  apply le_trans ?_ hmono
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (eVariationOn.sum_le G n hu hus)
  rw [edist_dist, edist_dist]
  apply ENNReal.ofReal_le_ofReal
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (hG (hus i) (hus (i+1)) (hu (Nat.le_succ i))))]
  exact hinc _ (hus i) _ (hus (i+1)) (hu (Nat.le_succ i))

theorem actualNegativeVariation_le_control (f G : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hG : MonotoneOn G (Icc a b))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → |f t - f s| ≤ G t - G s) :
    actualNegativeVariation f a b ≤ (G b - G a - (f b - f a)) / 2 := by
  have hh := variation_dominated_by_monotone_control f G a b hab hG hinc
  have hfinite : eVariationOn f (Icc a b) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hh
  have hv := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hG ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab))] at hv
  have he : variationOnFromTo f (Icc a b) a b = (eVariationOn f (Icc a b)).toReal := by
    rw [variationOnFromTo.eq_of_le f (Icc a b) hab, inter_self]
  unfold actualNegativeVariation
  rw [he]
  linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] in
theorem paired_column_abs_sum (edges : κ → PairedEdge ι) (e : κ) :
    (∑ i, |pairedMatrix edges i e|) = 2 := by
  have hh : ∀ i, |pairedMatrix edges i e| =
      (if i = (edges e).buyer then (1 : ℝ) else 0) +
      (if i = (edges e).seller then (1 : ℝ) else 0) := by
    intro i
    by_cases hb : i = (edges e).buyer <;> by_cases hs : i = (edges e).seller
    · exact False.elim ((edges e).distinct (hs.symm.trans hb))
    all_goals simp [pairedMatrix, hb, hs, (edges e).distinct, (edges e).distinct.symm]
  simp_rw [hh]
  norm_num [Finset.sum_add_distrib]

theorem paired_ledger_negative_variation_bound (edges : κ → PairedEdge ι)
    (Z : κ → ℝ → ℝ) (f : ι → ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hZ : ∀ e, MonotoneOn (Z e) (Icc a b))
    (hf : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      f i t - f i s = tradingInput (pairedMatrix edges) (fun e => Z e t - Z e s) i) :
    (∑ i, actualNegativeVariation (f i) a b) ≤ ∑ e, (Z e b - Z e a) := by
  let G := fun i t => ∑ e, |pairedMatrix edges i e| * Z e t
  have hG : ∀ i, MonotoneOn (G i) (Icc a b) := by
    intro i s hs t ht hst
    apply Finset.sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_left (hZ e hs ht hst) (abs_nonneg _)
  have hinc : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      |f i t - f i s| ≤ G i t - G i s := by
    intro i s hs t ht hst
    rw [hf i s hs t ht]
    simp only [tradingInput, G, ← Finset.sum_sub_distrib, ← mul_sub]
    apply (Finset.abs_sum_le_sum_abs _ _).trans_eq
    apply Finset.sum_congr rfl
    intro e _
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hZ e hs ht hst))]
  have hb := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => actualNegativeVariation_le_control (f i) (G i) a b hab (hG i) (hinc i))
  have hzero : (∑ i, (f i b - f i a)) = 0 := by
    simp_rw [hf _ a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩]
    exact paired_trading_sum_zero edges _
  have hg : (∑ i, (G i b - G i a)) = 2 * ∑ e, (Z e b - Z e a) := by
    simp only [G, ← Finset.sum_sub_distrib, ← mul_sub]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, paired_column_abs_sum]
    rw [Finset.mul_sum]
  simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib] at hb
  rw [← Finset.sum_sub_distrib, hg] at hb
  rw [← Finset.sum_sub_distrib, hzero] at hb
  linarith

variable {F rho : ι → ℝ} {response : ι → Response} {edges : κ → PairedEdge ι}
variable {s t : PhysicalMarketState ι}

theorem step_dollarSales_le_turnover
    (step : OriginalPhysicalStep F rho response edges s t) :
    (∑ i, step.dollarSales i) ≤ step.pairedTurnover := by
  cases step with
  | continuous m _ _ _ _ =>
    exact paired_ledger_negative_variation_bound edges
      (fun e => m.execution.cumulative e) (fun i a => m.dollarLedger a i)
      m.a m.b m.time_order (fun e => (m.execution.cumulative e).mono.monotoneOn _)
      m.marginal_dollar_primitive
  | pulse p _ _ _ =>
    have hh := paired_ledger_negative_variation_bound edges
      (fun e a => a * p.dollars e) (fun i a => p.dollarLedger a i) 0 1 (by norm_num)
      (fun e => (monotone_id.mul_const (p.nonnegative_dollars e)).monotoneOn _) (by
        intro i a ha b hb
        have h1 := p.marginal_dollar_primitive i a ha
        have h2 := p.marginal_dollar_primitive i b hb
        simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h1 h2
        rw [show p.dollarLedger b i - p.dollarLedger a i =
          b * tradingInput (pairedMatrix edges) p.dollars i -
          a * tradingInput (pairedMatrix edges) p.dollars i by linarith]
        simp only [tradingInput, Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro e _
        ring)
    simpa only [OriginalPhysicalStep.dollarSales, OriginalPhysicalStep.pairedTurnover,
      one_mul, zero_mul, sub_zero] using hh

theorem trace_dollarSales_le_turnover
    (trace : OriginalPhysicalReachable F rho response edges s t) :
    (∑ i, trace.dollarSales i) ≤ trace.pairedTurnover := by
  induction trace with
  | refl => simp [OriginalPhysicalReachable.dollarSales, OriginalPhysicalReachable.pairedTurnover]
  | append previous step ih =>
    simpa only [OriginalPhysicalReachable.dollarSales, OriginalPhysicalReachable.pairedTurnover,
      Finset.sum_add_distrib] using add_le_add ih (step_dollarSales_le_turnover step)

/-- Original Theorem 5.1: every terminal crisis requires the stated paired
dollar turnover and actual share-sale resources; each qualifying asset must
also satisfy its initial-inventory lower bound.

With k=ceil(alpha*N) and s=F*exp(-delta), every admissible terminal
crisis-attaining path satisfies
M >= -k*Phi(s) = k*integral_s^F u/g(u) du and
sum_i H_i^- >= -k*Psi(s) = k*integral_s^F 1/g(u) du.
For each qualifying asset with initial holding at most H_i and zero
terminal executed dollars, integral_s^F (F-u)/g(u) du <= F*H_i.
These are necessary conditions, not sufficiency claims. -/
theorem theorem_5_1_original [Nonempty ι]
    (F rho : ℝ) (g : Response)
    (p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) edges)
    (alpha delta : ℝ) (hα : 0 < alpha) (hα1 : alpha ≤ 1) (hδ : 0 < delta)
    (hcrisis : delta ≤ systemicCrisis (logPriceFromBenchmark F p.terminal.prices)
      (requiredAssetCount (ι := ι) alpha)) :
    (requiredAssetCount (ι := ι) alpha : ℝ) *
      (∫ u in F * Real.exp (-delta)..F, u / g.impact u) ≤ p.trace.pairedTurnover ∧
    (requiredAssetCount (ι := ι) alpha : ℝ) *
      (∫ u in F * Real.exp (-delta)..F, 1 / g.impact u) ≤ (∑ i, p.trace.shareSales i) ∧
    ∀ i H, delta ≤ Real.log (F / p.terminal.prices i) → p.initial.shares i ≤ H →
      (∫ u in F * Real.exp (-delta)..F, (F-u) / g.impact u) ≤ F * H := by
  obtain ⟨hd, hs⟩ := proposition_5_1_coordinate_resources F rho g p alpha delta hα hα1 hδ hcrisis
  exact ⟨hd.trans (trace_dollarSales_le_turnover p.trace), hs,
    fun i H hqual hholding => p.inventory_cap_for_qualifying_asset i delta H hδ hqual hholding⟩

end MarketCrash
