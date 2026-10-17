import MarketCrash.OriginalCertificate
import MarketCrash.CertificateTurnover
import MarketCrash.CertifiedRateLower
import MarketCrash.CertificateInventory
import MarketCrash.FiniteRateConstruction
import MarketCrash.ResponseFamilies

noncomputable section
namespace MarketCrash.OriginalCertificate
open Set MeasureTheory Filter

theorem local_if_le_continuousAt (f g : ℝ → ℝ) (b t : ℝ) (hne : t ≠ b)
    (hf : ContinuousAt f t) (hg : ContinuousAt g t) :
    ContinuousAt (fun s => if s ≤ b then f s else g s) t := by
  by_cases hlt : t < b
  · apply hf.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with s hs
    change s < b at hs
    simp only [if_pos hs.le]
  · have hgt : b < t := lt_of_le_of_ne (le_of_not_gt hlt) hne.symm
    apply hg.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with s hs
    change b < s at hs
    simp only [if_neg (not_le.mpr hs)]

theorem targetVelocity_continuousAt_away (h t : ℝ)
    (h₁ : t ≠ 23 / 10) (h₂ : t ≠ 177 / 10) (h₃ : t ≠ 20)
    (h₄ : t ≠ 223 / 10) (h₅ : t ≠ 377 / 10) : ContinuousAt (targetVelocity h) t := by
  unfold targetVelocity
  apply local_if_le_continuousAt _ _ _ _ h₁ continuousAt_const
  apply local_if_le_continuousAt _ _ _ _ h₂ continuousAt_const
  apply local_if_le_continuousAt _ _ _ _ h₃ continuousAt_const
  apply local_if_le_continuousAt _ _ _ _ h₄ continuousAt_const
  exact local_if_le_continuousAt _ _ _ _ h₅ continuousAt_const continuousAt_const

theorem actualTargetDollars_continuousAt_away (h t : ℝ)
    (h₁ : t ≠ 23 / 10) (h₂ : t ≠ 177 / 10) (h₃ : t ≠ 20)
    (h₄ : t ≠ 223 / 10) (h₅ : t ≠ 377 / 10) : ContinuousAt (actualTargetDollars h) t := by
  have hx := (targetSchedule_continuous h).continuousAt (x := t)
  exact hx.mul ((targetVelocity_continuousAt_away h t h₁ h₂ h₃ h₄ h₅).add
    (continuousAt_const.mul (hx.sub continuousAt_const)))

theorem targetVelocity_measurable (h : ℝ) : Measurable (targetVelocity h) := by
  unfold targetVelocity
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const
      (Measurable.ite measurableSet_Iic measurable_const
        (Measurable.ite measurableSet_Iic measurable_const
          (Measurable.ite measurableSet_Iic measurable_const measurable_const))))

theorem actualTargetDollars_measurable (h : ℝ) : Measurable (actualTargetDollars h) := by
  exact (targetSchedule_continuous h).measurable.mul ((targetVelocity_measurable h).add
    (measurable_const.mul ((targetSchedule_continuous h).measurable.sub measurable_const)))

theorem target_controls_measurable (h : ℝ) :
    Measurable (fun t => targetBuyingDollars (actualTargetDollars h t)) ∧
      Measurable (fun t => targetSellingDollars (actualTargetDollars h t)) := by
  exact ⟨(actualTargetDollars_measurable h).max measurable_const,
    (actualTargetDollars_measurable h).neg.max measurable_const⟩

theorem target_cumulatives_hasDerivAt (h t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 40)
    (h₁ : t ≠ 23 / 10) (h₂ : t ≠ 177 / 10) (h₃ : t ≠ 20)
    (h₄ : t ≠ 223 / 10) (h₅ : t ≠ 377 / 10) :
    HasDerivAt (targetBuyingCumulative h) (targetBuyingDollars (actualTargetDollars h t)) t ∧
      HasDerivAt (targetSellingCumulative h) (targetSellingDollars (actualTargetDollars h t)) t := by
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc (0 : ℝ) 40 := by
    rw [uIcc_of_le ht.1.le, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 40)]
    exact fun u hu => ⟨hu.1, hu.2.trans ht.2.le⟩
  have hc := actualTargetDollars_continuousAt_away h t h₁ h₂ h₃ h₄ h₅
  have hm := target_controls_measurable h
  constructor
  · exact intervalIntegral.integral_hasDerivAt_right
      ((actual_target_gross_integrable h).1.mono_set hsub)
      hm.1.stronglyMeasurable.stronglyMeasurableAtFilter (hc.max continuousAt_const)
  · exact intervalIntegral.integral_hasDerivAt_right
      ((actual_target_gross_integrable h).2.mono_set hsub)
      hm.2.stronglyMeasurable.stronglyMeasurableAtFilter (hc.neg.max continuousAt_const)

theorem target_cumulatives_ae_derivative (h : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 40 →
      HasDerivAt (targetBuyingCumulative h) (targetBuyingDollars (actualTargetDollars h t)) t ∧
      HasDerivAt (targetSellingCumulative h) (targetSellingDollars (actualTargetDollars h t)) t := by
  have hne (r : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ r := by rw [ae_iff]; simp
  filter_upwards [hne 0, hne 40, hne (23 / 10), hne (177 / 10), hne 20,
    hne (223 / 10), hne (377 / 10)] with t h0 h40 h1 h2 h3 h4 h5 ht
  exact target_cumulatives_hasDerivAt h t
    ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h40⟩ h1 h2 h3 h4 h5

theorem targetVelocity_abs_bound (h t : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper) :
    |targetVelocity h t| ≤ 3 / 125 := by
  have hu : h ≤ 1021 / 1000 := hh.2.trans (by norm_num [plateauUpper])
  unfold targetVelocity
  split_ifs <;> rw [abs_le] <;> constructor <;> norm_num <;> linarith [hh.1, hu]

theorem targetSchedule_global_bounds (h t : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (ht : t ∈ Icc (0 : ℝ) 40) :
    47 / 50 ≤ targetSchedule h t ∧ targetSchedule h t ≤ 103 / 100 := by
  have hh' : h ∈ Icc (1 : ℝ) (103 / 100) :=
    ⟨hh.1, hh.2.trans (by norm_num [plateauUpper])⟩
  by_cases ht20 : t ≤ 20
  · have hb := (targetSchedule_rolling_bands h hh').1 t ⟨ht.1, ht20⟩
    constructor <;> linarith [hb.1, hb.2]
  · have hb := (targetSchedule_rolling_bands h hh').2 t ⟨le_of_not_ge ht20, ht.2⟩
    constructor <;> linarith [hb.1, hb.2]

theorem actualTargetDollars_abs_bound (h t : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (ht : t ∈ Icc (0 : ℝ) 40) : |actualTargetDollars h t| ≤ 1 / 20 := by
  have hx := targetSchedule_global_bounds h t hh ht
  have hv := targetVelocity_abs_bound h t hh
  have hdev : |targetSchedule h t - 1| ≤ 3 / 50 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hfac : |targetVelocity h t + (2 / 5 : ℝ) * (targetSchedule h t - 1)| ≤ 6 / 125 := by
    calc
      _ ≤ |targetVelocity h t| + |(2 / 5 : ℝ) * (targetSchedule h t - 1)| := abs_add _ _
      _ = |targetVelocity h t| + (2 / 5 : ℝ) * |targetSchedule h t - 1| := by rw [abs_mul]; norm_num
      _ ≤ 6 / 125 := by linarith
  have hxa : |targetSchedule h t| ≤ 103 / 100 := by rw [abs_of_nonneg (by linarith [hx.1])]; exact hx.2
  unfold actualTargetDollars
  rw [abs_mul]
  calc
    _ ≤ (103 / 100 : ℝ) * (6 / 125) := mul_le_mul hxa hfac (abs_nonneg _) (by norm_num)
    _ ≤ 1 / 20 := by norm_num

theorem target_controls_bound (h t : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (ht : t ∈ Icc (0 : ℝ) 40) :
    |targetBuyingDollars (actualTargetDollars h t)| ≤ 1 / 20 ∧
      |targetSellingDollars (actualTargetDollars h t)| ≤ 1 / 20 := by
  have hu := actualTargetDollars_abs_bound h t hh ht
  have hb := directed_dollar_controls (actualTargetDollars h t)
  rw [abs_of_nonneg hb.1, abs_of_nonneg hb.2.1]
  constructor
  · exact (max_le (le_abs_self _) (abs_nonneg _)).trans hu
  · exact (max_le (neg_le_abs _) (abs_nonneg _)).trans hu

theorem target_cumulatives_lipschitz (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper) :
    LipschitzOnWith (1 / 20 : NNReal) (targetBuyingCumulative h) (Icc (0 : ℝ) 40) ∧
      LipschitzOnWith (1 / 20 : NNReal) (targetSellingCumulative h) (Icc (0 : ℝ) 40) := by
  constructor
  · apply integral_primitive_lipschitz _ 0 40 (by norm_num) (1 / 20 : NNReal)
      (actual_target_gross_integrable h).1
    exact Eventually.of_forall (fun t ht => (target_controls_bound h t hh ht).1)
  · apply integral_primitive_lipschitz _ 0 40 (by norm_num) (1 / 20 : NNReal)
      (actual_target_gross_integrable h).2
    exact Eventually.of_forall (fun t ht => (target_controls_bound h t hh ht).2)

theorem target_stieltjes_global_lipschitz (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper) :
    LipschitzWith (1 / 20 : NNReal) (targetBuyingStieltjes h) ∧
      LipschitzWith (1 / 20 : NNReal) (targetSellingStieltjes h) := by
  exact ⟨finiteContinuousStieltjesExtension_lipschitz 0 40 (by norm_num) _
    (targetBuyingCumulative_monotone h) (targetBuyingCumulative_continuous h) _
    (target_cumulatives_lipschitz h hh).1,
    finiteContinuousStieltjesExtension_lipschitz 0 40 (by norm_num) _
      (targetSellingCumulative_monotone h) (targetSellingCumulative_continuous h) _
      (target_cumulatives_lipschitz h hh).2⟩

theorem target_stieltjes_ae_derivative (h : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 40 →
      HasDerivAt (targetBuyingStieltjes h) (targetBuyingDollars (actualTargetDollars h t)) t ∧
      HasDerivAt (targetSellingStieltjes h) (targetSellingDollars (actualTargetDollars h t)) t := by
  have hne (r : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ r := by rw [ae_iff]; simp
  filter_upwards [target_cumulatives_ae_derivative h, hne 0, hne 40] with t hd h0 h40 ht
  have hti : t ∈ Ioo (0 : ℝ) 40 :=
    ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h40⟩
  constructor
  · apply ((hd ht).1).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
    exact targetBuyingStieltjes_eq h s ⟨hs.1.le, hs.2.le⟩
  · apply ((hd ht).2).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
    exact targetSellingStieltjes_eq h s ⟨hs.1.le, hs.2.le⟩

def certificateRates (h t : ℝ) (e : Fin 9 × Bool) : ℝ :=
  directedAmounts (targetBuyingDollars (actualTargetDollars h t))
    (targetSellingDollars (actualTargetDollars h t)) e

theorem certificate_execution_density (h : ℝ) :
    ∀ᵐ t ∂volume, t ∈ Icc (0 : ℝ) 40 → ∀ e : Fin 9 × Bool,
      HasDerivAt ((certificateExecution h).cumulative e) (certificateRates h t e) t := by
  filter_upwards [target_stieltjes_ae_derivative h] with t hd ht e
  by_cases he : e.2
  · simpa only [certificateExecution, certificateRates, directedAmounts, if_pos he] using (hd ht).1
  · simpa only [certificateExecution, certificateRates, directedAmounts, if_neg he] using (hd ht).2

theorem certificate_execution_lipschitz (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (e : Fin 9 × Bool) : LipschitzWith (1 / 20 : NNReal) ((certificateExecution h).cumulative e) := by
  by_cases he : e.2
  · simpa only [certificateExecution, if_pos he] using (target_stieltjes_global_lipschitz h hh).1
  · simpa only [certificateExecution, if_neg he] using (target_stieltjes_global_lipschitz h hh).2

theorem certificate_edge_primitive (h t : ℝ) (e : Fin 9 × Bool) (ht : t ∈ Icc (0 : ℝ) 40) :
    (certificateExecution h).cumulative e t - (certificateExecution h).cumulative e 0 =
      ∫ u in (0 : ℝ)..t, certificateRates h u e := by
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) 40 := by norm_num
  by_cases he : e.2
  · simp only [certificateExecution, certificateRates, directedAmounts, if_pos he,
      targetBuyingStieltjes_eq h t ht, targetBuyingStieltjes_eq h 0 hz]
    simp [targetBuyingCumulative]
  · simp only [certificateExecution, certificateRates, directedAmounts, if_neg he,
      targetSellingStieltjes_eq h t ht, targetSellingStieltjes_eq h 0 hz]
    simp [targetSellingCumulative]

theorem certificate_input_rate (h t : ℝ) (i : Fin 10) :
    tradingInput (pairedMatrix certificateEdges) (certificateRates h t) i =
      if i.val < 9 then actualTargetDollars h t else -9 * actualTargetDollars h t := by
  change tradingInput (pairedMatrix certificateEdges)
    (directedAmounts (targetBuyingDollars (actualTargetDollars h t))
      (targetSellingDollars (actualTargetDollars h t))) i = _
  rw [certificate_directed_input, (directed_dollar_controls _).2.2.1]

def certificateField (h : ℝ) (Y : ℝ → ℝ) (t : ℝ) (i : Fin 10) : ℝ :=
  -(2 / 5 : ℝ) * (certificatePrices h Y t i - 1) +
    tradingInput (pairedMatrix certificateEdges) (certificateRates h t) i / certificatePrices h Y t i

theorem certificate_prices_ae_ode (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (Y : ℝ → ℝ)
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 40 →
      HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t) :
    ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 40 → ∀ i : Fin 10,
      HasDerivAt (fun u => certificatePrices h Y u i) (certificateField h Y t i) t := by
  have hh' : h ∈ Icc (1 : ℝ) (103 / 100) :=
    ⟨hh.1, hh.2.trans (by norm_num [plateauUpper])⟩
  filter_upwards [targetSchedule_actual_ode h hh', hYd] with t hx hy ht i
  by_cases hi : i.val < 9
  · have he : certificateField h Y t i =
        compensatorField (-actualTargetDollars h t / 9) (targetSchedule h t) := by
      rw [certificateField, certificate_input_rate]
      simp only [certificatePrices, if_pos hi]
      unfold compensatorField
      ring
    simpa only [certificatePrices, if_pos hi, he] using hx ht
  · have he : certificateField h Y t i =
        compensatorField (actualTargetDollars h t) (Y t) := by
      rw [certificateField, certificate_input_rate]
      simp only [certificatePrices, if_neg hi]
      unfold compensatorField
      ring
    simpa only [certificatePrices, if_neg hi, he] using hy ht

theorem certificate_prices_lipschitz (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (Y : ℝ → ℝ) (hYL : LipschitzOnWith (17 / 10 : NNReal) Y (Icc (0 : ℝ) 40))
    (i : Fin 10) : LipschitzOnWith (17 / 10 : NNReal)
      (fun t => certificatePrices h Y t i) (Icc (0 : ℝ) 40) := by
  by_cases hi : i.val < 9
  · have hh' : h ∈ Icc (1 : ℝ) (103 / 100) :=
      ⟨hh.1, hh.2.trans (by norm_num [plateauUpper])⟩
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    simp only [certificatePrices, if_pos hi]
    calc
      _ ≤ (3 / 100 : NNReal) * dist s t := (targetSchedule_lipschitz h hh').dist_le_mul s hs t ht
      _ ≤ (17 / 10 : NNReal) * dist s t := mul_le_mul_of_nonneg_right (by norm_num) dist_nonneg
  · simpa only [certificatePrices, if_neg hi] using hYL

theorem certificate_prices_primitive (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (Y : ℝ → ℝ) (hYL : LipschitzOnWith (17 / 10 : NNReal) Y (Icc (0 : ℝ) 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 40 →
      HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (i : Fin 10) (s t : ℝ) (hs : s ∈ Icc (0 : ℝ) 40) (ht : t ∈ Icc (0 : ℝ) 40) :
    certificatePrices h Y t i - certificatePrices h Y s i =
      ∫ u in s..t, certificateField h Y u i := by
  have ha := certificate_prices_ae_ode h hh Y hYd
  have ordered (a b : ℝ) (ha' : a ∈ Icc (0 : ℝ) 40) (hb' : b ∈ Icc (0 : ℝ) 40)
      (hab : a ≤ b) : certificatePrices h Y b i - certificatePrices h Y a i =
        ∫ u in a..b, certificateField h Y u i := by
    have hl := (certificate_prices_lipschitz h hh Y hYL i).mono
      (show Icc a b ⊆ Icc (0 : ℝ) 40 from fun _ hu => ⟨ha'.1.trans hu.1, hu.2.trans hb'.2⟩)
    have hd : ∀ᵐ u ∂volume, u ∈ Ioo a b →
        HasDerivAt (fun v => certificatePrices h Y v i) (certificateField h Y u i) u := by
      filter_upwards [ha] with u hu hm
      exact hu ⟨ha'.1.trans_lt hm.1, hm.2.trans_le hb'.2⟩ i
    exact (lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hl hab hd).2.symm
  by_cases hst : s ≤ t
  · exact ordered s t hs ht hst
  · have hh' := ordered t s ht hs (le_of_not_ge hst)
    rw [intervalIntegral.integral_symm]
    linarith

def certificateACSession (h : ℝ) (hh : h ∈ Icc (1 : ℝ) plateauUpper)
    (Y : ℝ → ℝ) (hYL : LipschitzOnWith (17 / 10 : NNReal) Y (Icc (0 : ℝ) 40))
    (hYs : ∀ t ∈ Icc (0 : ℝ) 40, Y t ∈ Icc (7 / 10 : ℝ) (8 / 5))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) 40 →
      HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t) :
    ACPhysicalSession certificateEdges where
  a := 0
  b := 40
  time_order := by norm_num
  F := fun _ => 1
  rho := fun _ => 2 / 5
  response := fun _ => constantResponse 1 (by norm_num)
  benchmark_positive := fun _ => by norm_num
  resilience_nonnegative := fun _ => by norm_num
  prices := certificatePrices h Y
  rates := certificateRates h
  edgeDollars := fun t e => (certificateExecution h).cumulative e t
  continuous_prices := fun i => (certificate_prices_lipschitz h hh Y hYL i).continuousOn
  positive_prices := by
    intro t ht i
    by_cases hi : i.val < 9
    · simp only [certificatePrices, if_pos hi]
      linarith [(targetSchedule_global_bounds h t hh ht).1]
    · simp only [certificatePrices, if_neg hi]
      linarith [(hYs t ht).1]
  rates_integrable := by
    intro e
    by_cases he : e.2
    · simpa only [certificateRates, directedAmounts, if_pos he] using (actual_target_gross_integrable h).1
    · simpa only [certificateRates, directedAmounts, if_neg he] using (actual_target_gross_integrable h).2
  nonnegative_rates := Eventually.of_forall (fun t _ e => by
    by_cases he : e.2
    · simpa only [certificateRates, directedAmounts, if_pos he] using (directed_dollar_controls (actualTargetDollars h t)).1
    · simpa only [certificateRates, directedAmounts, if_neg he] using (directed_dollar_controls (actualTargetDollars h t)).2.1)
  edge_primitive := fun e t ht => certificate_edge_primitive h t e ht
  edge_derivative := certificate_execution_density h
  physical_primitive := by
    intro i s hs t ht
    simpa only [constantResponse, one_mul, certificateField] using
      certificate_prices_primitive h hh Y hYL hYd i s t hs ht
  physical_derivative := by
    have hne (r : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ r := by rw [ae_iff]; simp
    filter_upwards [certificate_prices_ae_ode h hh Y hYd, hne 0, hne 40] with t hd h0 h40 ht i
    simpa only [constantResponse, one_mul, certificateField] using
      hd ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h40⟩ i

-- BEGIN D01 HYBRID CHECKER

namespace HybridCertificate
open RationalInterval RationalInterval.CertificateReplay
open RationalInterval.CertificateReplay.IntegerReplay

def endpointBox (A B : IntegerReplay.Interval) (motion : Int) : IntegerReplay.Interval :=
  ⟨(A.lo + B.lo - motion) / 2, IntegerReplay.ceilDiv (A.hi + B.hi + motion) 2⟩

structure Bounds where
  coarse : IntegerReplay.Interval
  refined : IntegerReplay.Interval
  target : IntegerReplay.Interval
  dollars : IntegerReplay.Interval
  field : IntegerReplay.Interval
  magnitude : Int

def build (s : IntegerReplay.Segment) (j n : ℕ)
    (A B : IntegerReplay.Interval) : Bounds := Id.run do
  let dt := IntegerReplay.lit ((n : ℚ) / 2000)
  let motion := (IntegerReplay.multiply (IntegerReplay.lit (17 / 10)) dt).hi
  let yy := endpointBox A B motion
  let xa := IntegerReplay.plus s.x₀ (IntegerReplay.multiply s.velocity (IntegerReplay.lit ((j : ℚ) / 2000)))
  let xb := IntegerReplay.plus s.x₀ (IntegerReplay.multiply s.velocity (IntegerReplay.lit (((j + n : ℕ) : ℚ) / 2000)))
  let xx := IntegerReplay.Interval.mk (min xa.lo xb.lo) (max xa.hi xb.hi)
  let u := IntegerReplay.multiply xx (IntegerReplay.plus s.velocity
    (IntegerReplay.multiply (IntegerReplay.lit (2 / 5)) (IntegerReplay.minus xx (IntegerReplay.lit 1))))
  let field := IntegerReplay.minus
    (IntegerReplay.negate (IntegerReplay.multiply (IntegerReplay.lit (2 / 5)) (IntegerReplay.minus yy (IntegerReplay.lit 1))))
    (IntegerReplay.quotient (IntegerReplay.multiply (IntegerReplay.lit 9) u) yy)
  let M := max |field.lo| |field.hi|
  let motion' := (IntegerReplay.multiply ⟨M, M⟩ dt).hi
  let yy' := endpointBox A B motion'
  return ⟨yy, ⟨max yy.lo yy'.lo, min yy.hi yy'.hi⟩, xx, u, field, M⟩

def checkBounds (g : ℕ) (c : Bounds) : Bool := Id.run do
  let absU := max |c.dollars.lo| |c.dollars.hi|
  let reference := IntegerReplay.state 400
  let band := if g < 400 then
      decide (3 * IntegerReplay.Q / 4 < c.refined.lo) && decide (c.refined.hi < 5 * IntegerReplay.Q / 4)
    else decide (3 * reference.enclosure.hi < 4 * c.refined.lo) &&
      decide (4 * c.refined.hi < 5 * reference.enclosure.lo)
  return decide (0 < c.coarse.lo) && decide (c.coarse.lo ≤ c.coarse.hi) &&
    decide (0 < c.target.lo) && decide (0 < c.refined.lo) &&
    decide (9 * absU * 1000000 < 284481 * c.refined.lo) &&
    decide (absU * 1000000 < 284481 * c.target.lo) && band

def coarseBounds (g : ℕ) : Bounds := build (IntegerReplay.segment g) (blockStart g) 100
  (IntegerReplay.state g).enclosure (IntegerReplay.state (g + 1)).enclosure

def checkCoarse (g : ℕ) : Bool := checkBounds g (coarseBounds g)
def checkCoarseRange (start count : ℕ) : Bool := (List.range count).all (fun j => checkCoarse (start + j))

def microBounds (g m : ℕ) : Bounds := build (IntegerReplay.segment g) (blockStart g + m) 1
  (ResourceCertificate.stateAt (100 * g + m)).enclosure
  (ResourceCertificate.stateAt (100 * g + m + 1)).enclosure

def checkMicro (g m : ℕ) : Bool := checkBounds g (microBounds g m)
def checkMicroRange (g start count : ℕ) : Bool := (List.range count).all (fun j => checkMicro g (start + j))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_000 : checkCoarseRange 0 10 = true := by decide +kernel
#print axioms kernel_coarse_000
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_010 : checkCoarseRange 10 10 = true := by decide +kernel
#print axioms kernel_coarse_010
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_020 : checkCoarseRange 20 10 = true := by decide +kernel
#print axioms kernel_coarse_020
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_030 : checkCoarseRange 30 10 = true := by decide +kernel
#print axioms kernel_coarse_030
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_040 : checkCoarseRange 40 10 = true := by decide +kernel
#print axioms kernel_coarse_040
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_050 : checkCoarseRange 50 10 = true := by decide +kernel
#print axioms kernel_coarse_050
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_060 : checkCoarseRange 60 10 = true := by decide +kernel
#print axioms kernel_coarse_060
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_070 : checkCoarseRange 70 10 = true := by decide +kernel
#print axioms kernel_coarse_070
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_080 : checkCoarseRange 80 10 = true := by decide +kernel
#print axioms kernel_coarse_080
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_090 : checkCoarseRange 90 10 = true := by decide +kernel
#print axioms kernel_coarse_090
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_100 : checkCoarseRange 100 10 = true := by decide +kernel
#print axioms kernel_coarse_100
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_110 : checkCoarseRange 110 10 = true := by decide +kernel
#print axioms kernel_coarse_110
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_120 : checkCoarseRange 120 10 = true := by decide +kernel
#print axioms kernel_coarse_120
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_130 : checkCoarseRange 130 10 = true := by decide +kernel
#print axioms kernel_coarse_130
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_140 : checkCoarseRange 140 10 = true := by decide +kernel
#print axioms kernel_coarse_140
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_150 : checkCoarseRange 150 10 = true := by decide +kernel
#print axioms kernel_coarse_150
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_160 : checkCoarseRange 160 10 = true := by decide +kernel
#print axioms kernel_coarse_160
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_170 : checkCoarseRange 170 10 = true := by decide +kernel
#print axioms kernel_coarse_170
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_180 : checkCoarseRange 180 10 = true := by decide +kernel
#print axioms kernel_coarse_180
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_190 : checkCoarseRange 190 10 = true := by decide +kernel
#print axioms kernel_coarse_190
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_200 : checkCoarseRange 200 10 = true := by decide +kernel
#print axioms kernel_coarse_200
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_210 : checkCoarseRange 210 10 = true := by decide +kernel
#print axioms kernel_coarse_210
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_220 : checkCoarseRange 220 10 = true := by decide +kernel
#print axioms kernel_coarse_220
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_230 : checkCoarseRange 230 10 = true := by decide +kernel
#print axioms kernel_coarse_230
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_240 : checkCoarseRange 240 10 = true := by decide +kernel
#print axioms kernel_coarse_240
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_250 : checkCoarseRange 250 10 = true := by decide +kernel
#print axioms kernel_coarse_250
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_260 : checkCoarseRange 260 10 = true := by decide +kernel
#print axioms kernel_coarse_260
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_270 : checkCoarseRange 270 10 = true := by decide +kernel
#print axioms kernel_coarse_270
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_280 : checkCoarseRange 280 10 = true := by decide +kernel
#print axioms kernel_coarse_280
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_290 : checkCoarseRange 290 10 = true := by decide +kernel
#print axioms kernel_coarse_290
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_300 : checkCoarseRange 300 10 = true := by decide +kernel
#print axioms kernel_coarse_300
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_310 : checkCoarseRange 310 10 = true := by decide +kernel
#print axioms kernel_coarse_310
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_320 : checkCoarseRange 320 10 = true := by decide +kernel
#print axioms kernel_coarse_320
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_330 : checkCoarseRange 330 10 = true := by decide +kernel
#print axioms kernel_coarse_330
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_340 : checkCoarseRange 340 10 = true := by decide +kernel
#print axioms kernel_coarse_340
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_350 : checkCoarseRange 350 10 = true := by decide +kernel
#print axioms kernel_coarse_350
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_360 : checkCoarseRange 360 10 = true := by decide +kernel
#print axioms kernel_coarse_360
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_370 : checkCoarseRange 370 10 = true := by decide +kernel
#print axioms kernel_coarse_370
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_380 : checkCoarseRange 380 10 = true := by decide +kernel
#print axioms kernel_coarse_380
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_390 : checkCoarseRange 390 10 = true := by decide +kernel
#print axioms kernel_coarse_390
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_400 : checkCoarseRange 400 10 = true := by decide +kernel
#print axioms kernel_coarse_400
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_410 : checkCoarseRange 410 10 = true := by decide +kernel
#print axioms kernel_coarse_410
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_420 : checkCoarseRange 420 10 = true := by decide +kernel
#print axioms kernel_coarse_420
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_430 : checkCoarseRange 430 10 = true := by decide +kernel
#print axioms kernel_coarse_430
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_440 : checkCoarseRange 440 10 = true := by decide +kernel
#print axioms kernel_coarse_440
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_450 : checkCoarseRange 450 10 = true := by decide +kernel
#print axioms kernel_coarse_450
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_460 : checkCoarseRange 460 10 = true := by decide +kernel
#print axioms kernel_coarse_460
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_470 : checkCoarseRange 470 10 = true := by decide +kernel
#print axioms kernel_coarse_470
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_480 : checkCoarseRange 480 10 = true := by decide +kernel
#print axioms kernel_coarse_480
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_490 : checkCoarseRange 490 10 = true := by decide +kernel
#print axioms kernel_coarse_490
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_500 : checkCoarseRange 500 10 = true := by decide +kernel
#print axioms kernel_coarse_500
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_510 : checkCoarseRange 510 10 = true := by decide +kernel
#print axioms kernel_coarse_510
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_520 : checkCoarseRange 520 10 = true := by decide +kernel
#print axioms kernel_coarse_520
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_530 : checkCoarseRange 530 10 = true := by decide +kernel
#print axioms kernel_coarse_530
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_540 : checkCoarseRange 540 10 = true := by decide +kernel
#print axioms kernel_coarse_540
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_550 : checkCoarseRange 550 10 = true := by decide +kernel
#print axioms kernel_coarse_550
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_560 : checkCoarseRange 560 10 = true := by decide +kernel
#print axioms kernel_coarse_560
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_570 : checkCoarseRange 570 10 = true := by decide +kernel
#print axioms kernel_coarse_570
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_580 : checkCoarseRange 580 10 = true := by decide +kernel
#print axioms kernel_coarse_580
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_590 : checkCoarseRange 590 10 = true := by decide +kernel
#print axioms kernel_coarse_590
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_600 : checkCoarseRange 600 10 = true := by decide +kernel
#print axioms kernel_coarse_600
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_610 : checkCoarseRange 610 10 = true := by decide +kernel
#print axioms kernel_coarse_610
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_620 : checkCoarseRange 620 10 = true := by decide +kernel
#print axioms kernel_coarse_620
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_630 : checkCoarseRange 630 10 = true := by decide +kernel
#print axioms kernel_coarse_630
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_640 : checkCoarseRange 640 10 = true := by decide +kernel
#print axioms kernel_coarse_640
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_650 : checkCoarseRange 650 10 = true := by decide +kernel
#print axioms kernel_coarse_650
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_660 : checkCoarseRange 660 10 = true := by decide +kernel
#print axioms kernel_coarse_660
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_670 : checkCoarseRange 670 10 = true := by decide +kernel
#print axioms kernel_coarse_670
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_680 : checkCoarseRange 680 10 = true := by decide +kernel
#print axioms kernel_coarse_680
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_690 : checkCoarseRange 690 10 = true := by decide +kernel
#print axioms kernel_coarse_690
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_700 : checkCoarseRange 700 10 = true := by decide +kernel
#print axioms kernel_coarse_700
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_710 : checkCoarseRange 710 10 = true := by decide +kernel
#print axioms kernel_coarse_710
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_720 : checkCoarseRange 720 10 = true := by decide +kernel
#print axioms kernel_coarse_720
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_730 : checkCoarseRange 730 10 = true := by decide +kernel
#print axioms kernel_coarse_730
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_740 : checkCoarseRange 740 10 = true := by decide +kernel
#print axioms kernel_coarse_740
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_750 : checkCoarseRange 750 10 = true := by decide +kernel
#print axioms kernel_coarse_750
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_760 : checkCoarseRange 760 10 = true := by decide +kernel
#print axioms kernel_coarse_760
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_770 : checkCoarseRange 770 10 = true := by decide +kernel
#print axioms kernel_coarse_770
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_780 : checkCoarseRange 780 10 = true := by decide +kernel
#print axioms kernel_coarse_780
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_coarse_790 : checkCoarseRange 790 8 = true := by decide +kernel
#print axioms kernel_coarse_790
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_micro_798_0 : checkMicroRange 798 0 50 = true := by decide +kernel
#print axioms kernel_micro_798_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_micro_798_50 : checkMicroRange 798 50 50 = true := by decide +kernel
#print axioms kernel_micro_798_50
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_micro_799_0 : checkMicroRange 799 0 50 = true := by decide +kernel
#print axioms kernel_micro_799_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem kernel_micro_799_50 : checkMicroRange 799 50 50 = true := by decide +kernel
#print axioms kernel_micro_799_50

end HybridCertificate
-- END D01 HYBRID CHECKER

-- BEGIN D01 HYBRID SOUNDNESS
open Set MeasureTheory

namespace HybridCertificate
open RationalInterval RationalInterval.CertificateReplay
open ResourceSoundness ValidatedBlocks

set_option maxHeartbeats 2000000 in
theorem kernel_all_coarse (g : ℕ) (hg : g < 798) : checkCoarse g = true := by
  let b := g / 10
  have hb : b < 80 := by dsimp [b]; omega
  have hc : checkCoarseRange (10 * b) (if b = 79 then 8 else 10) = true := by
    interval_cases b
    · exact kernel_coarse_000
    · exact kernel_coarse_010
    · exact kernel_coarse_020
    · exact kernel_coarse_030
    · exact kernel_coarse_040
    · exact kernel_coarse_050
    · exact kernel_coarse_060
    · exact kernel_coarse_070
    · exact kernel_coarse_080
    · exact kernel_coarse_090
    · exact kernel_coarse_100
    · exact kernel_coarse_110
    · exact kernel_coarse_120
    · exact kernel_coarse_130
    · exact kernel_coarse_140
    · exact kernel_coarse_150
    · exact kernel_coarse_160
    · exact kernel_coarse_170
    · exact kernel_coarse_180
    · exact kernel_coarse_190
    · exact kernel_coarse_200
    · exact kernel_coarse_210
    · exact kernel_coarse_220
    · exact kernel_coarse_230
    · exact kernel_coarse_240
    · exact kernel_coarse_250
    · exact kernel_coarse_260
    · exact kernel_coarse_270
    · exact kernel_coarse_280
    · exact kernel_coarse_290
    · exact kernel_coarse_300
    · exact kernel_coarse_310
    · exact kernel_coarse_320
    · exact kernel_coarse_330
    · exact kernel_coarse_340
    · exact kernel_coarse_350
    · exact kernel_coarse_360
    · exact kernel_coarse_370
    · exact kernel_coarse_380
    · exact kernel_coarse_390
    · exact kernel_coarse_400
    · exact kernel_coarse_410
    · exact kernel_coarse_420
    · exact kernel_coarse_430
    · exact kernel_coarse_440
    · exact kernel_coarse_450
    · exact kernel_coarse_460
    · exact kernel_coarse_470
    · exact kernel_coarse_480
    · exact kernel_coarse_490
    · exact kernel_coarse_500
    · exact kernel_coarse_510
    · exact kernel_coarse_520
    · exact kernel_coarse_530
    · exact kernel_coarse_540
    · exact kernel_coarse_550
    · exact kernel_coarse_560
    · exact kernel_coarse_570
    · exact kernel_coarse_580
    · exact kernel_coarse_590
    · exact kernel_coarse_600
    · exact kernel_coarse_610
    · exact kernel_coarse_620
    · exact kernel_coarse_630
    · exact kernel_coarse_640
    · exact kernel_coarse_650
    · exact kernel_coarse_660
    · exact kernel_coarse_670
    · exact kernel_coarse_680
    · exact kernel_coarse_690
    · exact kernel_coarse_700
    · exact kernel_coarse_710
    · exact kernel_coarse_720
    · exact kernel_coarse_730
    · exact kernel_coarse_740
    · exact kernel_coarse_750
    · exact kernel_coarse_760
    · exact kernel_coarse_770
    · exact kernel_coarse_780
    · exact kernel_coarse_790

  have hj : g % 10 < (if b = 79 then 8 else 10) := by dsimp [b]; split_ifs <;> omega
  have hh := List.all_eq_true.mp hc (g % 10) (List.mem_range.mpr hj)
  have he : 10 * b + g % 10 = g := by dsimp [b]; omega
  simpa only [he] using hh

theorem kernel_all_micro (g m : ℕ) (hg : g = 798 ∨ g = 799) (hm : m < 100) :
    checkMicro g m = true := by
  rcases hg with rfl | rfl
  · by_cases h : m < 50
    · simpa using List.all_eq_true.mp kernel_micro_798_0 m (List.mem_range.mpr h)
    · have hm' : m - 50 < 50 := by omega
      have hh := List.all_eq_true.mp kernel_micro_798_50 (m - 50) (List.mem_range.mpr hm')
      have he : 50 + (m - 50) = m := by omega
      simpa only [he] using hh
  · by_cases h : m < 50
    · simpa using List.all_eq_true.mp kernel_micro_799_0 m (List.mem_range.mpr h)
    · have hm' : m - 50 < 50 := by omega
      have hh := List.all_eq_true.mp kernel_micro_799_50 (m - 50) (List.mem_range.mpr hm')
      have he : 50 + (m - 50) = m := by omega
      simpa only [he] using hh

theorem kernel_dense_row (g m : ℕ) (hg : g = 798 ∨ g = 799) (hm : m < 100) :
    ResourceCertificate.checkRow (100 * g + m) = true := by
  rcases hg with rfl | rfl
  · simpa using List.all_eq_true.mp ResourceCertificate.resource_probe_079_8 m (List.mem_range.mpr hm)
  · simpa using List.all_eq_true.mp ResourceCertificate.resource_probe_079_9 m (List.mem_range.mpr hm)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem critical_row_initial (g : ℕ) (hg : g = 798 ∨ g = 799) :
    ResourceCertificate.stateAt (100 * g) = IntegerReplay.state g := by
  rcases hg with rfl | rfl
  · apply integer_state_ext
    · decide +kernel
    · decide +kernel
    · rfl
  · apply integer_state_ext
    · decide +kernel
    · decide +kernel
    · rfl

theorem row_run_local (g : ℕ)
    (hc : ∀ j < 100, ResourceCertificate.checkRow (100 * g + j) = true)
    (m : ℕ) (hm : m ≤ 100) :
    IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (ResourceCertificate.stateAt (100 * g)) =
      ResourceCertificate.stateAt (100 * g + m) := by
  induction m with
  | zero => simp only [IntegerReplay.run, Nat.add_zero]
  | succ m ih =>
    have hmlt : m < 100 := by omega
    rw [IntegerChecks.run_succ_last, ih (by omega)]
    have hd : (100 * g + m) / 100 = g := by omega
    have hi : ResourceCertificate.localIndex (100 * g + m) = blockStart g + m := by
      unfold ResourceCertificate.localIndex
      rw [hd]
      have he : (100 * g + m) % 100 = m := by omega
      rw [he]
    have hs := ResourceSoundness.checked_step (100 * g + m) (hc m hmlt)
    simpa only [hd, hi, Nat.add_assoc] using hs

theorem critical_row_microstate (g m : ℕ) (hg : g = 798 ∨ g = 799) (hm : m ≤ 100) :
    ResourceCertificate.stateAt (100 * g + m) = IntegerReplay.run (IntegerReplay.segment g) m
      (blockStart g) (IntegerReplay.state g) := by
  have hr := row_run_local g (fun j hj => kernel_dense_row g j hg hj) m hm
  rw [critical_row_initial g hg] at hr
  exact hr.symm


 theorem lit_nat_time (n : ℕ) : Contains (IntegerReplay.view (IntegerReplay.lit ((n : ℚ) / 2000))) ((n : ℝ) / 2000) := by
  simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using IntegerReplay.lit_sound ((n : ℚ) / 2000)

 theorem point_scaled (n : Int) : Contains (IntegerReplay.view ⟨n, n⟩) (scaledInt n) := by
  simp only [Contains, view_lo_scaled, view_hi_scaled, le_refl, and_self]

set_option maxHeartbeats 2000000 in
 theorem build_sound (s : IntegerReplay.Segment) (j n : ℕ) (A B : IntegerReplay.Interval)
    (x₀ v t₀ : ℝ) (Y : ℝ → ℝ)
    (hx : Contains (IntegerReplay.view s.x₀) x₀)
    (hv : Contains (IntegerReplay.view s.velocity) v)
    (hYL : LipschitzOnWith ⟨17/10, by norm_num⟩ Y
      (Icc (t₀ + j/2000) (t₀ + ((j+n:ℕ):ℝ)/2000)))
    (ha : Contains (IntegerReplay.view A) (Y (t₀ + j/2000)))
    (hb : Contains (IntegerReplay.view B) (Y (t₀ + ((j+n:ℕ):ℝ)/2000)))
    (hode : ∀ᵐ t ∂volume, t ∈ Ioo (t₀+j/2000) (t₀+((j+n:ℕ):ℝ)/2000) →
      HasDerivAt Y (compensatorField (affineForcing x₀ v t₀ t) (Y t)) t)
    (hpos : 0 < (build s j n A B).coarse.lo)
    (horder : (build s j n A B).coarse.lo ≤ (build s j n A B).coarse.hi) :
    ∀ t ∈ Icc (t₀+j/2000) (t₀+((j+n:ℕ):ℝ)/2000),
      Contains (IntegerReplay.view (build s j n A B).target) (x₀+v*(t-t₀)) ∧
      Contains (IntegerReplay.view (build s j n A B).dollars) (affineForcing x₀ v t₀ t) ∧
      Contains (IntegerReplay.view (build s j n A B).refined) (Y t) := by
  let a := t₀ + (j:ℝ)/2000
  let b := t₀ + ((j+n:ℕ):ℝ)/2000
  let dt := IntegerReplay.lit ((n:ℚ)/2000)
  let motion := (IntegerReplay.multiply (IntegerReplay.lit (17/10)) dt).hi
  let c := build s j n A B
  have hab : a ≤ b := by dsimp [a,b]; push_cast; nlinarith [(show (0:ℝ) ≤ n from Nat.cast_nonneg n)]
  have hdt : b-a = (n:ℝ)/2000 := by dsimp [a,b]; push_cast; ring
  have hm : (17/10:ℝ)*(b-a) ≤ scaledInt motion := by
    have hh := IntegerReplay.multiply_sound (IntegerReplay.lit_sound (17/10)) (lit_nat_time n)
    have he := hh.2
    simpa only [view_hi_scaled, Rat.cast_div, Rat.cast_ofNat, ← hdt] using he
  have hc : ∀ t ∈ Icc a b, Contains (IntegerReplay.view c.coarse) (Y t) :=
    roundedEndpointBox_sound Y a b A B ⟨17/10, by norm_num⟩ motion hab hYL ha hb hm
  have hxa := IntegerReplay.plus_sound hx (IntegerReplay.multiply_sound hv (lit_nat_time j))
  have hxb := IntegerReplay.plus_sound hx (IntegerReplay.multiply_sound hv (lit_nat_time (j+n)))
  have hX : ∀ t ∈ Icc a b, Contains (IntegerReplay.view c.target) (x₀+v*(t-t₀)) := by
    intro t ht
    apply affine_integer_hull_contains _ _ x₀ v t₀ a b t _ _ ht
    · simpa only [a, add_sub_cancel_left] using hxa
    · simpa only [b, add_sub_cancel_left] using hxb
  have hU : ∀ t ∈ Icc a b, Contains (IntegerReplay.view c.dollars) (affineForcing x₀ v t₀ t) := by
    intro t ht
    have hh := IntegerReplay.multiply_sound (hX t ht) (IntegerReplay.plus_sound hv
      (IntegerReplay.multiply_sound (IntegerReplay.lit_sound (2/5))
        (IntegerReplay.minus_sound (hX t ht) (IntegerReplay.lit_sound 1))))
    simpa only [affineForcing, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hh
  let M := intervalMagnitude c.field
  have hF : ∀ t ∈ Icc a b, |compensatorField (affineForcing x₀ v t₀ t) (Y t)| ≤ M := by
    intro t ht
    exact interval_abs_bound (compensatorInterval_sound hpos
      ((le_of_lt hpos).trans horder) (hU t ht) (hc t ht))
  have hL := certificateBootstrap_lipschitz_of_ae_derivative hYL hode
    (Filter.Eventually.of_forall hF)
  let motion' := (IntegerReplay.multiply ⟨c.magnitude,c.magnitude⟩ dt).hi
  have hm' : (M:ℝ)*(b-a) ≤ scaledInt motion' := by
    have hh := (IntegerReplay.multiply_sound (point_scaled c.magnitude) (lit_nat_time n)).2
    simpa only [view_hi_scaled, ← hdt] using hh
  have hr := roundedEndpointBox_sound Y a b A B M motion' hab hL ha hb hm'
  intro t ht
  exact ⟨hX t ht, hU t ht, interval_intersection_sound (hc t ht) (hr t ht)⟩


theorem checked_coarse_positive (g : ℕ) (c : Bounds) (hc : checkBounds g c = true) :
    0 < c.coarse.lo ∧ c.coarse.lo ≤ c.coarse.hi := by
  simp [checkBounds, Id.run, Bool.and_eq_true] at hc
  tauto

theorem checked_economic_bounds (g : ℕ) (c : Bounds) (hc : checkBounds g c = true)
    (X U Y : ℝ) (hx : Contains (IntegerReplay.view c.target) X)
    (hu : Contains (IntegerReplay.view c.dollars) U)
    (hy : Contains (IntegerReplay.view c.refined) Y) :
    0 < X ∧ 0 < Y ∧ 9*|U| < (284481/1000000:ℝ)*Y ∧
      |U| < (284481/1000000:ℝ)*X ∧
    (if g < 400 then 3/4 < Y ∧ Y < 5/4
     else (3/4:ℝ)*scaledInt (IntegerReplay.state 400).enclosure.hi < Y ∧
       Y < (5/4:ℝ)*scaledInt (IntegerReplay.state 400).enclosure.lo) := by
  have hc' := hc
  simp [checkBounds, Id.run, Bool.and_eq_true] at hc'
  have hxp : 0 < c.target.lo := by tauto
  have hyp : 0 < c.refined.lo := by tauto
  have hr : 9*(max |c.dollars.lo| |c.dollars.hi|)*1000000 < 284481*c.refined.lo := by tauto
  have hrx : (max |c.dollars.lo| |c.dollars.hi|)*1000000 < 284481*c.target.lo := by tauto
  have hab := interval_abs_bound hu
  simp only [Contains, view_lo_scaled, view_hi_scaled] at hx hy
  have hpX : 0 < scaledInt c.target.lo := by unfold scaledInt; positivity
  have hpY : 0 < scaledInt c.refined.lo := by unfold scaledInt; positivity
  have hr' : 9*scaledInt (max |c.dollars.lo| |c.dollars.hi|)*1000000 < 284481*scaledInt c.refined.lo := by
    have he : (9:ℝ)*(max |c.dollars.lo| |c.dollars.hi|:Int)*1000000 < 284481*(c.refined.lo:ℝ) := by exact_mod_cast hr
    dsimp [scaledInt]
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<10^32)).mpr at he
    convert he using 1 <;> ring
  have hrx' : scaledInt (max |c.dollars.lo| |c.dollars.hi|)*1000000 < 284481*scaledInt c.target.lo := by
    have he : (max |c.dollars.lo| |c.dollars.hi|:Int)*(1000000:ℝ) < 284481*(c.target.lo:ℝ) := by exact_mod_cast hrx
    dsimp [scaledInt]
    apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<10^32)).mpr at he
    convert he using 1 <;> ring
  refine ⟨hpX.trans_le hx.1, hpY.trans_le hy.1, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · split_ifs with hg
    · have hb : 3*IntegerReplay.Q/4 < c.refined.lo ∧ c.refined.hi < 5*IntegerReplay.Q/4 := by
        simpa only [if_pos hg, Bool.and_eq_true, decide_eq_true_eq] using hc'.2
      have hl : (3/4:ℝ) < scaledInt c.refined.lo := by
        have he : (3*IntegerReplay.Q/4: Int) = 3*10^32/4 := by rfl
        have hq : (3*IntegerReplay.Q/4:ℝ) < (c.refined.lo:ℝ) := by
          norm_num [IntegerReplay.Q] at hb ⊢
          exact_mod_cast hb.1
        unfold scaledInt
        rw [lt_div_iff₀ (by positivity)]
        norm_num [IntegerReplay.Q] at hq ⊢
        exact hq
      have hh : scaledInt c.refined.hi < (5/4:ℝ) := by
        unfold scaledInt
        rw [div_lt_iff₀ (by positivity)]
        have he : (c.refined.hi:ℝ) < (125000000000000000000000000000000:ℝ) := by
          norm_num [IntegerReplay.Q] at hb
          exact_mod_cast hb.2
        norm_num
        exact he
      exact ⟨hl.trans_le hy.1, hy.2.trans_lt hh⟩
    · have hb : 3*(IntegerReplay.state 400).enclosure.hi < 4*c.refined.lo ∧
          4*c.refined.hi < 5*(IntegerReplay.state 400).enclosure.lo := by
        simpa only [if_neg hg, Bool.and_eq_true, decide_eq_true_eq] using hc'.2
      have hl : 3*scaledInt (IntegerReplay.state 400).enclosure.hi < 4*scaledInt c.refined.lo := by
        have he : (3:ℝ)*(IntegerReplay.state 400).enclosure.hi < 4*(c.refined.lo:ℝ) := by exact_mod_cast hb.1
        dsimp [scaledInt]
        apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<10^32)).mpr at he
        convert he using 1 <;> ring
      have hh : 4*scaledInt c.refined.hi < 5*scaledInt (IntegerReplay.state 400).enclosure.lo := by
        have he : (4:ℝ)*c.refined.hi < 5*((IntegerReplay.state 400).enclosure.lo:ℝ) := by exact_mod_cast hb.2
        dsimp [scaledInt]
        apply (div_lt_div_iff_of_pos_right (by positivity : (0:ℝ)<10^32)).mpr at he
        convert he using 1 <;> ring
      constructor <;> linarith [hy.1,hy.2]


set_option maxHeartbeats 2000000 in
theorem actual_local_bounds (h : ℝ) (hh : Contains plateau h) (Y : ℝ → ℝ)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (g m n : ℕ) (hg : g < 800) (hmn : m+n ≤ 100) (A B : IntegerReplay.Interval)
    (ha : Contains (IntegerReplay.view A) (Y ((g:ℝ)/20+m/2000)))
    (hb : Contains (IntegerReplay.view B) (Y ((g:ℝ)/20+((m+n:ℕ):ℝ)/2000)))
    (hc : checkBounds g (build (IntegerReplay.segment g) (blockStart g+m) n A B) = true) :
    ∀ t ∈ Ioc ((g:ℝ)/20+m/2000) ((g:ℝ)/20+((m+n:ℕ):ℝ)/2000),
      Contains (IntegerReplay.view (build (IntegerReplay.segment g) (blockStart g+m) n A B).target) (targetSchedule h t) ∧
      Contains (IntegerReplay.view (build (IntegerReplay.segment g) (blockStart g+m) n A B).dollars) (actualTargetDollars h t) ∧
      Contains (IntegerReplay.view (build (IntegerReplay.segment g) (blockStart g+m) n A B).refined) (Y t) := by
  let a := (g:ℝ)/20+(m:ℝ)/2000
  let b := (g:ℝ)/20+((m+n:ℕ):ℝ)/2000
  have hs := WitnessMesh.parameter_boxes_contain h hh g
  have hp := ForcingBoxes.integerPreparation_parameters _ _ _ _ _
    (WitnessMesh.static_piece_checks g).2.1 hs.1 hs.2
  rw [WitnessMesh.integer_segment_eq] at hp
  have ca : WitnessMesh.startTime g + ((blockStart g+m:ℕ):ℝ)/2000 = a := by
    rw [WitnessMesh.block_clock]; dsimp [a]; push_cast; ring
  have cb : WitnessMesh.startTime g + ((blockStart g+m+n:ℕ):ℝ)/2000 = b := by
    rw [Nat.add_assoc, WitnessMesh.block_clock]; dsimp [b]; push_cast; ring
  have hab : Icc a b ⊆ Icc (0:ℝ) 40 := by
    intro t ht
    have hg' : (g:ℝ) ≤ 799 := by exact_mod_cast (show g ≤ 799 by omega)
    have hmn' : ((m+n:ℕ):ℝ) ≤ 100 := by exact_mod_cast hmn
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hg0 : (0:ℝ) ≤ g := Nat.cast_nonneg g
    dsimp [a,b] at ht
    constructor <;> nlinarith [ht.1,ht.2]
  have hblock : ∀ t ∈ Ioc a b, t ∈ Ioc ((g:ℝ)/20) (((g+1:ℕ):ℝ)/20) := by
    intro t ht
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hmn' : ((m+n:ℕ):ℝ) ≤ 100 := by exact_mod_cast hmn
    dsimp [a,b] at ht
    simp only [Nat.cast_add,Nat.cast_one]
    constructor <;> linarith [ht.1,ht.2]
  have hd : ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt Y
      (compensatorField (affineForcing (WitnessMesh.actualStart h g)
        ((WitnessMesh.actualEnd h g-WitnessMesh.actualStart h g)/WitnessMesh.duration g)
        (WitnessMesh.startTime g) t) (Y t)) t := by
    filter_upwards [hYd] with t ht hmem
    have hglob := hab ⟨hmem.1.le,hmem.2.le⟩
    have hh := ht ⟨lt_of_le_of_lt (hab ⟨le_rfl,(le_of_lt hmem.1).trans hmem.2.le⟩).1 hmem.1,
      lt_of_lt_of_le hmem.2 (hab ⟨(le_of_lt hmem.1).trans hmem.2.le,le_rfl⟩).2⟩
    rw [block_forcing_eq_actual h g t (hblock t ⟨hmem.1,hmem.2.le⟩)]
    exact hh
  have hpcheck := checked_coarse_positive g _ hc
  have hbld := build_sound (IntegerReplay.segment g) (blockStart g+m) n A B
    (WitnessMesh.actualStart h g)
    ((WitnessMesh.actualEnd h g-WitnessMesh.actualStart h g)/WitnessMesh.duration g)
    (WitnessMesh.startTime g) Y hp.1 hp.2
  rw [ca,cb] at hbld
  have hout := hbld (hYL.mono hab) ha hb hd hpcheck.1 hpcheck.2
  intro t ht
  have hr := hout t ⟨ht.1.le,ht.2⟩
  rw [block_price_eq_actual h g t (hblock t ht),block_forcing_eq_actual h g t (hblock t ht)] at hr
  exact hr


theorem finite_grid_cover (a d : ℝ) (hd : 0 < d) (N : ℕ) :
    ∀ t ∈ Ioc a (a+N*d), ∃ k < N, t ∈ Ioc (a+k*d) (a+(k+1)*d) := by
  induction N with
  | zero => intro t ht; simp only [Nat.cast_zero,zero_mul,add_zero] at ht; linarith [ht.1,ht.2]
  | succ N ih =>
    intro t ht
    by_cases hh : t ≤ a+N*d
    · obtain ⟨k,hk,hm⟩ := ih t ⟨ht.1,hh⟩
      exact ⟨k,by omega,hm⟩
    · refine ⟨N,by omega,lt_of_not_ge hh,?_⟩
      simpa only [Nat.cast_add,Nat.cast_one] using ht.2

set_option maxHeartbeats 2000000 in
theorem actual_coarse_bounds (h : ℝ) (hh : Contains plateau h) (Y : ℝ → ℝ)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (hYb : ∀ g ≤ 800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) (Y ((g:ℝ)/20)))
    (g : ℕ) (hg : g < 798) :
    ∀ t ∈ Ioc ((g:ℝ)/20) (((g+1:ℕ):ℝ)/20),
      Contains (IntegerReplay.view (coarseBounds g).target) (targetSchedule h t) ∧
      Contains (IntegerReplay.view (coarseBounds g).dollars) (actualTargetDollars h t) ∧
      Contains (IntegerReplay.view (coarseBounds g).refined) (Y t) := by
  have ha := hYb g (by omega)
  have hb := hYb (g+1) (by omega)
  have htime : (g:ℝ)/20+((0+100:ℕ):ℝ)/2000 = ((g+1:ℕ):ℝ)/20 := by push_cast; ring
  have hr := actual_local_bounds h hh Y hYL hYd g 0 100 (by omega) (by omega)
    (IntegerReplay.state g).enclosure (IntegerReplay.state (g+1)).enclosure
    (by simpa using ha) (by simpa only [htime] using hb) (kernel_all_coarse g hg)
  simpa only [Nat.add_zero,Nat.cast_zero,zero_div,add_zero,htime] using hr

set_option maxHeartbeats 2000000 in
theorem actual_micro_bounds (h : ℝ) (hh : Contains plateau h) (Y : ℝ → ℝ)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (hYm : ∀ g < 800, ∀ m ≤ 100, Contains (IntegerReplay.view
      (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (IntegerReplay.state g)).enclosure)
      (Y ((g:ℝ)/20+m/2000)))
    (g m : ℕ) (hg : g=798 ∨ g=799) (hm : m < 100) :
    ∀ t ∈ Ioc ((g:ℝ)/20+m/2000) ((g:ℝ)/20+((m+1:ℕ):ℝ)/2000),
      Contains (IntegerReplay.view (microBounds g m).target) (targetSchedule h t) ∧
      Contains (IntegerReplay.view (microBounds g m).dollars) (actualTargetDollars h t) ∧
      Contains (IntegerReplay.view (microBounds g m).refined) (Y t) := by
  have hglt : g<800 := by omega
  have ha := hYm g hglt m (by omega)
  have hb := hYm g hglt (m+1) (by omega)
  rw [← critical_row_microstate g m hg (by omega)] at ha
  rw [← critical_row_microstate g (m+1) hg (by omega)] at hb
  have hb' : Contains (IntegerReplay.view (ResourceCertificate.stateAt (100*g+m+1)).enclosure)
      (Y ((g:ℝ)/20+((m+1:ℕ):ℝ)/2000)) := by simpa only [Nat.add_assoc] using hb
  exact actual_local_bounds h hh Y hYL hYd g m 1 hglt (by omega) _ _ ha hb' (kernel_all_micro g m hg hm)

set_option maxHeartbeats 2000000 in
theorem actual_global_boxes (h : ℝ) (hh : Contains plateau h) (Y : ℝ → ℝ)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (hYb : ∀ g ≤ 800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) (Y ((g:ℝ)/20)))
    (hYm : ∀ g < 800, ∀ m ≤ 100, Contains (IntegerReplay.view
      (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (IntegerReplay.state g)).enclosure)
      (Y ((g:ℝ)/20+m/2000))) :
    ∀ t ∈ Ioc (0:ℝ) 40, ∃ g : ℕ, ∃ c : Bounds,
      g<800 ∧ t ∈ Ioc ((g:ℝ)/20) (((g+1:ℕ):ℝ)/20) ∧ checkBounds g c=true ∧
      Contains (IntegerReplay.view c.target) (targetSchedule h t) ∧
      Contains (IntegerReplay.view c.dollars) (actualTargetDollars h t) ∧
      Contains (IntegerReplay.view c.refined) (Y t) := by
  intro t ht
  have hgrid : t ∈ Ioc (0:ℝ) (0+800*(1/20:ℝ)) := by norm_num; exact ht
  obtain ⟨g,hg,hgt⟩ := finite_grid_cover 0 (1/20) (by norm_num) 800 t hgrid
  have hgt' : t ∈ Ioc ((g:ℝ)/20) (((g+1:ℕ):ℝ)/20) := by
    simpa only [zero_add,div_eq_mul_inv,Nat.cast_add,Nat.cast_one,one_mul] using hgt
  by_cases hcoarse : g<798
  · exact ⟨g,coarseBounds g,hg,hgt',kernel_all_coarse g hcoarse,
      actual_coarse_bounds h hh Y hYL hYd hYb g hcoarse t hgt'⟩
  · have hcritical : g=798 ∨ g=799 := by omega
    have hsub : t ∈ Ioc ((g:ℝ)/20) ((g:ℝ)/20+100*(1/2000:ℝ)) := by
      constructor
      · exact hgt'.1
      · have he : ((g:ℝ)/20+100*(1/2000:ℝ))=(((g+1:ℕ):ℝ)/20) := by push_cast; ring
        rw [he]; exact hgt'.2
    obtain ⟨m,hm,hmt⟩ := finite_grid_cover ((g:ℝ)/20) (1/2000) (by norm_num) 100 t hsub
    have hmt' : t ∈ Ioc ((g:ℝ)/20+m/2000) ((g:ℝ)/20+((m+1:ℕ):ℝ)/2000) := by
      simpa only [div_eq_mul_inv,Nat.cast_add,Nat.cast_one,one_mul] using hmt
    exact ⟨g,microBounds g m,hg,hgt',kernel_all_micro g m hcritical hm,
      actual_micro_bounds h hh Y hYL hYd hYm g m hcritical hm t hmt'⟩


set_option maxHeartbeats 2000000 in
theorem actual_global_economic_bounds (h : ℝ) (hh : Contains plateau h) (Y : ℝ → ℝ)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (hYb : ∀ g ≤ 800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) (Y ((g:ℝ)/20)))
    (hYm : ∀ g < 800, ∀ m ≤ 100, Contains (IntegerReplay.view
      (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (IntegerReplay.state g)).enclosure)
      (Y ((g:ℝ)/20+m/2000))) :
    ∀ t ∈ Ioc (0:ℝ) 40, 0 < targetSchedule h t ∧ 0 < Y t ∧
      9*|actualTargetDollars h t| < (284481/1000000:ℝ)*Y t ∧
      |actualTargetDollars h t| < (284481/1000000:ℝ)*targetSchedule h t ∧
      (if t ≤ 20 then 3/4 < Y t ∧ Y t < 5/4
       else (3/4:ℝ)*Y 20 < Y t ∧ Y t < (5/4:ℝ)*Y 20) := by
  intro t ht
  obtain ⟨g,c,hg,hgt,hc,hx,hu,hy⟩ := actual_global_boxes h hh Y hYL hYd hYb hYm t ht
  have he := checked_economic_bounds g c hc _ _ _ hx hu hy
  refine ⟨he.1,he.2.1,he.2.2.1,he.2.2.2.1,?_⟩
  have href := hYb 400 (by omega)
  norm_num only [Nat.cast_ofNat] at href
  simp only [Contains,view_lo_scaled,view_hi_scaled] at href
  have hiff : g<400 ↔ t≤20 := by
    constructor
    · intro hgg
      have hhg : (g:ℝ)+1 ≤ 400 := by exact_mod_cast (show g+1≤400 by omega)
      simp only [Nat.cast_add,Nat.cast_one] at hgt
      linarith [hgt.2]
    · intro htt
      by_contra hgg
      have hhg : (400:ℝ)≤g := by exact_mod_cast (show 400≤g by omega)
      linarith [hgt.1]
  split_ifs with htt
  · simpa only [if_pos (hiff.mpr htt)] using he.2.2.2.2
  · have hgg := mt hiff.mp htt
    have hb := he.2.2.2.2
    rw [if_neg hgg] at hb
    constructor <;> linarith [hb.1,hb.2,href.1,href.2]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem checkpoint_twenty_above_one :
    IntegerReplay.Q ≤ (IntegerReplay.state 400).enclosure.lo := by decide +kernel

theorem actual_global_floor (h : ℝ) (hh : Contains plateau h) (Y : ℝ → ℝ)
    (hYa : Y 0=1)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (hYb : ∀ g ≤ 800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) (Y ((g:ℝ)/20)))
    (hYm : ∀ g < 800, ∀ m ≤ 100, Contains (IntegerReplay.view
      (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (IntegerReplay.state g)).enclosure)
      (Y ((g:ℝ)/20+m/2000))) : ∀ t ∈ Icc (0:ℝ) 40, 3/4 ≤ Y t := by
  have h20 := hYb 400 (by omega)
  norm_num only [Nat.cast_ofNat] at h20
  simp only [Contains,view_lo_scaled,view_hi_scaled] at h20
  have hq := scaledInt_mono checkpoint_twenty_above_one
  have hq' : (1:ℝ)≤scaledInt (IntegerReplay.state 400).enclosure.lo := by
    norm_num [scaledInt,IntegerReplay.Q] at hq ⊢
    exact hq
  intro t ht
  by_cases hz : t=0
  · subst t; rw [hYa]; norm_num
  · have ht' : t∈Ioc (0:ℝ) 40 := ⟨lt_of_le_of_ne ht.1 (Ne.symm hz),ht.2⟩
    have he := (actual_global_economic_bounds h hh Y hYL hYd hYb hYm t ht').2.2.2.2
    split_ifs at he with hday <;> linarith [he.1,h20.1]


theorem actual_rate_bounded (h : ℝ) (hh : h ∈ Icc (1:ℝ) plateauUpper)
    (hp : Contains plateau h) (Y : ℝ → ℝ)
    (hYL : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40))
    (hYs : ∀ t ∈ Icc (0:ℝ) 40, Y t ∈ Icc (7/10:ℝ) (8/5))
    (hYd : ∀ᵐ t ∂volume, t ∈ Ioo 0 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t)
    (hYb : ∀ g ≤ 800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) (Y ((g:ℝ)/20)))
    (hYm : ∀ g < 800, ∀ m ≤ 100, Contains (IntegerReplay.view
      (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (IntegerReplay.state g)).enclosure)
      (Y ((g:ℝ)/20+m/2000))) :
    (certificateACSession h hh Y hYL hYs hYd).RateBounded (284481/1000000) := by
  refine ⟨by norm_num,?_⟩
  have hn : ∀ᵐ t:ℝ ∂volume, t≠0 := by rw [ae_iff]; simp
  filter_upwards [hn] with t ht htmem i
  have ht' : t∈Ioc (0:ℝ) 40 := ⟨lt_of_le_of_ne htmem.1 (Ne.symm ht),htmem.2⟩
  have he := actual_global_economic_bounds h hp Y hYL hYd hYb hYm t ht'
  change certificateGrossDollars (targetBuyingDollars (actualTargetDollars h t))
    (targetSellingDollars (actualTargetDollars h t)) i / certificatePrices h Y t i ≤ _
  rw [certificate_actual_gross_rate]
  split_ifs
  · exact ((div_lt_iff₀ he.1).mpr he.2.2.2.1).le
  · exact ((div_lt_iff₀ he.2.1).mpr he.2.2.1).le

end HybridCertificate
-- END D01 HYBRID SOUNDNESS



theorem target_rolling_bands (h : ℝ) (hh : h∈Icc (1:ℝ) plateauUpper) :
    (∀ t∈Icc (0:ℝ) 20, (97/100:ℝ)≤targetSchedule h t ∧ targetSchedule h t≤103/100) ∧
    (∀ t∈Icc (20:ℝ) 40, (97/100:ℝ)*(97/100)≤targetSchedule h t ∧ targetSchedule h t≤(103/100)*(97/100)) := by
  have hhi : h≤103/100 := by have := hh.2; norm_num [plateauUpper] at this; linarith
  constructor
  · intro t ht
    unfold targetSchedule
    split_ifs <;> norm_num [targetLine] <;> constructor <;> nlinarith [ht.1,ht.2,hh.1]
  · intro t ht
    unfold targetSchedule
    split_ifs <;> norm_num [targetLine] <;> constructor <;> nlinarith [ht.1,ht.2,hh.1]

-- BEGIN D01 ACTUAL PHYSICAL ASSEMBLY
open RationalInterval RationalInterval.CertificateReplay

structure CertificateActualData where
  h : ℝ
  root : plateauPolynomial h=0
  parameter : h∈Icc (1:ℝ) plateauUpper
  plateau : Contains RationalInterval.CertificateReplay.plateau h
  Y : ℝ → ℝ
  initial : Y 0=1
  lipschitz : LipschitzOnWith (17/10:NNReal) Y (Icc 0 40)
  strip : ∀ t ∈ Icc (0:ℝ) 40, Y t∈Icc (7/10:ℝ) (8/5)
  ode : ∀ᵐ t ∂volume, t∈Ioo (0:ℝ) 40 → HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t
  checkpoint : ∀ g≤800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) (Y ((g:ℝ)/20))
  mesh : ∀ g<800, ∀ m≤100, Contains (IntegerReplay.view
    (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (IntegerReplay.state g)).enclosure)
    (Y ((g:ℝ)/20+m/2000))

theorem certificateActualData_exists : Nonempty CertificateActualData := by
  obtain ⟨h,hh,_⟩ := plateau_exists_unique
  have hp : Contains plateau h := by
    norm_num [Contains,plateau] at ⊢
    exact ⟨by convert hh.1.le using 1 <;> norm_num [plateauLower],
      by convert hh.2.1.le using 1 <;> norm_num [plateauUpper]⟩
  have hh' : h∈Icc (1:ℝ) plateauUpper := by
    refine ⟨?_,hh.2.1.le⟩
    have hl := hh.1
    norm_num [plateauLower] at hl
    linarith
  obtain ⟨Y,ha,hL,hs,hd,hb,hm⟩ := ValidatedBlocks.actual_compensator_exists_with_mesh h hp 800 (by omega)
  norm_num only [Nat.cast_ofNat] at hL hs hd
  exact ⟨⟨h,hh.2.2,hh',hp,Y,ha,hL,hs,hd,hb,hm⟩⟩

def CertificateActualData.session (d : CertificateActualData) : ACPhysicalSession certificateEdges :=
  certificateACSession d.h d.parameter d.Y d.lipschitz d.strip d.ode

theorem CertificateActualData.rate_bound (d : CertificateActualData) :
    d.session.RateBounded (284481/1000000) :=
  HybridCertificate.actual_rate_bounded d.h d.parameter d.plateau d.Y d.lipschitz d.strip d.ode d.checkpoint d.mesh

theorem CertificateActualData.floor (d : CertificateActualData) :
    ∀ t∈Icc (0:ℝ) 40, 3/4≤d.Y t :=
  HybridCertificate.actual_global_floor d.h d.plateau d.Y d.initial d.lipschitz d.ode d.checkpoint d.mesh

def CertificateActualData.piece (d : CertificateActualData) : PhysicalContinuousBVPiece certificateEdges :=
  acSessionOriginalPiece d.session rfl (fun e=>(certificateExecution d.h).cumulative e)
    (fun _=>1/20) (fun e=>certificate_execution_lipschitz d.h d.parameter e)
    (fun e=>by
      filter_upwards [certificate_execution_density d.h] with t ht hmem
      exact ht hmem e)
    (fun _=>2) (fun _=>0) (by
      have hs := certificateInventory_no_short d.h d.parameter d.root d.Y d.lipschitz.continuousOn d.floor
        (fun t ht=>targetSchedule_global_bounds d.h t d.parameter ht)
        (fun t _=>targetVelocity_abs_bound d.h t d.parameter)
      intro t ht i
      exact (hs t ht i).le)

theorem CertificateActualData.shares_lipschitz (d : CertificateActualData) (i : Fin 10) :
    LipschitzOnWith ⟨284481/1000000,by norm_num⟩ (fun t=>d.piece.shares t i) (Icc (0:ℝ) 40) := by
  apply lipschitzOn_of_bounded_primitive _ _ 0 40 ⟨284481/1000000,by norm_num⟩
    (fun s hs t ht=>rateShares_difference certificateEdges d.session.prices d.session.rates (fun _=>2)
      40 (by norm_num) (fun i=>d.session.signed_share_integrable i) i s t hs ht)
  filter_upwards [d.session.signed_share_bound _ d.rate_bound] with t ht htmem
  exact ht htmem i

theorem CertificateActualData.shares_bv (d : CertificateActualData) (i : Fin 10) :
    BoundedVariationOn (fun t=>d.piece.shares t i) (Icc (0:ℝ) 40) := by
  have hb := (d.shares_lipschitz i).locallyBoundedVariationOn 0 40 (by constructor <;> norm_num) (by constructor <;> norm_num)
  simpa only [inter_self] using hb

def CertificateActualData.path (d : CertificateActualData) :
    OriginalAdmissiblePhysicalPath (fun _:Fin 10=>1) (fun _=>2/5)
      (fun _=>constantResponse 1 (by norm_num)) certificateEdges where
  benchmark_positive := fun _=>by norm_num
  resilience_nonnegative := fun _=>by norm_num
  initial := ⟨0,d.piece.prices 0,d.piece.shares 0,d.piece.dollarLedger 0⟩
  terminal := ⟨40,d.piece.prices 40,d.piece.shares 40,d.piece.dollarLedger 40⟩
  trace := .append (.refl _) (.continuous d.piece rfl rfl rfl (fun i=>d.shares_bv i))
  at_zero := rfl
  initial_prices := by
    intro i
    change certificatePrices d.h d.Y 0 i=1
    norm_num [certificatePrices,targetSchedule,targetLine,d.initial]
  initial_holdings := by
    intro i
    change 0≤rateShares certificateEdges (certificatePrices d.h d.Y) (certificateRates d.h) (fun _=>2) 0 i
    rw [rateShares_initial]; norm_num
  initial_dollars := by
    intro i
    change 0+tradingInput (pairedMatrix certificateEdges) (fun e=>
      (certificateExecution d.h).cumulative e 0-(certificateExecution d.h).cumulative e 0) i=0
    simp [tradingInput]
  terminal_dollars := by
    intro i
    change 0+certificateDollarLedger d.h 40 i=0
    simpa only [zero_add] using certificateDollarLedger_closed d.h d.root i

theorem CertificateActualData.initial_two (d : CertificateActualData) :
    ∀ i, d.path.initial.shares i=2 := by
  intro i
  change rateShares certificateEdges (certificatePrices d.h d.Y) (certificateRates d.h) (fun _=>2) 0 i=2
  rw [rateShares_initial]

theorem CertificateActualData.sales (d : CertificateActualData) :
    ∀ i, IntervalIntegrable (fun t=>certificateInventory_grossSellingRate d.h d.Y t i) volume 0 40 ∧
      (∫ t in (0:ℝ)..40, certificateInventory_grossSellingRate d.h d.Y t i)<2 :=
  certificateInventory_sales_bounds d.h d.parameter d.root d.Y d.lipschitz.continuousOn d.floor
    (fun t ht=>targetSchedule_global_bounds d.h t d.parameter ht)
    (fun t _=>targetVelocity_abs_bound d.h t d.parameter)



set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem certificate_final_checkpoint_hi : (IntegerReplay.state 800).enclosure.hi =
    140555423111958453123472102742373 := by decide +kernel

theorem CertificateActualData.final_upper (d : CertificateActualData) :
    d.Y 40 ≤ (140555423111958453123472102742373:ℝ)/100000000000000000000000000000000 := by
  have hb := d.checkpoint 800 (by omega)
  norm_num only [Nat.cast_ofNat] at hb
  simp only [Contains,ResourceSoundness.view_lo_scaled,ResourceSoundness.view_hi_scaled] at hb
  rw [certificate_final_checkpoint_hi] at hb
  norm_num [ResourceSoundness.scaledInt] at hb ⊢
  exact hb.2

theorem CertificateActualData.target_closes (d : CertificateActualData) :
    ∀ i:Fin 10, i.val<9 → d.piece.prices 20 i=97/100 ∧ d.piece.prices 40 i=9409/10000 := by
  intro i hi
  change certificatePrices d.h d.Y 20 i=97/100 ∧ certificatePrices d.h d.Y 40 i=9409/10000
  simp only [certificatePrices,if_pos hi]
  constructor <;> norm_num [targetSchedule,targetLine] <;> ring

theorem CertificateActualData.crisis (d : CertificateActualData) :
    (1/50:ℝ)<systemicCrisis (logPriceFromBenchmark 1 d.path.terminal.prices)
      (requiredAssetCount (ι:=Fin 10) (9/10)) := by
  have hpos : 0<d.Y 40 := lt_of_lt_of_le (by norm_num) (d.strip 40 (by constructor <;> norm_num)).1
  have hc := actual_crisis_of_endpoint_bound (d.Y 40) hpos d.final_upper
  have hp : d.path.terminal.prices=terminalPrices (d.Y 40) := by
    funext i
    change certificatePrices d.h d.Y 40 i=terminalPrices (d.Y 40) i
    unfold certificatePrices terminalPrices
    split_ifs
    · norm_num [targetSchedule,targetLine] <;> ring
    · rfl
  rw [hp]
  exact hc


def certificateBandWidth (i : Fin 10) : ℝ := if i.val<9 then 3/100 else 1/4

theorem CertificateActualData.rolling_bands (d : CertificateActualData) :
    (∀ t∈Icc (0:ℝ) 20, ∀ i, (1-certificateBandWidth i)≤d.piece.prices t i ∧
      d.piece.prices t i≤1+certificateBandWidth i) ∧
    (∀ t∈Icc (20:ℝ) 40, ∀ i, (1-certificateBandWidth i)*d.piece.prices 20 i≤d.piece.prices t i ∧
      d.piece.prices t i≤(1+certificateBandWidth i)*d.piece.prices 20 i) := by
  have htarget := target_rolling_bands d.h d.parameter
  have hcomp := HybridCertificate.actual_global_economic_bounds d.h d.plateau d.Y
    d.lipschitz d.ode d.checkpoint d.mesh
  constructor
  · intro t ht i
    change 1-certificateBandWidth i≤certificatePrices d.h d.Y t i ∧
      certificatePrices d.h d.Y t i≤1+certificateBandWidth i
    by_cases hi : i.val<9
    · convert htarget.1 t ht using 1 <;> norm_num [certificatePrices,certificateBandWidth,hi]
    · simp only [certificatePrices,certificateBandWidth,if_neg hi]
      by_cases hz : t=0
      · subst t; rw [d.initial]; norm_num
      · have he := (hcomp t ⟨lt_of_le_of_ne ht.1 (Ne.symm hz),by linarith [ht.2]⟩).2.2.2.2
        rw [if_pos ht.2] at he
        constructor <;> linarith [he.1,he.2]
  · intro t ht i
    change (1-certificateBandWidth i)*certificatePrices d.h d.Y 20 i≤certificatePrices d.h d.Y t i ∧
      certificatePrices d.h d.Y t i≤(1+certificateBandWidth i)*certificatePrices d.h d.Y 20 i
    by_cases hi : i.val<9
    · have hc := (d.target_closes i hi).1
      change certificatePrices d.h d.Y 20 i=97/100 at hc
      simp only [certificateBandWidth,if_pos hi,certificatePrices] at hc ⊢
      rw [hc]
      convert htarget.2 t ht using 1 <;> norm_num
    · simp only [certificatePrices,certificateBandWidth,if_neg hi]
      by_cases hz : t=20
      · subst t
        have hp := d.floor 20 (by constructor <;> norm_num)
        constructor <;> linarith
      · have htt : 20<t := lt_of_le_of_ne ht.1 (Ne.symm hz)
        have he := (hcomp t ⟨by linarith,ht.2⟩).2.2.2.2
        rw [if_neg (by linarith)] at he
        constructor <;> linarith [he.1,he.2]



theorem CertificateActualData.gross_bound_all (d : CertificateActualData) :
    ∀ t∈Icc (0:ℝ) 40, ∀ i, d.session.gross t i ≤ 284481/1000000 := by
  intro t ht i
  change certificateGrossDollars (targetBuyingDollars (actualTargetDollars d.h t))
    (targetSellingDollars (actualTargetDollars d.h t)) i / certificatePrices d.h d.Y t i ≤ _
  rw [certificate_actual_gross_rate]
  by_cases hz : t=0
  · subst t
    have hu : actualTargetDollars d.h 0=(d.h-1)/(23/10:ℝ) := by
      norm_num [actualTargetDollars,targetSchedule,targetVelocity,targetLine]
    have hp : targetSchedule d.h 0=1 := by norm_num [targetSchedule,targetLine]
    have hn : 0≤(d.h-1)/(23/10:ℝ) := div_nonneg (by linarith [d.parameter.1]) (by norm_num)
    have hb : (d.h-1)/(23/10:ℝ)≤1/100 := by
      have hh := d.parameter.2
      norm_num [plateauUpper] at hh
      linarith
    rw [hu,hp,d.initial,abs_of_nonneg hn]
    split_ifs <;> norm_num <;> linarith
  · have he := HybridCertificate.actual_global_economic_bounds d.h d.plateau d.Y
      d.lipschitz d.ode d.checkpoint d.mesh t ⟨lt_of_le_of_ne ht.1 (Ne.symm hz),ht.2⟩
    split_ifs
    · exact ((div_lt_iff₀ he.1).mpr he.2.2.2.1).le
    · exact ((div_lt_iff₀ he.2.1).mpr he.2.2.1).le



/-- The fixed instance, with arbitrary finite directed controls and arbitrary
AC prices. No target schedule, compensator family, or root parameter is imposed. -/
structure CertificateFixedConditions {κ : Type} [Fintype κ]
    {edges : κ → PairedEdge (Fin 10)} (m : ACPhysicalSession edges) : Prop where
  at_zero : m.a=0
  at_forty : m.b=40
  benchmarks : ∀ i,m.F i=1
  resilience : ∀ i,m.rho i=2/5
  response : ∀ i x,0<x → (m.response i).impact x=1
  initial : ∀ i,m.prices 0 i=1
  closed : ∀ i,(∫ t in (0:ℝ)..40,tradingInput (pairedMatrix edges) (m.rates t) i)=0
  inventory : ∃ H:Fin 10→ℝ, (∀ i,0≤H i) ∧
    ∀ t∈Icc (0:ℝ) 40,∀ i,0≤rateShares edges m.prices m.rates H t i
  closes : ∀ i:Fin 10,i.val<9 → m.prices 20 i=97/100 ∧ m.prices 40 i=9409/10000
  first_band : ∀ t∈Icc (0:ℝ) 20,∀ i,1-certificateBandWidth i≤m.prices t i ∧
    m.prices t i≤1+certificateBandWidth i
  second_band : ∀ t∈Icc (20:ℝ) 40,∀ i,(1-certificateBandWidth i)*m.prices 20 i≤m.prices t i ∧
    m.prices t i≤(1+certificateBandWidth i)*m.prices 20 i
  crisis : (1/50:ℝ)≤systemicCrisis (logPriceFromBenchmark 1 (m.prices 40))
    (requiredAssetCount (ι:=Fin 10) (9/10))

def certificateFixedFeasibleFor (κ : Type) [Fintype κ] (v : ℝ) : Prop :=
  ∃ (edges:κ→PairedEdge (Fin 10)) (m:ACPhysicalSession edges),
    m.RateBounded v ∧ CertificateFixedConditions m

def certificateFixedFeasibleCaps : Set ℝ :=
  {v | ∃ (κ : Type) (κfinite : Fintype κ), @certificateFixedFeasibleFor κ κfinite v}

theorem CertificateActualData.fixed_conditions (d : CertificateActualData) :
    CertificateFixedConditions d.session where
  at_zero := rfl
  at_forty := rfl
  benchmarks := fun _=>rfl
  resilience := fun _=>rfl
  response := fun _ _ _=>rfl
  initial := d.path.initial_prices
  closed := by
    intro i
    have hz := actual_target_dollar_ledger_closed d.h d.root
    change (∫ t in (0:ℝ)..40, tradingInput (pairedMatrix certificateEdges) (certificateRates d.h t) i)=0
    simp_rw [certificate_input_rate]
    by_cases hi:i.val<9
    · simpa only [if_pos hi] using hz
    · simp only [if_neg hi,intervalIntegral.integral_const_mul,hz,mul_zero]
  inventory := ⟨fun _=>2,fun _=>by norm_num,d.piece.no_short_sales⟩
  closes := d.target_closes
  first_band := d.rolling_bands.1
  second_band := d.rolling_bands.2
  crisis := d.crisis.le

theorem certificateFixedFeasibleCaps_nonempty : certificateFixedFeasibleCaps.Nonempty := by
  obtain ⟨d⟩ := certificateActualData_exists
  refine ⟨284481/1000000,Fin 9×Bool,inferInstance,certificateEdges,d.session,d.rate_bound,d.fixed_conditions⟩

theorem certificateFixedFeasibleCaps_necessary (v : ℝ) (hv:v∈certificateFixedFeasibleCaps) :
    (441/10000:ℝ)<v := by
  obtain ⟨κ,κfinite,edges,m,hm,hc⟩ := hv
  letI : Fintype κ := κfinite
  exact certifiedRateLower_actual_necessary m v hm hc.at_zero hc.at_forty hc.benchmarks
    hc.resilience hc.response hc.initial _ hc.crisis

theorem certificate_minimum_rate_bracket :
    (44/1000:ℝ)<sInf certificateFixedFeasibleCaps ∧ sInf certificateFixedFeasibleCaps<285/1000 := by
  have hn := certificateFixedFeasibleCaps_nonempty
  have hl := certifiedRateLower_infimum_margin certificateFixedFeasibleCaps hn certificateFixedFeasibleCaps_necessary
  refine ⟨hl.2,?_⟩
  have hb : BddBelow certificateFixedFeasibleCaps := ⟨441/10000,fun v hv=>(certificateFixedFeasibleCaps_necessary v hv).le⟩
  obtain ⟨d⟩ := certificateActualData_exists
  have hm : (284481/1000000:ℝ)∈certificateFixedFeasibleCaps :=
    ⟨Fin 9×Bool,inferInstance,certificateEdges,d.session,d.rate_bound,d.fixed_conditions⟩
  exact (csInf_le hb hm).trans_lt (by norm_num)

-- END D01 ACTUAL PHYSICAL ASSEMBLY

end MarketCrash.OriginalCertificate


namespace MarketCrash
open Set MeasureTheory
open OriginalCertificate
/-
In the ten-asset specification just stated in Section~\ref{subsec:v7-certified} ($k=9$, $F=\eta=1$, $\rho=0.4$, $\tau_1=\tau_2=20$, target bands $\pm3\%$, compensator bands $\pm25\%$), there exists a continuous, absolutely continuous, fully paired-dollar path with all per-asset terminal signed-dollar ledgers exactly zero such that the same nine assets close at $0.97$ and $0.9409$, respectively, while
\begin{equation}\label{eq:v7-certified-result}
\boxed{\Cris_{0.9}(40)>0.020,\quad \bar v_{\mathrm{used}}<0.285,\quad M<3,\quad H_i^-<2\quad(1\le i\le10).}
\end{equation}
Every executed price remains inside its rolling session band. Here $M$ counts paired executed dollars once and $H_i^-$ denotes gross shares sold, so initial holdings of two shares of every asset are sufficient without shorting.
\end{proposition}
-/
theorem proposition_7_6_original :
    ∃ d : OriginalCertificate.CertificateActualData, ∃ v : ℝ,
      v < 285/1000 ∧ d.session.RateBounded v ∧
      (∀ t∈Icc (0:ℝ) 40, ∀ i, d.session.gross t i≤v) ∧
      (∀ i, d.path.initial.shares i=2) ∧
      (∀ i, d.path.terminal.dollars i=0) ∧
      (∀ i:Fin 10, i.val<9 → d.piece.prices 20 i=97/100 ∧ d.piece.prices 40 i=9409/10000) ∧
      (1/50:ℝ)<systemicCrisis (logPriceFromBenchmark 1 d.path.terminal.prices)
        (requiredAssetCount (ι:=Fin 10) (9/10)) ∧
      (∫ t in (0:ℝ)..40,∑ e:Fin 9×Bool, d.session.rates t e)<3 ∧
      (∀ i, (∫ t in (0:ℝ)..40, certificateInventory_grossSellingRate d.h d.Y t i)<2) ∧
      (∀ t∈Icc (0:ℝ) 40, ∀ i, 0≤d.piece.shares t i) ∧
      (∀ t∈Icc (0:ℝ) 20, ∀ i, (1-certificateBandWidth i)≤d.piece.prices t i ∧
        d.piece.prices t i≤1+certificateBandWidth i) ∧
      (∀ t∈Icc (20:ℝ) 40, ∀ i, (1-certificateBandWidth i)*d.piece.prices 20 i≤d.piece.prices t i ∧
        d.piece.prices t i≤(1+certificateBandWidth i)*d.piece.prices 20 i) := by
  obtain ⟨d⟩ := certificateActualData_exists
  refine ⟨d,284481/1000000,by norm_num,d.rate_bound,d.gross_bound_all,d.initial_two,d.path.terminal_dollars,
    d.target_closes,d.crisis,?_,(fun i=>(d.sales i).2),d.piece.no_short_sales,
    d.rolling_bands.1,d.rolling_bands.2⟩
  have hM := certificateTurnover_actual_paired_integral d.h d.parameter d.root
  change (∫ t in (0:ℝ)..40,∑ e:Fin 9×Bool,
    directedAmounts (targetBuyingDollars (actualTargetDollars d.h t))
      (targetSellingDollars (actualTargetDollars d.h t)) e)<3
  linarith
end MarketCrash
