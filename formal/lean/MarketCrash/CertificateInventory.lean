import MarketCrash.OriginalCertificate
import MarketCrash.CertificateTurnover
import MarketCrash.FiniteRateConstruction

open Set MeasureTheory
open scoped Interval
namespace MarketCrash.OriginalCertificate

noncomputable def certificateInventory_rates (h : ℝ) (t : ℝ) :=
  directedAmounts (targetBuyingDollars (actualTargetDollars h t))
    (targetSellingDollars (actualTargetDollars h t))

noncomputable def certificateInventory_grossSellingRate (h : ℝ) (Y : ℝ → ℝ)
    (t : ℝ) (i : Fin 10) : ℝ :=
  (∑ e, if (certificateEdges e).seller = i then certificateInventory_rates h t e else 0) /
    certificatePrices h Y t i

theorem certificateInventory_seller_sum (buy sell : ℝ) (i : Fin 10) :
    (∑ e, if (certificateEdges e).seller = i then directedAmounts buy sell e else 0) =
      if i.val < 9 then sell else 9 * buy := by
  fin_cases i <;>
    norm_num [certificateEdges, directedAmounts, targetIndex,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  all_goals norm_num only [Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]
  all_goals simp only [if_true, if_false]
  all_goals ring

theorem certificateInventory_gross_formula (h : ℝ) (Y : ℝ → ℝ) (t : ℝ) (i : Fin 10) :
    certificateInventory_grossSellingRate h Y t i =
      if i.val < 9 then targetSellingDollars (actualTargetDollars h t) / targetSchedule h t
      else 9 * targetBuyingDollars (actualTargetDollars h t) / Y t := by
  unfold certificateInventory_grossSellingRate certificateInventory_rates
  rw [certificateInventory_seller_sum]
  by_cases hi : i.val < 9 <;> simp [certificatePrices, hi]

theorem certificateInventory_div_integrable {f P : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 40) (hP : ContinuousOn P (Icc 0 40))
    (hp : ∀ t ∈ Icc 0 40, 0 < P t) :
    IntervalIntegrable (fun t => f t / P t) volume 0 40 := by
  have hc : ContinuousOn (fun t => (P t)⁻¹) (uIcc 0 40) := by
    rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 40)]
    exact hP.inv₀ (fun t ht => (hp t ht).ne')
  simpa only [div_eq_mul_inv] using hf.mul_continuousOn hc

theorem certificateInventory_target_sale_bound (h t : ℝ)
    (hx : 47/50 ≤ targetSchedule h t ∧ targetSchedule h t ≤ 103/100)
    (hv : |targetVelocity h t| ≤ 3/125) :
    targetSellingDollars (actualTargetDollars h t) / targetSchedule h t ≤ 6/125 := by
  have hp : 0 < targetSchedule h t := by linarith [hx.1]
  apply (div_le_iff₀ hp).mpr
  unfold targetSellingDollars actualTargetDollars
  apply max_le
  · have hv' := (abs_le.mp hv).1
    nlinarith [hx.1]
  · positivity

theorem certificateInventory_sales_bounds (h : ℝ) (hh : h ∈ Icc (1:ℝ) plateauUpper)
    (hr : plateauPolynomial h = 0) (Y : ℝ → ℝ)
    (hY : ContinuousOn Y (Icc 0 40)) (hy : ∀ t ∈ Icc 0 40, 3/4 ≤ Y t)
    (hx : ∀ t ∈ Icc 0 40, 47/50 ≤ targetSchedule h t ∧ targetSchedule h t ≤ 103/100)
    (hv : ∀ t ∈ Icc 0 40, |targetVelocity h t| ≤ 3/125) :
    ∀ i, IntervalIntegrable (fun t => certificateInventory_grossSellingRate h Y t i) volume 0 40 ∧
      (∫ t in (0:ℝ)..40, certificateInventory_grossSellingRate h Y t i) < 2 := by
  have hxp : ∀ t ∈ Icc (0:ℝ) 40, 0 < targetSchedule h t := by
    intro t ht; linarith [(hx t ht).1]
  have hyp : ∀ t ∈ Icc (0:ℝ) 40, 0 < Y t := by
    intro t ht; linarith [hy t ht]
  have hs := certificateInventory_div_integrable (actual_target_gross_integrable h).2
    (targetSchedule_continuous h).continuousOn hxp
  have hb := certificateInventory_div_integrable (actual_target_gross_integrable h).1 hY hyp
  intro i
  simp_rw [certificateInventory_gross_formula]
  by_cases hi : i.val < 9
  · simp only [hi, if_true]
    refine ⟨hs, lt_of_le_of_lt ?_ (by norm_num : (48/25:ℝ) < 2)⟩
    calc
      _ ≤ ∫ _t in (0:ℝ)..40, (6/125:ℝ) :=
        intervalIntegral.integral_mono_on (by norm_num) hs intervalIntegrable_const
          (fun t ht => certificateInventory_target_sale_bound h t (hx t ht) (hv t ht))
      _ = 48/25 := by norm_num
  · simp only [hi, if_false]
    have hbi : IntervalIntegrable (fun t => 9 * targetBuyingDollars (actualTargetDollars h t) / Y t) volume 0 40 := by
      simpa only [mul_div_assoc] using hb.const_mul 9
    refine ⟨hbi, ?_⟩
    have hle : (∫ t in (0:ℝ)..40, 9 * targetBuyingDollars (actualTargetDollars h t) / Y t) ≤
        12 * targetBuyingCumulative h 40 := by
      calc
        _ ≤ ∫ t in (0:ℝ)..40, 12 * targetBuyingDollars (actualTargetDollars h t) := by
          apply intervalIntegral.integral_mono_on (by norm_num) hbi ((actual_target_gross_integrable h).1.const_mul 12)
          intro t ht
          apply (div_le_iff₀ (hyp t ht)).mpr
          have hb0 := (directed_dollar_controls (actualTargetDollars h t)).1
          nlinarith [hy t ht]
        _ = _ := by rw [intervalIntegral.integral_const_mul]; rfl
    have hc := (certificateTurnover_cumulative_bound h hh hr).2.1
    rw [← certificateTurnover_buy_eq_sell h hr] at hc
    linarith

theorem certificateInventory_negative_controls (u : ℝ) :
    targetBuyingDollars (-9*u) = 9*targetSellingDollars u ∧
    targetSellingDollars (-9*u) = 9*targetBuyingDollars u := by
  unfold targetBuyingDollars targetSellingDollars
  by_cases hu : 0 ≤ u
  · rw [max_eq_right (by linarith : -9*u ≤ 0), max_eq_right (by linarith : -u ≤ 0),
      max_eq_left (by linarith : 0 ≤ -(-9*u)), max_eq_left hu]
    constructor <;> ring
  · have hu' : u ≤ 0 := le_of_not_ge hu
    rw [max_eq_left (by linarith : 0 ≤ -9*u), max_eq_left (by linarith : 0 ≤ -u),
      max_eq_right (by linarith : -(-9*u) ≤ 0), max_eq_right hu']
    constructor <;> ring

theorem certificateInventory_no_short (h : ℝ) (hh : h ∈ Icc (1:ℝ) plateauUpper)
    (hr : plateauPolynomial h = 0) (Y : ℝ → ℝ)
    (hY : ContinuousOn Y (Icc 0 40)) (hy : ∀ t ∈ Icc 0 40, 3/4 ≤ Y t)
    (hx : ∀ t ∈ Icc 0 40, 47/50 ≤ targetSchedule h t ∧ targetSchedule h t ≤ 103/100)
    (hv : ∀ t ∈ Icc 0 40, |targetVelocity h t| ≤ 3/125) :
    ∀ t ∈ Icc (0:ℝ) 40, ∀ i, 0 <
      rateShares certificateEdges (certificatePrices h Y) (certificateInventory_rates h)
        (fun _ => 2) t i := by
  have hxp : ∀ t ∈ Icc (0:ℝ) 40, 0 < targetSchedule h t := by
    intro t ht; linarith [(hx t ht).1]
  have hyp : ∀ t ∈ Icc (0:ℝ) 40, 0 < Y t := by
    intro t ht; linarith [hy t ht]
  have hxs := certificateInventory_div_integrable (actual_target_gross_integrable h).2
    (targetSchedule_continuous h).continuousOn hxp
  have hxb := certificateInventory_div_integrable (actual_target_gross_integrable h).1
    (targetSchedule_continuous h).continuousOn hxp
  have hys := certificateInventory_div_integrable (actual_target_gross_integrable h).2 hY hyp
  have hyb := certificateInventory_div_integrable (actual_target_gross_integrable h).1 hY hyp
  have hb := certificateInventory_sales_bounds h hh hr Y hY hy hx hv
  intro t ht i
  unfold rateShares certificateInventory_rates
  simp_rw [certificate_directed_input, (directed_dollar_controls _).2.2.1]
  by_cases hi : i.val < 9
  · simp only [certificatePrices, hi, if_true]
    have hbound := (hb i).2
    simp_rw [certificateInventory_gross_formula, if_pos hi] at hbound
    exact inventory_positive_on_Icc_of_selling_bound (actualTargetDollars h)
      (targetSchedule h) 0 40 2 (by norm_num) hxp hxb hxs hbound t ht
  · simp only [certificatePrices, hi, if_false]
    have hbound := (hb i).2
    simp_rw [certificateInventory_gross_formula, if_neg hi] at hbound
    have hbuy : IntervalIntegrable (fun t => targetBuyingDollars (-9*actualTargetDollars h t) / Y t) volume 0 40 := by
      simp_rw [(certificateInventory_negative_controls _).1, mul_div_assoc]
      exact hys.const_mul 9
    have hsell : IntervalIntegrable (fun t => targetSellingDollars (-9*actualTargetDollars h t) / Y t) volume 0 40 := by
      simp_rw [(certificateInventory_negative_controls _).2, mul_div_assoc]
      exact hyb.const_mul 9
    have hbound' : (∫ u in (0:ℝ)..40, targetSellingDollars (-9*actualTargetDollars h u) / Y u) < 2 := by
      simpa only [(certificateInventory_negative_controls _).2] using hbound
    exact inventory_positive_on_Icc_of_selling_bound (fun u => -9*actualTargetDollars h u)
      Y 0 40 2 (by norm_num) hyp hbuy hsell hbound' t ht

theorem certificateInventory_initial (h : ℝ) (Y : ℝ → ℝ) :
    rateShares certificateEdges (certificatePrices h Y) (certificateInventory_rates h)
      (fun _ => 2) 0 = (fun _ => 2) := rateShares_initial _ _ _ _

end MarketCrash.OriginalCertificate
