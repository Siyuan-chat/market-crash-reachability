import MarketCrash.OriginalCertificate
noncomputable section
namespace MarketCrash.OriginalCertificate
open Set MeasureTheory

theorem certificateTurnover_buy_nonnegative_piece (h x₀ x₁ a b : ℝ)
    (heq : ∀ t ∈ Ioo a b, actualTargetDollars h t = targetLine x₀ x₁ a b t *
      ((x₁-x₀)/(b-a)+(2/5:ℝ)*(targetLine x₀ x₁ a b t-1)))
    (hpos : ∀ t ∈ Ioo a b,0 ≤ targetLine x₀ x₁ a b t ∧
      0 ≤ (x₁-x₀)/(b-a)+(2/5:ℝ)*(targetLine x₀ x₁ a b t-1)) :
    ∀ t ∈ Ioo a b,targetBuyingDollars (actualTargetDollars h t) =
      targetLine x₀ x₁ a b t *((x₁-x₀)/(b-a)+(2/5:ℝ)*(targetLine x₀ x₁ a b t-1)) := by
  intro t ht
  rw [heq t ht,targetBuyingDollars,max_eq_left (mul_nonneg (hpos t ht).1 (hpos t ht).2)]

theorem certificateTurnover_buy_zero_piece (h a b : ℝ)
    (hneg : ∀ t ∈ Ioo a b,actualTargetDollars h t ≤ 0) :
    ∀ t ∈ Ioo a b,targetBuyingDollars (actualTargetDollars h t) =
      targetLine 1 1 a b t *((1-1)/(b-a)+(2/5:ℝ)*(targetLine 1 1 a b t-1)) := by
  intro t ht
  rw [targetBuyingDollars,max_eq_right (hneg t ht)]
  simp [targetLine]

set_option maxHeartbeats 1200000 in
theorem certificateTurnover_buy_cumulative (h : ℝ) (hh : h ∈ Icc (1:ℝ) plateauUpper) :
    targetBuyingCumulative h 40 = positiveDollarMajorant h := by
  let f := fun t => targetBuyingDollars (actualTargetDollars h t)
  have hupper : h ≤ 103/100 := hh.2.trans (by norm_num [plateauUpper])
  have hp := targetSchedule_positive h ⟨hh.1,hupper⟩
  have h₁ := dollars_segment_from_open_formula f 1 h 0 (23/10) (by norm_num)
    (certificateTurnover_buy_nonnegative_piece h 1 h 0 (23/10) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | (norm_num [targetLine])) (by
      intro t ht
      have hv : 0 ≤ (h-1)/(23/10:ℝ) := div_nonneg (by linarith [hh.1]) (by norm_num)
      have hx : 1 ≤ targetLine 1 h 0 (23/10) t := by
        simp only [targetLine,sub_zero]
        exact le_add_of_nonneg_right (mul_nonneg hv ht.1.le)
      constructor
      · linarith
      · simpa only [sub_zero] using add_nonneg hv
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2/5) (sub_nonneg.mpr hx))))
  have h₂ := dollars_segment_from_open_formula f h h (23/10) (177/10) (by norm_num)
    (certificateTurnover_buy_nonnegative_piece h h h (23/10) (177/10) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | (norm_num [targetLine])) (by
      intro t ht
      simp only [targetLine,sub_self,zero_div,zero_mul,add_zero]
      constructor <;> linarith [hh.1]))
  have h₃ := dollars_segment_from_open_formula f 1 1 (177/10) 20 (by norm_num)
    (certificateTurnover_buy_zero_piece h (177/10) 20 (by
      intro t ht
      have hxt := (targetSchedule_rolling_bands h ⟨hh.1,hupper⟩).1 t ⟨by linarith [ht.1],ht.2.le⟩
      have hv : targetVelocity h t = (97/100-h)/(23/10) := by
        unfold targetVelocity
        split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | rfl
      have hfac : targetVelocity h t+(2/5:ℝ)*(targetSchedule h t-1) ≤ 0 := by
        rw [hv];nlinarith [hh.1,hxt.2]
      exact mul_nonpos_of_nonneg_of_nonpos (hp t ⟨by linarith [ht.1],by linarith [ht.2]⟩).le hfac))
  have h₄ := dollars_segment_from_open_formula f 1 1 20 (1013/50) (by norm_num)
    (certificateTurnover_buy_zero_piece h 20 (1013/50) (by
      intro t ht
      have he : targetVelocity h t+(2/5:ℝ)*(targetSchedule h t-1) = (5*t-1013/10)/1150 := by
        unfold targetVelocity targetSchedule
        split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | (norm_num [targetLine];ring)
      apply mul_nonpos_of_nonneg_of_nonpos (hp t ⟨by linarith [ht.1],by linarith [ht.2]⟩).le
      rw [he];linarith [ht.2]))
  have h₅ := dollars_segment_from_open_formula f (179/184) (199/200) (1013/50) (223/10) (by norm_num)
    (certificateTurnover_buy_nonnegative_piece h (179/184) (199/200) (1013/50) (223/10) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | (norm_num [targetLine];ring)) (by
      intro t ht
      norm_num [targetLine]
      constructor <;> linarith [ht.1]))
  have h₆ := dollars_segment_from_open_formula f 1 1 (223/10) (377/10) (by norm_num)
    (certificateTurnover_buy_zero_piece h (223/10) (377/10) (by
      intro t ht
      have he : actualTargetDollars h t = -(199:ℝ)/100000 := by
        unfold actualTargetDollars targetSchedule targetVelocity
        split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | norm_num
      rw [he];norm_num))
  have h₇ := dollars_segment_from_open_formula f 1 1 (377/10) 40 (by norm_num)
    (certificateTurnover_buy_zero_piece h (377/10) 40 (by
      intro t ht
      have hxt := (targetSchedule_rolling_bands h ⟨hh.1,hupper⟩).2 t ⟨by linarith [ht.1],ht.2.le⟩
      have hv : targetVelocity h t = (9409/10000-199/200)/(23/10) := by
        unfold targetVelocity
        split_ifs <;> first | (exfalso;linarith [ht.1,ht.2]) | rfl
      have hfac : targetVelocity h t+(2/5:ℝ)*(targetSchedule h t-1) ≤ 0 := by rw [hv];nlinarith [hxt.2]
      exact mul_nonpos_of_nonneg_of_nonpos (hp t ⟨by linarith [ht.1],ht.2.le⟩).le hfac))
  have i₂ := h₁.1.trans h₂.1
  have i₃ := i₂.trans h₃.1
  have i₄ := i₃.trans h₄.1
  have i₅ := i₄.trans h₅.1
  have i₆ := i₅.trans h₆.1
  change (∫ t in (0:ℝ)..40,f t) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals i₆ h₇.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₅ h₆.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₄ h₅.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₃ h₄.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₂ h₃.1,
    ← intervalIntegral.integral_add_adjacent_intervals h₁.1 h₂.1,
    h₁.2,h₂.2,h₃.2,h₄.2,h₅.2,h₆.2,h₇.2]
  have he (x0 x1 d : ℝ) (hd : 0 < d) : physicalSegmentDollars x0 x1 d = linearSegmentDollars x0 x1 d :=
    (linearSegmentDollars_eq_physical_integral x0 x1 d hd).symm
  have hz (d : ℝ) : physicalSegmentDollars 1 1 d = 0 := by simp [physicalSegmentDollars]
  rw [hz,hz,hz,hz]
  norm_num only [zero_add,add_zero,sub_zero]
  rw [he 1 h _ (by norm_num),he h h _ (by norm_num),he (179/184) (199/200) _ (by norm_num)]
  norm_num [positiveDollarMajorant]

theorem certificateTurnover_buy_eq_sell (h : ℝ) (hroot : plateauPolynomial h = 0) :
    targetBuyingCumulative h 40 = targetSellingCumulative h 40 := by
  have hh := target_gross_cumulative_difference h 40 (by norm_num)
  rw [actual_target_dollar_ledger_closed h hroot] at hh
  linarith

theorem certificateTurnover_cumulative_bound (h : ℝ) (hh : h ∈ Icc (1:ℝ) plateauUpper)
    (hroot : plateauPolynomial h = 0) :
    9*(targetBuyingCumulative h 40+targetSellingCumulative h 40) = 18*positiveDollarMajorant h ∧
    9*(targetBuyingCumulative h 40+targetSellingCumulative h 40) < 2984/1000 ∧
    9*(targetBuyingCumulative h 40+targetSellingCumulative h 40) < 3 := by
  have he : 9*(targetBuyingCumulative h 40+targetSellingCumulative h 40) = 18*positiveDollarMajorant h := by
    rw [←certificateTurnover_buy_eq_sell h hroot,certificateTurnover_buy_cumulative h hh]
    ring
  refine ⟨he,?_,?_⟩
  · rw [he];exact positiveDollarMajorant_turnover_margin h hh
  · have hb := positiveDollarMajorant_turnover_margin h hh
    rw [he];linarith

theorem certificateTurnover_actual_paired_integral (h : ℝ) (hh : h ∈ Icc (1:ℝ) plateauUpper)
    (hroot : plateauPolynomial h = 0) :
    (∫ t in (0:ℝ)..40,∑ e : Fin 9 × Bool,
      directedAmounts (targetBuyingDollars (actualTargetDollars h t))
        (targetSellingDollars (actualTargetDollars h t)) e) < 2984/1000 := by
  have hb := (actual_target_gross_integrable h).1
  have hs := (actual_target_gross_integrable h).2
  have he (t : ℝ) : (∑ e : Fin 9 × Bool,
      directedAmounts (targetBuyingDollars (actualTargetDollars h t))
        (targetSellingDollars (actualTargetDollars h t)) e) =
      9*(targetBuyingDollars (actualTargetDollars h t)+targetSellingDollars (actualTargetDollars h t)) := by
    rw [certificate_actual_paired_turnover_rate,(directed_dollar_controls _).2.2.2.1]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hb hs]
  exact (certificateTurnover_cumulative_bound h hh hroot).2.1

end MarketCrash.OriginalCertificate
