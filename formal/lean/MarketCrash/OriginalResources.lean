import MarketCrash.PhysicalBVResourceCoordinates
import MarketCrash.LipschitzFTC
import Mathlib.Topology.Order.IntermediateValue
import MarketCrash.OriginalPhysicalTrace

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

/-- A Lipschitz score cannot cross below zero if its actual a.e. speed
is nonnegative wherever the score is negative. The proof uses its last
zero and the kernel-checked Lipschitz FTC. -/
theorem resource_score_nonnegative_of_negative_speed
    {H w : ℝ → ℝ} {C : ℝ≥0} (hH : LipschitzWith C H) (a b : ℝ) (hab : a ≤ b)
    (hstart : 0 ≤ H a)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt H (w x) x)
    (hspeed : ∀ᵐ x ∂volume, x ∈ Ioo a b → H x < 0 → 0 ≤ w x) : 0 ≤ H b := by
  by_contra hfail
  have hneg : H b < 0 := lt_of_not_ge hfail
  have hroot : ∃ x ∈ Icc a b, H x = 0 := by
    have hh : (0 : ℝ) ∈ uIcc (H a) (H b) := mem_uIcc_of_ge hneg.le hstart
    obtain ⟨x, hx, he⟩ := intermediate_value_uIcc hH.continuous.continuousOn hh
    exact ⟨x, by simpa [uIcc_of_le hab] using hx, he⟩
  let K := Icc a b ∩ H ⁻¹' {0}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hH.continuous)
  have hne : K.Nonempty := by
    obtain ⟨x, hx, he⟩ := hroot
    exact ⟨x, hx, he⟩
  obtain ⟨r, hr, hmax⟩ := hK.exists_isGreatest hne
  have hrab : r ∈ Icc a b := hr.1
  have hrzero : H r = 0 := hr.2
  have hbelow : ∀ x ∈ Ioo r b, H x < 0 := by
    intro x hx
    by_contra hn
    have hxn : 0 ≤ H x := le_of_not_gt hn
    have hh : (0 : ℝ) ∈ uIcc (H x) (H b) := mem_uIcc_of_ge hneg.le hxn
    obtain ⟨y, hy, he⟩ := intermediate_value_uIcc hH.continuous.continuousOn hh
    have hxy : y ∈ Icc x b := by simpa [uIcc_of_le hx.2.le] using hy
    have hyr : y ≤ r := hmax ⟨⟨hrab.1.trans (hx.1.le.trans hxy.1), hxy.2⟩, he⟩
    linarith [hx.1, hxy.1]
  have hrd : ∀ᵐ x ∂volume, x ∈ Ioo r b → HasDerivAt H (w x) x := by
    filter_upwards [hd] with x hx hmem
    exact hx ⟨hrab.1.trans_lt hmem.1, hmem.2⟩
  have hftc := (lipschitzOn_integral_eq_sub_of_hasDerivAt_ae
    hH.lipschitzOnWith hrab.2 hrd).2
  have hi : 0 ≤ ∫ x in r..b, w x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hrab.2
    filter_upwards [ae_restrict_of_ae hspeed, ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (show ∀ᵐ x : ℝ ∂volume, x ≠ r by simp [ae_iff]),
      ae_restrict_of_ae (show ∀ᵐ x : ℝ ∂volume, x ≠ b by simp [ae_iff])] with x hx hmem hxr hxb
    have hxi : x ∈ Ioo r b := ⟨lt_of_le_of_ne hmem.1 hxr.symm, lt_of_le_of_ne hmem.2 hxb⟩
    exact hx ⟨hrab.1.trans_lt hxi.1, hxi.2⟩ (hbelow x hxi)
  rw [hftc, hrzero, sub_zero] at hi
  exact (not_lt_of_ge hi) hneg

theorem inventoryCostCoordinate_lower_distance (F s : ℝ) (g : Response) (hF : 0 < F) (hs : 0 < s) :
    inventoryCostCoordinate F g.impact s = ∫ u in s..F, (F - u) / g.impact u := by
  rw [inventoryCostCoordinate_integral F s g hF hs, intervalIntegral.integral_symm,
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro u _
  ring

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {F rho : ι → ℝ} {response : ι → Response} {edges : κ → PairedEdge ι}
variable {s t : PhysicalMarketState ι}

def physicalInventoryCost (F : ι → ℝ) (response : ι → Response) (s : PhysicalMarketState ι) (i : ι) : ℝ :=
  F i * s.shares i + inventoryCostCoordinate (F i) (response i).impact (s.prices i) - s.dollars i

theorem OriginalPhysicalStep.inventory_cost_nonincreasing
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) :
    physicalInventoryCost F response t i ≤ physicalInventoryCost F response s i := by
  cases step with
  | continuous m hF hr hg _ =>
    simpa only [physicalInventoryCost, hF, hg] using m.inventory_cost_nonincreasing i
  | pulse p hF hg _ =>
    have hh := p.cost_at_parameter 1 ⟨by norm_num, le_rfl⟩ i
    simpa only [physicalInventoryCost, hF, hg] using hh.le

theorem OriginalPhysicalReachable.inventory_cost_nonincreasing
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    physicalInventoryCost F response t i ≤ physicalInventoryCost F response s i := by
  induction trace with
  | refl => exact le_rfl
  | append previous step ih => exact (step.inventory_cost_nonincreasing i).trans ih

/-- The original inventory inequality for every actually qualifying
asset, including continuous singular-BV pieces and finite physical pulses. -/
theorem OriginalAdmissiblePhysicalPath.inventory_cap_for_qualifying_asset
    (p : OriginalAdmissiblePhysicalPath F rho response edges)
    (i : ι) (delta H : ℝ) (hdelta : 0 < delta)
    (hqual : delta ≤ Real.log (F i / p.terminal.prices i))
    (hinventory : p.initial.shares i ≤ H) :
    (∫ u in F i * Real.exp (-delta)..F i, (F i - u) / (response i).impact u) ≤ F i * H := by
  have hp : ∀ i, 0 < p.terminal.prices i := p.trace.endpoint_positive
    (fun i => by rw [p.initial_prices i]; exact p.benchmark_positive i)
  have hF := p.benchmark_positive i
  let target := F i * Real.exp (-delta)
  have htarget : 0 < target := mul_pos hF (Real.exp_pos _)
  have htargetF : target < F i := by
    have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hdelta)
    exact (mul_lt_mul_of_pos_left hh hF).trans_eq (mul_one _)
  have hlog : delta ≤ -Real.log (p.terminal.prices i / F i) := by
    rw [Real.log_div hF.ne' (hp i).ne'] at hqual
    rw [Real.log_div (hp i).ne' hF.ne']
    linarith
  have hterminal : p.terminal.prices i ≤ target :=
    rateBand_price_of_log_loss (F i) _ delta hF (hp i) hlog
  have hmon := inventoryCostCoordinate_antitone_below (F i) (response i) hF
    ⟨hp i, hterminal.trans htargetF.le⟩ ⟨htarget, htargetF.le⟩ hterminal
  have hcost := p.trace.inventory_cost_nonincreasing i
  unfold physicalInventoryCost at hcost
  rw [p.initial_prices i, p.initial_dollars i, p.terminal_dollars i] at hcost
  have hzero : inventoryCostCoordinate (F i) (response i).impact (F i) = 0 := by
    simp [inventoryCostCoordinate, coordinate_at_benchmark, shareResponseCoordinate_at_benchmark]
  rw [hzero] at hcost
  have hshares := mul_nonneg hF.le (p.trace.endpoint_no_short p.initial_holdings i)
  have hholding := mul_le_mul_of_nonneg_left hinventory hF.le
  rw [← inventoryCostCoordinate_lower_distance (F i) target (response i) hF htarget]
  exact hmon.trans (by linarith)

/-- Jordan negative variation of the ACTUAL scalar path: half of its
total variation minus its signed increment. This retains netting of
simultaneous buys/sells and is not a gross edge-sale budget. -/
def actualNegativeVariation (f : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (variationOnFromTo f (Icc a b) a b - (f b - f a)) / 2

theorem actualNegativeVariation_nonnegative (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : BoundedVariationOn f (Icc a b)) : 0 ≤ actualNegativeVariation f a b := by
  have hh := variationOnFromTo.sub_self_monotoneOn hf.locallyBoundedVariationOn
    (a := a) ⟨le_rfl, hab⟩ ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  simp only [Pi.sub_apply, variationOnFromTo.self] at hh
  unfold actualNegativeVariation
  linarith

theorem actualNegativeVariation_bounds_terminal_drop (f : ℝ → ℝ) (a b r : ℝ)
    (hab : a ≤ b) (hf : BoundedVariationOn f (Icc a b)) (hr : r ∈ Icc a b) :
    f r - f b ≤ actualNegativeVariation f a b := by
  have hl := hf.locallyBoundedVariationOn
  have hvar := variationOnFromTo.add hl ⟨le_rfl, hab⟩ hr ⟨hab, le_rfl⟩
  have hstart := variationOnFromTo.sub_self_monotoneOn hl (a := a)
    ⟨le_rfl, hab⟩ ⟨le_rfl, hab⟩ hr hr.1
  simp only [Pi.sub_apply, variationOnFromTo.self] at hstart
  have htail : f r - f b ≤ variationOnFromTo f (Icc a b) r b := by
    rw [variationOnFromTo.eq_of_le f (Icc a b) hr.2]
    have hfinite := hl r b hr ⟨hab, le_rfl⟩
    have he := ENNReal.toReal_mono hfinite (eVariationOn.edist_le f
      (s := Icc a b ∩ Icc r b) ⟨hr, le_rfl, hr.2⟩ ⟨⟨hab, le_rfl⟩, hr.2, le_rfl⟩)
    rw [← dist_edist, Real.dist_eq] at he
    exact (le_abs_self (f r - f b)).trans he
  unfold actualNegativeVariation
  linarith

/-- Monotone reparametrization preserves true Jordan negative variation,
not merely an upper bound based on gross executions. -/
theorem actualNegativeVariation_reparam (f T : ℝ → ℝ) (a b A B : ℝ)
    (hT : MonotoneOn T (Icc A B)) (himage : T '' Icc A B = Icc a b)
    (hA : A ≤ B) (hta : T A = a) (htb : T B = b) :
    actualNegativeVariation (fun u => f (T u)) A B = actualNegativeVariation f a b := by
  have hh := variationOnFromTo.comp_eq_of_monotoneOn f T hT
    ⟨le_rfl, hA⟩ ⟨hA, le_rfl⟩
  simp only [Function.comp_def, himage, hta, htb] at hh
  unfold actualNegativeVariation
  simp only [hh, hta, htb]

theorem actualNegativeVariation_add (f : ℝ → ℝ) (a b c : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hf : BoundedVariationOn f (Icc a c)) :
    actualNegativeVariation f a b + actualNegativeVariation f b c = actualNegativeVariation f a c := by
  have hleft : variationOnFromTo f (Icc a c) a b = variationOnFromTo f (Icc a b) a b := by
    rw [variationOnFromTo.eq_of_le _ _ hab, variationOnFromTo.eq_of_le _ _ hab,
      inter_self, inter_eq_right.mpr (show Icc a b ⊆ Icc a c from fun x hx => ⟨hx.1, hx.2.trans hbc⟩)]
  have hright : variationOnFromTo f (Icc a c) b c = variationOnFromTo f (Icc b c) b c := by
    rw [variationOnFromTo.eq_of_le _ _ hbc, variationOnFromTo.eq_of_le _ _ hbc,
      inter_self, inter_eq_right.mpr (show Icc b c ⊆ Icc a c from fun x hx => ⟨hab.trans hx.1, hx.2⟩)]
  have hh := variationOnFromTo.add hf.locallyBoundedVariationOn
    ⟨le_rfl, hab.trans hbc⟩ ⟨hab, hbc⟩ ⟨hab.trans hbc, le_rfl⟩
  rw [hleft, hright] at hh
  unfold actualNegativeVariation
  linarith

theorem resource_last_zero_tail {y : ℝ → ℝ} {C : ℝ≥0} (hy : LipschitzWith C y)
    (a b : ℝ) (hab : a ≤ b) (hb : y b < 0) :
    ∃ r ∈ Icc a b, min (y a) 0 ≤ y r ∧ ∀ x ∈ Ioo r b, y x < 0 := by
  let K := Icc a b ∩ y ⁻¹' {0}
  by_cases hne : K.Nonempty
  · have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_singleton.preimage hy.continuous)
    obtain ⟨r, hr, hmax⟩ := hK.exists_isGreatest hne
    refine ⟨r, hr.1, ?_, ?_⟩
    · rw [show y r = 0 from hr.2]
      exact min_le_right _ _
    · intro x hx
      by_contra hn
      have hh : (0 : ℝ) ∈ uIcc (y x) (y b) := mem_uIcc_of_ge hb.le (le_of_not_gt hn)
      obtain ⟨z, hz, he⟩ := intermediate_value_uIcc hy.continuous.continuousOn hh
      have hxz : z ∈ Icc x b := by simpa [uIcc_of_le hx.2.le] using hz
      have hzr := hmax ⟨⟨hr.1.1.trans (hx.1.le.trans hxz.1), hxz.2⟩, he⟩
      linarith [hx.1, hxz.1]
  · have hn : ∀ x ∈ Icc a b, y x < 0 := by
      intro x hx
      by_contra hnot
      have hh : (0 : ℝ) ∈ uIcc (y x) (y b) := mem_uIcc_of_ge hb.le (le_of_not_gt hnot)
      obtain ⟨z, hz, he⟩ := intermediate_value_uIcc hy.continuous.continuousOn hh
      have hxz : z ∈ Icc x b := by simpa [uIcc_of_le hx.2] using hz
      exact hne ⟨z, ⟨⟨hx.1.trans hxz.1, hxz.2⟩, he⟩⟩
    exact ⟨a, ⟨le_rfl, hab⟩, min_le_left _ _, fun x hx => hn x ⟨hx.1.le, hx.2.le⟩⟩

/-- Endpoint resource loss is charged to the actual control's Jordan
negative variation, using only its real derivative and inward recovery. -/
theorem resource_loss_le_actual_negative_variation
    {y f ys fs : ℝ → ℝ} {C D : ℝ≥0} (hy : LipschitzWith C y) (hf : LipschitzWith D f)
    (a b : ℝ) (hab : a ≤ b)
    (hdy : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt y (ys x) x)
    (hdf : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt f (fs x) x)
    (hrec : ∀ᵐ x ∂volume, x ∈ Ioo a b → y x < 0 → fs x ≤ ys x) :
    min (y a) 0 - actualNegativeVariation f a b ≤ y b := by
  have hfBV : BoundedVariationOn f (Icc a b) := by
    have hh := hf.locallyBoundedVariationOn (Icc a b)
    simpa only [inter_self] using hh a b ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩
  by_cases hb : 0 ≤ y b
  · have hv := actualNegativeVariation_nonnegative f a b hab hfBV
    linarith [min_le_right (y a) (0 : ℝ)]
  · obtain ⟨r, hr, hyr, htail⟩ := resource_last_zero_tail hy a b hab (lt_of_not_ge hb)
    have hd : ∀ᵐ x ∂volume, x ∈ Ioo r b → HasDerivAt (fun u => y u - f u) (ys x - fs x) x := by
      filter_upwards [hdy, hdf] with x hx hy hmem
      have hxm : x ∈ Ioo a b := ⟨hr.1.trans_lt hmem.1, hmem.2⟩
      exact (hx hxm).sub (hy hxm)
    have hftc := (lipschitzOn_integral_eq_sub_of_hasDerivAt_ae (hy.sub hf).lipschitzOnWith hr.2 hd).2
    have hi : 0 ≤ ∫ x in r..b, ys x - fs x := by
      apply intervalIntegral.integral_nonneg_of_ae_restrict hr.2
      filter_upwards [ae_restrict_of_ae hrec, ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (show ∀ᵐ x : ℝ ∂volume, x ≠ r by simp [ae_iff]),
        ae_restrict_of_ae (show ∀ᵐ x : ℝ ∂volume, x ≠ b by simp [ae_iff])] with x hx hmem hxr hxb
      have hxi : x ∈ Ioo r b := ⟨lt_of_le_of_ne hmem.1 hxr.symm, lt_of_le_of_ne hmem.2 hxb⟩
      exact sub_nonneg.mpr (hx ⟨hr.1.trans_lt hxi.1, hxi.2⟩ (htail x hxi))
    rw [hftc] at hi
    have hv := actualNegativeVariation_bounds_terminal_drop f a b r hab hfBV hr
    linarith

variable {m : PhysicalContinuousBVPiece edges} {scale : ℝ}

theorem PhysicalBVClock.negative_variation_reparam (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (f : ℝ → ℝ) :
    actualNegativeVariation (fun u => f (c.time u)) c.A c.B = actualNegativeVariation f m.a m.b := by
  have hmono := (m.execution.variationClock_strictMono scale hs.le).monotone
  have horder : c.A ≤ c.B := hmono m.time_order
  have himage : c.time '' Icc c.A c.B = Icc m.a m.b := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact c.time_range u
    · intro ht
      refine ⟨m.execution.variationClock scale t, ⟨hmono ht.1, hmono ht.2⟩, c.time_clock t ht⟩
  exact actualNegativeVariation_reparam f c.time m.a m.b c.A c.B
    (c.monotone_time.monotoneOn _) himage horder
    (c.time_clock m.a ⟨le_rfl, m.time_order⟩) (c.time_clock m.b ⟨m.time_order, le_rfl⟩)

theorem PhysicalBVClock.global_response_coordinate_lipschitz
    (c : PhysicalBVClock m scale) (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C
      (fun u => coordinate (m.F i) (m.response i).impact (m.prices (c.time u) i)) := by
  obtain ⟨C, hC⟩ := c.coordinate_lipschitz_asset hs i
  refine ⟨C, c.global_lipschitz_of_reparam hs (fun t => coordinate (m.F i) (m.response i).impact (m.prices t i)) ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [Subtype.dist_eq] using hC.dist_le_mul u u.property v v.property

theorem PhysicalBVClock.global_share_coordinate_lipschitz
    (c : PhysicalBVClock m scale) (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C
      (fun u => shareResponseCoordinate (m.F i) (m.response i).impact (m.prices (c.time u) i)) := by
  obtain ⟨C, hC⟩ := c.share_coordinate_lipschitz hs i
  refine ⟨C, c.global_lipschitz_of_reparam hs (fun t => shareResponseCoordinate (m.F i) (m.response i).impact (m.prices t i)) ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u v
  simpa only [Subtype.dist_eq] using hC.dist_le_mul u u.property v v.property

theorem PhysicalContinuousBVPiece.share_resource_lower
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    min (shareResponseCoordinate (m.F i) (m.response i).impact (m.prices m.a i)) 0 -
      actualNegativeVariation (fun t => m.shares t i) m.a m.b ≤
        shareResponseCoordinate (m.F i) (m.response i).impact (m.prices m.b i) := by
  obtain ⟨c⟩ := m.exists_physicalBVClock 1 (by norm_num)
  obtain ⟨C, hC⟩ := c.global_share_coordinate_lipschitz (by norm_num) i
  obtain ⟨D, hD⟩ := c.global_shares_lipschitz (by norm_num) i
  have horder : c.A ≤ c.B := (m.execution.variationClock_strictMono 1 (by norm_num)).monotone m.time_order
  have hdy : ∀ᵐ u ∂volume, u ∈ Ioo c.A c.B →
      HasDerivAt (fun u => shareResponseCoordinate (m.F i) (m.response i).impact (m.prices (c.time u) i))
        (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i -
          m.rho i * (m.prices (c.time u) i - m.F i) / (m.response i).impact (m.prices (c.time u) i) *
            deriv c.timeIntegrator u) u := by
    filter_upwards [c.share_coordinate_derivative_ae (by norm_num) i] with u hu hmem
    exact hu ⟨hmem.1.le, hmem.2.le⟩
  have hdf : ∀ᵐ u ∂volume, u ∈ Ioo c.A c.B → HasDerivAt (fun u => m.shares (c.time u) i)
      (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i) u := by
    filter_upwards [c.physical_ode_ae (by norm_num)] with u hu hmem
    exact (hu ⟨hmem.1.le, hmem.2.le⟩).2.2.2.1 i
  have hrec : ∀ᵐ u ∂volume, u ∈ Ioo c.A c.B →
      shareResponseCoordinate (m.F i) (m.response i).impact (m.prices (c.time u) i) < 0 →
      tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i ≤
        tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i -
          m.rho i * (m.prices (c.time u) i - m.F i) / (m.response i).impact (m.prices (c.time u) i) *
            deriv c.timeIntegrator u := by
    filter_upwards [] with u hmem hneg
    have hp := m.positive_prices _ (c.time_range u) i
    have hg := (m.response i).positive _ hp
    have hbelow : m.prices (c.time u) i < m.F i := by
      by_contra hn
      have hh := (shareResponseCoordinate_strictMonoOn (m.F i) (m.response i) (m.benchmark_positive i)).monotoneOn
        (m.benchmark_positive i) hp (le_of_not_gt hn)
      rw [shareResponseCoordinate_at_benchmark] at hh
      linarith
    have hn := mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
        (m.resilience_nonnegative i) (sub_nonpos.mpr hbelow.le)) hg.le)
      (c.actual_speeds_nonnegative u).1
    linarith
  have hh := resource_loss_le_actual_negative_variation hC hD c.A c.B horder hdy hdf hrec
  rw [c.negative_variation_reparam (by norm_num) (fun t => m.shares t i)] at hh
  have hta : c.time c.A = m.a := c.time_clock m.a ⟨le_rfl, m.time_order⟩
  have htb : c.time c.B = m.b := c.time_clock m.b ⟨m.time_order, le_rfl⟩
  simpa [hta, htb] using hh

theorem PhysicalContinuousBVPiece.dollar_resource_lower
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    min (coordinate (m.F i) (m.response i).impact (m.prices m.a i)) 0 -
      actualNegativeVariation (fun t => m.dollarLedger t i) m.a m.b ≤
        coordinate (m.F i) (m.response i).impact (m.prices m.b i) := by
  obtain ⟨c⟩ := m.exists_physicalBVClock 1 (by norm_num)
  obtain ⟨C, hC⟩ := c.global_response_coordinate_lipschitz (by norm_num) i
  obtain ⟨D, hD⟩ := c.global_ledger_lipschitz (by norm_num) i
  have horder : c.A ≤ c.B := (m.execution.variationClock_strictMono 1 (by norm_num)).monotone m.time_order
  let net := fun u => tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i
  let slope := fun u => net u - m.rho i *
    (m.prices (c.time u) i * (m.prices (c.time u) i - m.F i) /
      (m.response i).impact (m.prices (c.time u) i)) * deriv c.timeIntegrator u
  have hdy : ∀ᵐ u ∂volume, u ∈ Ioo c.A c.B →
      HasDerivAt (fun u => coordinate (m.F i) (m.response i).impact (m.prices (c.time u) i)) (slope u) u := by
    filter_upwards [c.physical_ode_ae (by norm_num)] with u hu hmem
    have hp := m.positive_prices _ (c.time_range u) i
    have hg := (m.response i).positive _ hp
    have hh := (coordinate_hasDerivAt (m.F i) (m.response i) (m.benchmark_positive i) hp).comp u
      ((hu ⟨hmem.1.le, hmem.2.le⟩).2.2.1 i)
    convert hh using 1 <;> dsimp [Function.comp, slope, net] <;> field_simp [hp.ne', hg.ne'] <;> ring
  have hdf : ∀ᵐ u ∂volume, u ∈ Ioo c.A c.B → HasDerivAt (fun u => m.dollarLedger (c.time u) i) (net u) u := by
    filter_upwards [c.physical_ode_ae (by norm_num)] with u hu hmem
    exact (hu ⟨hmem.1.le, hmem.2.le⟩).2.2.2.2 i
  have hrec : ∀ᵐ u ∂volume, u ∈ Ioo c.A c.B →
      coordinate (m.F i) (m.response i).impact (m.prices (c.time u) i) < 0 → net u ≤ slope u := by
    filter_upwards [] with u hmem hneg
    have hp := m.positive_prices _ (c.time_range u) i
    have hg := (m.response i).positive _ hp
    have hbelow : m.prices (c.time u) i < m.F i := by
      by_contra hn
      have hh := (coordinate_strictMonoOn (m.F i) (m.response i) (m.benchmark_positive i)).monotoneOn
        (m.benchmark_positive i) hp (le_of_not_gt hn)
      rw [coordinate_at_benchmark] at hh
      linarith
    have hn := mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (m.resilience_nonnegative i)
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hp.le
          (sub_nonpos.mpr hbelow.le)) hg.le)) (c.actual_speeds_nonnegative u).1
    dsimp [slope]
    linarith
  have hh := resource_loss_le_actual_negative_variation hC hD c.A c.B horder hdy hdf hrec
  rw [c.negative_variation_reparam (by norm_num) (fun t => m.dollarLedger t i)] at hh
  have hta : c.time c.A = m.a := c.time_clock m.a ⟨le_rfl, m.time_order⟩
  have htb : c.time c.B = m.b := c.time_clock m.b ⟨m.time_order, le_rfl⟩
  simpa [hta, htb] using hh

theorem OriginalFlowCompletedPulse.ledger_boundedVariation
    (p : OriginalFlowCompletedPulse edges) (i : ι) :
    BoundedVariationOn (fun a => p.dollarLedger a i) (Icc 0 1) := by
  let net := tradingInput (pairedMatrix edges) p.dollars i
  let f := fun a => p.dollarLedger 0 i + a * net
  have hL : LipschitzWith (⟨|net|, abs_nonneg net⟩ : ℝ≥0) f := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simp only [Real.dist_eq, NNReal.coe_mk]
    rw [show f a - f b = (a - b) * net by dsimp [f]; ring, abs_mul]
    exact le_of_eq (mul_comm _ _)
  have heq : EqOn (fun a => p.dollarLedger a i) f (Icc 0 1) := by
    intro a ha
    have hh := p.marginal_dollar_primitive i a ha
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hh
    dsimp [f, net]
    linarith
  unfold BoundedVariationOn
  rw [eVariationOn.eq_of_eqOn heq]
  have hh := hL.locallyBoundedVariationOn (Icc (0 : ℝ) 1)
  simpa only [inter_self] using hh 0 1 ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩

def OriginalPhysicalStep.shareSales
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : ℝ :=
  match step with
  | .continuous m _ _ _ _ => actualNegativeVariation (fun a => m.shares a i) m.a m.b
  | .pulse p _ _ _ => actualNegativeVariation (fun a => p.shares a i) 0 1

def OriginalPhysicalStep.dollarSales
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : ℝ :=
  match step with
  | .continuous m _ _ _ _ => actualNegativeVariation (fun a => m.dollarLedger a i) m.a m.b
  | .pulse p _ _ _ => actualNegativeVariation (fun a => p.dollarLedger a i) 0 1

def OriginalPhysicalStep.pairedTurnover
    (step : OriginalPhysicalStep F rho response edges s t) : ℝ :=
  match step with
  | .continuous m _ _ _ _ => ∑ e, ((m.execution.cumulative e) m.b - (m.execution.cumulative e) m.a)
  | .pulse p _ _ _ => ∑ e, p.dollars e

def OriginalPhysicalReachable.shareSales {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ι → ℝ
  | _, .refl _, _ => 0
  | _, .append previous step, i => previous.shareSales i + step.shareSales i

def OriginalPhysicalReachable.dollarSales {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ι → ℝ
  | _, .refl _, _ => 0
  | _, .append previous step, i => previous.dollarSales i + step.dollarSales i

def OriginalPhysicalReachable.pairedTurnover {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ℝ
  | _, .refl _ => 0
  | _, .append previous step => previous.pairedTurnover + step.pairedTurnover

theorem OriginalPhysicalStep.shareSales_nonnegative
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : 0 ≤ step.shareSales i := by
  cases step with
  | continuous m _ _ _ hv => exact actualNegativeVariation_nonnegative _ _ _ m.time_order (hv i)
  | pulse p _ _ hv => exact actualNegativeVariation_nonnegative _ _ _ (by norm_num) (hv i)

theorem OriginalPhysicalStep.dollarSales_nonnegative
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : 0 ≤ step.dollarSales i := by
  cases step with
  | continuous m _ _ _ _ =>
    obtain ⟨c⟩ := m.exists_physicalBVClock 1 (by norm_num)
    obtain ⟨C, hC⟩ := c.global_ledger_lipschitz (by norm_num) i
    have horder : c.A ≤ c.B := (m.execution.variationClock_strictMono 1 (by norm_num)).monotone m.time_order
    have hBV : BoundedVariationOn (fun u => m.dollarLedger (c.time u) i) (Icc c.A c.B) := by
      have hh := hC.locallyBoundedVariationOn (Icc c.A c.B)
      simpa only [inter_self] using hh c.A c.B ⟨le_rfl, horder⟩ ⟨horder, le_rfl⟩
    have hh := actualNegativeVariation_nonnegative _ _ _ horder hBV
    rw [c.negative_variation_reparam (by norm_num) (fun t => m.dollarLedger t i)] at hh
    exact hh
  | pulse p _ _ _ => exact actualNegativeVariation_nonnegative _ _ _ (by norm_num) (p.ledger_boundedVariation i)

theorem OriginalPhysicalStep.share_resource_lower
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) :
    min (shareResponseCoordinate (F i) (response i).impact (s.prices i)) 0 - step.shareSales i ≤
      shareResponseCoordinate (F i) (response i).impact (t.prices i) := by
  cases step with
  | continuous m hF hr hg _ =>
    simpa only [OriginalPhysicalStep.shareSales, hF, hg] using m.share_resource_lower i
  | pulse p hF hg hv =>
    have hh := p.share_coordinate_at_parameter 1 ⟨by norm_num, le_rfl⟩ i
    have hd := actualNegativeVariation_bounds_terminal_drop (fun a => p.shares a i) 0 1 0
      (by norm_num) (hv i) ⟨le_rfl, by norm_num⟩
    dsimp only [OriginalPhysicalStep.shareSales]
    rw [← hF, ← hg]
    linarith [min_le_left (shareResponseCoordinate (p.F i) (p.response i).impact (p.prices 0 i)) (0 : ℝ)]

theorem OriginalPhysicalStep.dollar_resource_lower
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) :
    min (coordinate (F i) (response i).impact (s.prices i)) 0 - step.dollarSales i ≤
      coordinate (F i) (response i).impact (t.prices i) := by
  cases step with
  | continuous m hF hr hg _ =>
    simpa only [OriginalPhysicalStep.dollarSales, hF, hg] using m.dollar_resource_lower i
  | pulse p hF hg _ =>
    have hh := p.coordinate_endpoint i
    have hl := p.ledger_endpoint i
    have hd := actualNegativeVariation_bounds_terminal_drop (fun a => p.dollarLedger a i) 0 1 0
      (by norm_num) (p.ledger_boundedVariation i) ⟨le_rfl, by norm_num⟩
    dsimp only [OriginalPhysicalStep.dollarSales]
    rw [← hF, ← hg]
    linarith [min_le_left (coordinate (p.F i) (p.response i).impact (p.prices 0 i)) (0 : ℝ)]

theorem OriginalPhysicalReachable.shareSales_nonnegative
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) : 0 ≤ trace.shareSales i := by
  induction trace with
  | refl => exact le_rfl
  | append previous step ih => exact add_nonneg ih (step.shareSales_nonnegative i)

theorem OriginalPhysicalReachable.dollarSales_nonnegative
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) : 0 ≤ trace.dollarSales i := by
  induction trace with
  | refl => exact le_rfl
  | append previous step ih => exact add_nonneg ih (step.dollarSales_nonnegative i)

theorem OriginalPhysicalReachable.share_resource_lower
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    min (shareResponseCoordinate (F i) (response i).impact (s.prices i)) 0 - trace.shareSales i ≤
      shareResponseCoordinate (F i) (response i).impact (t.prices i) := by
  induction trace with
  | refl => simpa [OriginalPhysicalReachable.shareSales] using min_le_left (shareResponseCoordinate (F i) (response i).impact (s.prices i)) (0 : ℝ)
  | @append mid t previous step ih =>
    have hn := previous.shareSales_nonnegative i
    have hh := step.share_resource_lower i
    have hm : min (shareResponseCoordinate (F i) (response i).impact (s.prices i)) 0 - previous.shareSales i ≤ 0 := by
      linarith [min_le_right (shareResponseCoordinate (F i) (response i).impact (s.prices i)) (0 : ℝ)]
    have hb := le_min ih hm
    dsimp only [OriginalPhysicalReachable.shareSales]
    linarith

theorem OriginalPhysicalReachable.dollar_resource_lower
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    min (coordinate (F i) (response i).impact (s.prices i)) 0 - trace.dollarSales i ≤
      coordinate (F i) (response i).impact (t.prices i) := by
  induction trace with
  | refl => simpa [OriginalPhysicalReachable.dollarSales] using min_le_left (coordinate (F i) (response i).impact (s.prices i)) (0 : ℝ)
  | @append mid t previous step ih =>
    have hn := previous.dollarSales_nonnegative i
    have hh := step.dollar_resource_lower i
    have hm : min (coordinate (F i) (response i).impact (s.prices i)) 0 - previous.dollarSales i ≤ 0 := by
      linarith [min_le_right (coordinate (F i) (response i).impact (s.prices i)) (0 : ℝ)]
    have hb := le_min ih hm
    dsimp only [OriginalPhysicalReachable.dollarSales]
    linarith

theorem resource_sum_of_qualifying_assets (R : ι → ℝ) (amount : ℝ)
    (hR : ∀ i, 0 ≤ R i) (Q : Finset ι) (k : ℕ) (hcard : k ≤ Q.card)
    (hqual : ∀ i ∈ Q, amount ≤ R i) : (k : ℝ) * amount ≤ ∑ i, R i := by
  classical
  obtain ⟨P, hPQ, hPk⟩ := Finset.exists_subset_card_eq hcard
  calc
    (k : ℝ) * amount = ∑ _i ∈ P, amount := by simp [hPk]
    _ ≤ ∑ i ∈ P, R i := Finset.sum_le_sum (fun i hi => hqual i (hPQ hi))
    _ ≤ ∑ i, R i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => hR i)

/-- Original crisis breadth supplies k distinct qualifying assets. The
resource quantities here are the actual completed-trace Jordan negative
variations, including netting, rather than gross edge-sale upper bounds. -/
theorem proposition_5_1_coordinate_resources
    [Nonempty ι] (F rho : ℝ) (g : Response)
    (p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) edges)
    (alpha delta : ℝ) (hα : 0 < alpha) (hα1 : alpha ≤ 1) (hδ : 0 < delta)
    (hcrisis : delta ≤ systemicCrisis (logPriceFromBenchmark F p.terminal.prices)
      (requiredAssetCount (ι := ι) alpha)) :
    (requiredAssetCount (ι := ι) alpha : ℝ) *
      (∫ u in F * Real.exp (-delta)..F, u / g.impact u) ≤ ∑ i, p.trace.dollarSales i ∧
    (requiredAssetCount (ι := ι) alpha : ℝ) *
      (∫ u in F * Real.exp (-delta)..F, 1 / g.impact u) ≤ ∑ i, p.trace.shareSales i := by
  classical
  have hF : 0 < F := p.benchmark_positive (Classical.choice (inferInstance : Nonempty ι))
  have hp : ∀ i, 0 < p.terminal.prices i := p.trace.endpoint_positive
    (fun i => by rw [p.initial_prices i]; exact hF)
  let target := F * Real.exp (-delta)
  have htarget : 0 < target := mul_pos hF (Real.exp_pos _)
  let Q := Finset.univ.filter (fun i => delta ≤ -logPriceFromBenchmark F p.terminal.prices i)
  have hk := requiredAssetCount_pos (ι := ι) alpha hα
  have hkn := requiredAssetCount_le_card (ι := ι) alpha hα1
  have hcard : requiredAssetCount (ι := ι) alpha ≤ Q.card :=
    ((systemicCrisis_threshold_iff (logPriceFromBenchmark F p.terminal.prices)
      (requiredAssetCount (ι := ι) alpha) hk hkn delta).mp hcrisis).2
  have hterminal : ∀ i ∈ Q, p.terminal.prices i ≤ target := by
    intro i hi
    exact rateBand_price_of_log_loss F _ delta hF (hp i) (Finset.mem_filter.mp hi).2
  have hdollar : ∀ i ∈ Q, -coordinate F g.impact target ≤ p.trace.dollarSales i := by
    intro i hi
    have hl := p.trace.dollar_resource_lower i
    rw [p.initial_prices i, coordinate_at_benchmark] at hl
    simp only [min_self] at hl
    have hm := (coordinate_strictMonoOn F g hF).monotoneOn (hp i) htarget (hterminal i hi)
    nlinarith
  have hshare : ∀ i ∈ Q, -shareResponseCoordinate F g.impact target ≤ p.trace.shareSales i := by
    intro i hi
    have hl := p.trace.share_resource_lower i
    rw [p.initial_prices i, shareResponseCoordinate_at_benchmark] at hl
    simp only [min_self] at hl
    have hm := (shareResponseCoordinate_strictMonoOn F g hF).monotoneOn (hp i) htarget (hterminal i hi)
    nlinarith
  have hd := resource_sum_of_qualifying_assets p.trace.dollarSales (-coordinate F g.impact target)
    p.trace.dollarSales_nonnegative Q (requiredAssetCount (ι := ι) alpha) hcard hdollar
  have hs := resource_sum_of_qualifying_assets p.trace.shareSales (-shareResponseCoordinate F g.impact target)
    p.trace.shareSales_nonnegative Q (requiredAssetCount (ι := ι) alpha) hcard hshare
  have heD : -coordinate F g.impact target = ∫ u in target..F, u / g.impact u := by
    unfold coordinate
    rw [intervalIntegral.integral_symm, neg_neg]
  have heS : -shareResponseCoordinate F g.impact target = ∫ u in target..F, 1 / g.impact u := by
    unfold shareResponseCoordinate
    rw [intervalIntegral.integral_symm, neg_neg]
  rw [heD] at hd
  rw [heS] at hs
  exact ⟨hd, hs⟩

end MarketCrash
