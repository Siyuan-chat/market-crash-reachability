import MarketCrash.ACPhysicalSession
import MarketCrash.LipschitzFTC
import MarketCrash.CrisisQuantile

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace MarketCrash

theorem rateBand_lipschitz_mul {f g : ℝ → ℝ} {a b : ℝ} {C D : ℝ≥0}
    (hf : LipschitzOnWith C f (Icc a b)) (hg : LipschitzOnWith D g (Icc a b)) :
    ∃ E : ℝ≥0, LipschitzOnWith E (fun x => f x * g x) (Icc a b) := by
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image hf.continuousOn.norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hg.continuousOn.norm
  let A' : ℝ≥0 := ⟨max A 0, le_max_right _ _⟩
  let B' : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  refine ⟨A' * D + B' * C, LipschitzOnWith.of_dist_le_mul ?_⟩
  intro x hx y hy
  have hfx : |f x| ≤ A' := (hA (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  have hgy : |g y| ≤ B' := (hB (mem_image_of_mem _ hy)).trans (le_max_left _ _)
  have hfd := hf.dist_le_mul x hx y hy
  have hgd := hg.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at hfd hgd ⊢
  calc
    |f x * g x - f y * g y| = |f x * (g x - g y) + g y * (f x - f y)| := by congr 1; ring
    _ ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by simpa [abs_mul] using abs_add_le (f x * (g x - g y)) (g y * (f x - f y))
    _ ≤ (A' : ℝ) * (D * |x - y|) + (B' : ℝ) * (C * |x - y|) :=
      add_le_add (mul_le_mul hfx hgd (abs_nonneg _) A'.coe_nonneg)
        (mul_le_mul hgy hfd (abs_nonneg _) B'.coe_nonneg)
    _ = ↑(A' * D + B' * C) * |x - y| := by push_cast; ring

theorem rateBand_exp_lipschitz (rho a b : ℝ) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun x => Real.exp (rho * x)) (Icc a b) := by
  have hc : ContinuousOn (fun x => ‖Real.exp (rho * x) * rho‖) (Icc a b) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous_const).norm.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  refine ⟨C, (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x => Real.exp (rho * x) * rho) ?_ ?_⟩
  · intro x _
    simpa using (((hasDerivAt_id x).const_mul rho).exp).hasDerivWithinAt (s := Icc a b)
  · intro x hx
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)

/-- A.e. linear comparison using the proved Lipschitz FTC, not pointwise monotonicity. -/
theorem rateBand_nonnegative_of_derivative_ge_linear
    {H w : ℝ → ℝ} {a b rho : ℝ} {C : ℝ≥0}
    (hab : a ≤ b) (hH : LipschitzOnWith C H (Icc a b))
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt H (w x) x)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc a b → -rho * H x ≤ w x)
    (ha : 0 ≤ H a) : 0 ≤ H b := by
  obtain ⟨D, hD⟩ := rateBand_exp_lipschitz rho a b
  obtain ⟨E, hE⟩ := rateBand_lipschitz_mul hD hH
  let W := fun x => Real.exp (rho * x) * (rho * H x + w x)
  have hder : ∀ᵐ x ∂volume, x ∈ Ioo a b →
      HasDerivAt (fun y => Real.exp (rho * y) * H y) (W x) x := by
    filter_upwards [hd] with x hx hmem
    convert (((hasDerivAt_id x).const_mul rho).exp.mul (hx hmem)) using 1 <;> dsimp [W] <;> ring
  obtain ⟨_, hftc⟩ := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hE hab hder
  have hn : 0 ≤ ∫ x in a..b, W x := by
    apply intervalIntegral.integral_nonneg_of_ae_restrict hab
    filter_upwards [ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Icc] with x hx hmem
    exact mul_nonneg (Real.exp_pos _).le (by linarith [hx hmem])
  rw [hftc] at hn
  have hh : 0 ≤ Real.exp (rho * b) * H b :=
    le_trans (mul_nonneg (Real.exp_pos _).le ha) (by linarith)
  exact nonneg_of_mul_nonneg_right hh (Real.exp_pos _)

/-- Scalar finite-rate floor for an actual Lipschitz price and its a.e. ODE. -/
theorem rateBand_scalar_floor {S w : ℝ → ℝ} {C : ℝ≥0}
    (F rho A t : ℝ) (hrho : 0 < rho) (ht : 0 ≤ t)
    (hS : LipschitzOnWith C S (Icc 0 t)) (hzero : S 0 = F)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo 0 t → HasDerivAt S (w x) x)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc 0 t → -rho * (S x - F) - A ≤ w x) :
    F - A / rho * (1 - Real.exp (-rho * t)) ≤ S t := by
  let B := A / rho
  let H := fun x => S x - (F - B) - B * Real.exp (-rho * x)
  obtain ⟨D, hD⟩ := rateBand_exp_lipschitz (-rho) 0 t
  have hc : LipschitzOnWith 0 (fun _ : ℝ => B) (Icc 0 t) :=
    (LipschitzWith.const B).lipschitzOnWith
  obtain ⟨E, hE⟩ := rateBand_lipschitz_mul hc hD
  have hH : LipschitzOnWith (C + E) H (Icc 0 t) := by
    have hc' : LipschitzOnWith 0 (fun _ : ℝ => F - B) (Icc 0 t) :=
      (LipschitzWith.const (F - B)).lipschitzOnWith
    simpa [H] using (hS.sub hc').sub hE
  let W := fun x => w x + B * rho * Real.exp (-rho * x)
  have hHd : ∀ᵐ x ∂volume, x ∈ Ioo 0 t → HasDerivAt H (W x) x := by
    filter_upwards [hd] with x hx hmem
    convert ((hx hmem).sub_const (F - B)).sub
      ((((hasDerivAt_id x).const_mul (-rho)).exp).const_mul B) using 1 <;> dsimp [H, W] <;> ring
  have hHb : ∀ᵐ x ∂volume, x ∈ Icc 0 t → -rho * H x ≤ W x := by
    filter_upwards [hb] with x hx hmem
    have hBr : B * rho = A := by dsimp [B]; exact div_mul_cancel₀ A hrho.ne'
    dsimp [H, W]
    nlinarith [hx hmem]
  have hH0 : 0 ≤ H 0 := by simp [H, hzero]
  have hh := rateBand_nonnegative_of_derivative_ge_linear ht hH hHd hHb hH0
  dsimp [H, B] at hh
  linarith

theorem ACPhysicalSession.rate_floor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v G : ℝ) (hv : m.RateBounded v) (ha : m.a = 0)
    (hstart : ∀ i, m.prices 0 i = m.F i)
    (hG : ∀ x ∈ Icc m.a m.b, ∀ i, (m.response i).impact (m.prices x i) ≤ G)
    (i : ι) (hrho : 0 < m.rho i) (t : ℝ) (ht : t ∈ Icc 0 m.b) :
    m.F i - G * v / m.rho i * (1 - Real.exp (-m.rho i * t)) ≤ m.prices t i := by
  obtain ⟨C, hC⟩ := m.prices_lipschitz v hv i
  have hsub : Icc 0 t ⊆ Icc m.a m.b := by
    intro x hx
    rw [ha]
    exact ⟨hx.1, hx.2.trans ht.2⟩
  apply rateBand_scalar_floor (m.F i) (m.rho i) (G * v) t hrho ht.1
    (hC.mono hsub) (hstart i)
  · filter_upwards [m.physical_derivative] with x hx hmem
    exact hx (hsub ⟨hmem.1.le, hmem.2.le⟩) i
  · filter_upwards [m.local_capacity, hv.2] with x hx hcap hmem
    have hm := hsub hmem
    have hp := m.positive_prices x hm i
    have hg := (m.response i).positive _ hp
    have hn : -v ≤ tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i := by
      have habs : |tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i| ≤ v := by
        rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
        exact (hx hm i).2.trans (by nlinarith [hcap hm i])
      exact (abs_le.mp habs).1
    have hb := mul_le_mul_of_nonneg_left hn hg.le
    have hu := mul_le_mul_of_nonneg_right (hG x hm i) hv.1
    nlinarith

theorem rateBand_crisis_of_floor {ι : Type*} [Fintype ι] [Nonempty ι]
    (F L : ℝ) (prices : ι → ℝ) (hF : 0 < F) (hL : 0 < L)
    (hS : ∀ i, L ≤ prices i) (k : ℕ) (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    meanLogLoss (logPriceFromBenchmark F prices) ≤ Real.log (F / L) ∧
    coverageQuantile (logPriceFromBenchmark F prices) k ≤ Real.log (F / L) ∧
    systemicCrisis (logPriceFromBenchmark F prices) k ≤ Real.log (F / L) := by
  have hp : ∀ i, 0 < prices i := fun i => hL.trans_le (hS i)
  have hloss : ∀ i, -logPriceFromBenchmark F prices i ≤ Real.log (F / L) := by
    intro i
    rw [← actualLogLoss_eq_neg_logPrice F prices hF hp i]
    exact Real.log_le_log (div_pos hF (hp i)) (div_le_div_of_nonneg_left hF.le hL (hS i))
  have hmean : meanLogLoss (logPriceFromBenchmark F prices) ≤ Real.log (F / L) := by
    rw [meanLogLoss_eq_actual F prices hF hp]
    apply (div_le_iff₀ (by exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι))).mpr
    calc
      ∑ i, actualLogLoss F prices i ≤ ∑ _i : ι, Real.log (F / L) := by
        apply Finset.sum_le_sum
        intro i _
        rw [actualLogLoss_eq_neg_logPrice F prices hF hp i]
        exact hloss i
      _ = Real.log (F / L) * (Fintype.card ι : ℝ) := by simp [mul_comm]
  obtain ⟨i, _, heq, _⟩ := coverageQuantile_eq_max_candidate (logPriceFromBenchmark F prices) k hk hkn
  exact ⟨hmean, heq ▸ hloss i, (systemicCrisis_le_meanLogLoss _ k).trans hmean⟩

theorem rateBand_max_floor (F G v rho T t β : ℝ) (hGv : 0 ≤ G * v)
    (hrho : 0 < rho) (ht : t ≤ T) (hβ : β < 1) (hF : 0 < F) (S : ℝ)
    (hband : F * (1 - β) ≤ S)
    (hrate : F - G * v / rho * (1 - Real.exp (-rho * t)) ≤ S) :
    0 < max (F * (1 - β)) (F - G * v / rho * (1 - Real.exp (-rho * T))) ∧
    max (F * (1 - β)) (F - G * v / rho * (1 - Real.exp (-rho * T))) ≤ S := by
  constructor
  · exact (mul_pos hF (by linarith)).trans_le (le_max_left _ _)
  · apply max_le hband
    have he : Real.exp (-rho * T) ≤ Real.exp (-rho * t) := Real.exp_le_exp.mpr (by nlinarith)
    have hn : 0 ≤ G * v / rho := div_nonneg hGv hrho.le
    nlinarith

theorem rateBand_necessary_speed_of_individual_loss (F G v rho T δ S : ℝ)
    (hG : 0 < G) (hrho : 0 < rho) (hT : 0 < T)
    (hfloor : F - G * v / rho * (1 - Real.exp (-rho * T)) ≤ S)
    (hloss : S ≤ F * Real.exp (-δ)) :
    rho * F * (1 - Real.exp (-δ)) / (G * (1 - Real.exp (-rho * T))) ≤ v := by
  have hd : 0 < 1 - Real.exp (-rho * T) := by
    have := Real.exp_lt_one_iff.mpr (show -rho * T < 0 by nlinarith)
    linarith
  apply (div_le_iff₀ (mul_pos hG hd)).mpr
  have hm := mul_le_mul_of_nonneg_right (hfloor.trans hloss) hrho.le
  have he : G * v / rho * rho = G * v := div_mul_cancel₀ _ hrho.ne'
  nlinarith

theorem rateBand_price_of_log_loss (F S δ : ℝ) (hF : 0 < F) (hS : 0 < S)
    (hloss : δ ≤ -Real.log (S / F)) : S ≤ F * Real.exp (-δ) := by
  have he := Real.exp_le_exp.mpr (show Real.log (S / F) ≤ -δ by linarith)
  rw [Real.exp_log (div_pos hS hF)] at he
  have hh := (div_le_iff₀ hF).mp he
  simpa [mul_comm] using hh

theorem rateBand_necessary_speed_of_crisis {ι : Type*} [Fintype ι] [Nonempty ι]
    (F G v rho T δ : ℝ) (prices : ι → ℝ) (k : ℕ)
    (hF : 0 < F) (hG : 0 < G) (hrho : 0 < rho) (hT : 0 < T)
    (hp : ∀ i, 0 < prices i) (hk : 0 < k) (hkn : k ≤ Fintype.card ι)
    (hfloor : ∀ i, F - G * v / rho * (1 - Real.exp (-rho * T)) ≤ prices i)
    (hcrisis : δ ≤ systemicCrisis (logPriceFromBenchmark F prices) k) :
    rho * F * (1 - Real.exp (-δ)) / (G * (1 - Real.exp (-rho * T))) ≤ v := by
  obtain ⟨⟨i, hi⟩, _⟩ := coverageQuantile_is_kth_largest (logPriceFromBenchmark F prices) k hk hkn
  have hl : δ ≤ -Real.log (prices i / F) := by
    have hh := hcrisis.trans (min_le_right (meanLogLoss (logPriceFromBenchmark F prices))
      (coverageQuantile (logPriceFromBenchmark F prices) k))
    rw [hi] at hh
    exact hh
  exact rateBand_necessary_speed_of_individual_loss F G v rho T δ (prices i) hG hrho hT
    (hfloor i) (rateBand_price_of_log_loss F _ δ hF (hp i) hl)

/-- Hypothetical proportional resets: the prices themselves satisfy the product bound. -/
theorem rateBand_reset_product (F : ℝ) (factor price : ℕ → ℝ)
    (hfactor : ∀ d, 0 ≤ factor d) (hzero : F ≤ price 0)
    (hstep : ∀ d, factor d * price d ≤ price (d + 1)) :
    ∀ D, F * ∏ d ∈ Finset.range D, factor d ≤ price D := by
  intro D
  induction D with
  | zero => simpa using hzero
  | succ D ih =>
    rw [Finset.prod_range_succ]
    calc
      F * ((∏ d ∈ Finset.range D, factor d) * factor D) =
          factor D * (F * ∏ d ∈ Finset.range D, factor d) := by ring
      _ ≤ factor D * price D := mul_le_mul_of_nonneg_left ih (hfactor D)
      _ ≤ price (D + 1) := hstep D

theorem rateBand_reset_crisis {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (factor : ℕ → ℝ) (prices : ι → ℝ) (D k : ℕ)
    (hF : 0 < F) (hfactor : ∀ d < D, 0 < factor d)
    (hS : ∀ i, F * ∏ d ∈ Finset.range D, factor d ≤ prices i)
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    systemicCrisis (logPriceFromBenchmark F prices) k ≤
      -∑ d ∈ Finset.range D, Real.log (factor d) := by
  have hp : 0 < ∏ d ∈ Finset.range D, factor d :=
    Finset.prod_pos (fun d hd => hfactor d (Finset.mem_range.mp hd))
  have hh := (rateBand_crisis_of_floor F (F * ∏ d ∈ Finset.range D, factor d)
    prices hF (mul_pos hF hp) hS k hk hkn).2.2
  have he : Real.log (F / (F * ∏ d ∈ Finset.range D, factor d)) =
      -∑ d ∈ Finset.range D, Real.log (factor d) := by
    rw [Real.log_div hF.ne' (mul_pos hF hp).ne', Real.log_mul hF.ne' hp.ne',
      Real.log_prod _ _ (fun d hd => (hfactor d (Finset.mem_range.mp hd)).ne')]
    ring
  rw [he] at hh
  exact hh

theorem rateBand_reset_product_finite (F : ℝ) (factor price : ℕ → ℝ) (D : ℕ)
    (hfactor : ∀ d < D, 0 ≤ factor d) (hzero : F ≤ price 0)
    (hstep : ∀ d < D, factor d * price d ≤ price (d + 1)) :
    F * ∏ d ∈ Finset.range D, factor d ≤ price D := by
  induction D with
  | zero => simpa using hzero
  | succ D ih =>
    have hh := ih (fun d hd => hfactor d (Nat.lt_trans hd (Nat.lt_succ_self D)))
      (fun d hd => hstep d (Nat.lt_trans hd (Nat.lt_succ_self D)))
    rw [Finset.prod_range_succ]
    calc
      F * ((∏ d ∈ Finset.range D, factor d) * factor D) =
          factor D * (F * ∏ d ∈ Finset.range D, factor d) := by ring
      _ ≤ factor D * price D := mul_le_mul_of_nonneg_left hh (hfactor D (Nat.lt_succ_self D))
      _ ≤ price (D + 1) := hstep D (Nat.lt_succ_self D)

theorem rateBand_fixed_band_exclusion {ι : Type*} [Fintype ι] [Nonempty ι]
    (F β δ : ℝ) (prices : ι → ℝ) (k : ℕ) (hF : 0 < F) (hβ : β < 1)
    (hS : ∀ i, F * (1 - β) ≤ prices i) (hk : 0 < k) (hkn : k ≤ Fintype.card ι)
    (hδ : -Real.log (1 - β) < δ) :
    systemicCrisis (logPriceFromBenchmark F prices) k < δ := by
  have hp : 0 < 1 - β := by linarith
  have hh := (rateBand_crisis_of_floor F (F * (1 - β)) prices hF
    (mul_pos hF hp) hS k hk hkn).2.2
  have he : Real.log (F / (F * (1 - β))) = -Real.log (1 - β) := by
    rw [Real.log_div hF.ne' (mul_pos hF hp).ne', Real.log_mul hF.ne' hp.ne']
    ring
  exact (he ▸ hh).trans_lt hδ

/-- Proposition 6.1: the original finite-rate physical integral model,
with all one-session scalar, breadth, necessary-speed and band clauses.
The separately proved reset lemmas apply only to the hypothetical regime. -/
theorem proposition_6_1_rate_band
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (F rho G v β : ℝ) (hF : 0 < F) (hrho : 0 < rho) (hG : 0 < G)
    (hβ : β < 1) (ha : m.a = 0) (hFi : ∀ i, m.F i = F)
    (hri : ∀ i, m.rho i = rho) (hv : m.RateBounded v)
    (hstart : ∀ i, m.prices 0 i = F)
    (himpact : ∀ x ∈ Icc 0 m.b, ∀ i, (m.response i).impact (m.prices x i) ≤ G)
    (hband : ∀ x ∈ Icc 0 m.b, ∀ i, F * (1 - β) ≤ m.prices x i) :
    (∀ t ∈ Icc 0 m.b, ∀ i,
      F - G * v / rho * (1 - Real.exp (-rho * t)) ≤ m.prices t i) ∧
    (0 < max (F * (1 - β)) (F - G * v / rho * (1 - Real.exp (-rho * m.b)))) ∧
    (∀ t ∈ Icc 0 m.b, ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
      let k := requiredAssetCount (ι := ι) alpha
      let q := logPriceFromBenchmark F (m.prices t)
      meanLogLoss q ≤ Real.log (F / max (F * (1 - β))
        (F - G * v / rho * (1 - Real.exp (-rho * m.b)))) ∧
      coverageQuantile q k ≤ Real.log (F / max (F * (1 - β))
        (F - G * v / rho * (1 - Real.exp (-rho * m.b)))) ∧
      systemicCrisis q k ≤ Real.log (F / max (F * (1 - β))
        (F - G * v / rho * (1 - Real.exp (-rho * m.b))))) ∧
    (∀ t ∈ Icc 0 m.b, ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 → ∀ δ : ℝ,
      δ ≤ systemicCrisis (logPriceFromBenchmark F (m.prices t))
        (requiredAssetCount (ι := ι) alpha) →
      rho * F * (1 - Real.exp (-δ)) / (G * (1 - Real.exp (-rho * m.b))) ≤ v) ∧
    (∀ t ∈ Icc 0 m.b, ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 → ∀ δ : ℝ,
      -Real.log (1 - β) < δ →
      systemicCrisis (logPriceFromBenchmark F (m.prices t))
        (requiredAssetCount (ι := ι) alpha) < δ) := by
  have htime : 0 < m.b := by linarith [m.time_order]
  have hflo : ∀ t ∈ Icc 0 m.b, ∀ i,
      F - G * v / rho * (1 - Real.exp (-rho * t)) ≤ m.prices t i := by
    intro t ht i
    have hh := m.rate_floor v G hv ha (fun i => (hstart i).trans (hFi i).symm)
      (by simpa [ha] using himpact) i (by rw [hri]; exact hrho) t ht
    simpa [hFi, hri] using hh
  have hall (t : ℝ) (ht : t ∈ Icc 0 m.b) (i : ι) :=
    rateBand_max_floor F G v rho m.b t β (mul_nonneg hG.le hv.1) hrho ht.2 hβ hF
      (m.prices t i) (hband t ht i) (hflo t ht i)
  have hpos := (hall 0 ⟨le_rfl, htime.le⟩ (Classical.choice (inferInstance : Nonempty ι))).1
  refine ⟨hflo, hpos, ?_, ?_, ?_⟩
  · intro t ht alpha hα hα1
    exact rateBand_crisis_of_floor F _ (m.prices t) hF hpos
      (fun i => (hall t ht i).2) _
      (requiredAssetCount_pos alpha hα) (requiredAssetCount_le_card alpha hα1)
  · intro t ht alpha hα hα1 δ hδ
    apply rateBand_necessary_speed_of_crisis F G v rho m.b δ (m.prices t) _ hF hG hrho htime
      (fun i => m.positive_prices t (by simpa [ha] using ht) i)
      (requiredAssetCount_pos alpha hα) (requiredAssetCount_le_card alpha hα1) _ hδ
    intro i
    exact (le_max_right _ _).trans (hall t ht i).2
  · intro t ht alpha hα hα1 δ hδ
    exact rateBand_fixed_band_exclusion F β δ (m.prices t) _ hF hβ (hband t ht)
      (requiredAssetCount_pos alpha hα) (requiredAssetCount_le_card alpha hα1) hδ

/-- The rate-only clauses require no price-band premise. -/
theorem proposition_6_1_rate_only
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (F rho G v : ℝ) (hF : 0 < F) (hrho : 0 < rho) (hG : 0 < G)
    (ha : m.a = 0) (hFi : ∀ i, m.F i = F) (hri : ∀ i, m.rho i = rho)
    (hv : m.RateBounded v) (hstart : ∀ i, m.prices 0 i = F)
    (himpact : ∀ x ∈ Icc 0 m.b, ∀ i, (m.response i).impact (m.prices x i) ≤ G) :
    (∀ t ∈ Icc 0 m.b, ∀ i,
      F - G * v / rho * (1 - Real.exp (-rho * t)) ≤ m.prices t i) ∧
    (∀ t ∈ Icc 0 m.b, ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 → ∀ δ : ℝ,
      δ ≤ systemicCrisis (logPriceFromBenchmark F (m.prices t))
        (requiredAssetCount (ι := ι) alpha) →
      rho * F * (1 - Real.exp (-δ)) / (G * (1 - Real.exp (-rho * m.b))) ≤ v) := by
  have htime : 0 < m.b := by linarith [m.time_order]
  have hflo : ∀ t ∈ Icc 0 m.b, ∀ i,
      F - G * v / rho * (1 - Real.exp (-rho * t)) ≤ m.prices t i := by
    intro t ht i
    have hh := m.rate_floor v G hv ha (fun i => (hstart i).trans (hFi i).symm)
      (by simpa [ha] using himpact) i (by rw [hri]; exact hrho) t ht
    simpa [hFi, hri] using hh
  refine ⟨hflo, ?_⟩
  intro t ht alpha hα hα1 δ hδ
  apply rateBand_necessary_speed_of_crisis F G v rho m.b δ (m.prices t) _ hF hG hrho htime
    (fun i => m.positive_prices t (by simpa [ha] using ht) i)
    (requiredAssetCount_pos alpha hα) (requiredAssetCount_le_card alpha hα1) _ hδ
  intro i
  have he : Real.exp (-rho * m.b) ≤ Real.exp (-rho * t) :=
    Real.exp_le_exp.mpr (by nlinarith [ht.2])
  have hn : 0 ≤ G * v / rho := div_nonneg (mul_nonneg hG.le hv.1) hrho.le
  nlinarith [hflo t ht i]

/-- The hypothetical reset regime, with only the stated D sessions quantified. -/
theorem proposition_6_1_hypothetical_reset
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (beta : ℕ → ℝ) (prices : ℕ → ι → ℝ) (D : ℕ)
    (hF : 0 < F) (hbeta : ∀ d < D, beta d < 1)
    (hzero : ∀ i, F ≤ prices 0 i)
    (hstep : ∀ d < D, ∀ i, (1 - beta d) * prices d i ≤ prices (d + 1) i) :
    (∀ i, F * ∏ d ∈ Finset.range D, (1 - beta d) ≤ prices D i) ∧
    (∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
      systemicCrisis (logPriceFromBenchmark F (prices D))
        (requiredAssetCount (ι := ι) alpha) ≤
        -∑ d ∈ Finset.range D, Real.log (1 - beta d)) := by
  have hp : ∀ d < D, 0 < 1 - beta d := by intro d hd; linarith [hbeta d hd]
  have hS : ∀ i, F * ∏ d ∈ Finset.range D, (1 - beta d) ≤ prices D i := by
    intro i
    exact rateBand_reset_product_finite F (fun d => 1 - beta d) (fun d => prices d i) D
      (fun d hd => (hp d hd).le) (hzero i) (fun d hd => hstep d hd i)
  refine ⟨hS, ?_⟩
  intro alpha hα hα1
  exact rateBand_reset_crisis F (fun d => 1 - beta d) (prices D) D _ hF hp hS
    (requiredAssetCount_pos alpha hα) (requiredAssetCount_le_card alpha hα1)

end MarketCrash
