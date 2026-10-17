import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MarketCrash.CrisisQuantile
import MarketCrash.IntervalODEEnclosure
import MarketCrash.OriginalInputPackaging
import MarketCrash.CertificateCoarseBootstrap

/-! Exact arithmetic parts of Proposition 7.6 only.
These declarations do NOT certify the ODE enclosure or assert an admissible witness. -/
noncomputable section
namespace MarketCrash
namespace OriginalCertificate

def plateauPolynomial (h : ℝ) : ℝ := 101600000000 * h ^ 2 - 97138000000 * h - 6646157699
def plateauLower : ℝ := 102020225507905 / 100000000000000
def plateauUpper : ℝ := 102020225507908 / 100000000000000

theorem plateau_exact_signs :
    plateauPolynomial plateauLower = -726172695155753 / 500000000000000000 ∧
    plateauPolynomial plateauUpper = 1447396528633183 / 781250000000000000 := by
  norm_num [plateauPolynomial, plateauLower, plateauUpper]

theorem plateauPolynomial_strictMono : StrictMonoOn plateauPolynomial (Set.Ici (1 : ℝ)) := by
  intro x hx y _ hxy
  have hcoef : 0 < 101600000000 * (y + x) - 97138000000 := by
    have hxx : 1 ≤ x := hx
    linarith
  have hp := mul_pos (sub_pos.mpr hxy) hcoef
  have he : plateauPolynomial y - plateauPolynomial x =
      (y - x) * (101600000000 * (y + x) - 97138000000) := by
    dsimp [plateauPolynomial]
    ring
  linarith

theorem plateau_exists_unique :
    ∃! h : ℝ, plateauLower < h ∧ h < plateauUpper ∧ plateauPolynomial h = 0 := by
  have horder : plateauLower ≤ plateauUpper := by norm_num [plateauLower, plateauUpper]
  have hc : Continuous plateauPolynomial := by unfold plateauPolynomial; fun_prop
  have hl : plateauPolynomial plateauLower < 0 := by rw [plateau_exact_signs.1]; norm_num
  have hu : 0 < plateauPolynomial plateauUpper := by rw [plateau_exact_signs.2]; norm_num
  obtain ⟨h, hh, hroot⟩ := intermediate_value_Icc horder hc.continuousOn ⟨hl.le, hu.le⟩
  have hstrict : plateauLower < h ∧ h < plateauUpper := by
    constructor
    · apply lt_of_le_of_ne hh.1
      intro he
      rw [he, hroot] at hl
      exact (lt_irrefl 0) hl
    · apply lt_of_le_of_ne hh.2
      intro he
      rw [← he, hroot] at hu
      exact (lt_irrefl 0) hu
  refine ⟨h, ⟨hstrict.1, hstrict.2, hroot⟩, ?_⟩
  intro y hy
  apply plateauPolynomial_strictMono.injOn
    (show (1 : ℝ) ≤ y by have := hy.1; norm_num [plateauLower] at *; linarith)
    (show (1 : ℝ) ≤ h by have := hstrict.1; norm_num [plateauLower] at *; linarith)
  rw [hy.2.2, hroot]

/-- Exact executed target dollars on one linear segment, before any ODE certificate. -/
def linearSegmentDollars (x0 x1 duration : ℝ) : ℝ :=
  (x1 ^ 2 - x0 ^ 2) / 2 + (2 / 5 : ℝ) * duration *
    ((x0 ^ 2 + x0 * x1 + x1 ^ 2) / 3 - (x0 + x1) / 2)

def targetTotalDollars (h : ℝ) : ℝ :=
  linearSegmentDollars 1 h (23 / 10) + linearSegmentDollars h h (77 / 5) +
  linearSegmentDollars h (97 / 100) (23 / 10) +
  linearSegmentDollars (97 / 100) (199 / 200) (23 / 10) +
  linearSegmentDollars (199 / 200) (199 / 200) (77 / 5) +
  linearSegmentDollars (199 / 200) (9409 / 10000) (23 / 10)

theorem target_closure_polynomial (h : ℝ) :
    targetTotalDollars h = plateauPolynomial h / 15000000000 := by
  dsimp [targetTotalDollars, linearSegmentDollars, plateauPolynomial]
  ring

theorem exact_root_closes_target_formula (h : ℝ) (hh : plateauPolynomial h = 0) :
    targetTotalDollars h = 0 := by rw [target_closure_polynomial, hh, zero_div]

theorem linearSegmentDollars_eq_physical_integral (x0 x1 duration : ℝ) (hτ : 0 < duration) :
    linearSegmentDollars x0 x1 duration =
      ∫ t in (0 : ℝ)..duration,
        (x0 + (x1 - x0) / duration * t) *
          ((x1 - x0) / duration + (2 / 5 : ℝ) *
            (x0 + (x1 - x0) / duration * t - 1)) := by
  let v := (x1 - x0) / duration
  let A := x0 * v + (2 / 5 : ℝ) * x0 * (x0 - 1)
  let B := v ^ 2 + (2 / 5 : ℝ) * v * (2 * x0 - 1)
  let P := fun t : ℝ => A * t + B * t ^ 2 / 2 + (2 / 5 : ℝ) * v ^ 2 * t ^ 3 / 3
  have hd (t : ℝ) : HasDerivAt P ((x0 + v * t) * (v + (2 / 5 : ℝ) * (x0 + v * t - 1))) t := by
    have hh := (((hasDerivAt_id t).const_mul A).add
      (((hasDerivAt_id t).pow 2).const_mul B |>.div_const 2)).add
      ((((hasDerivAt_id t).pow 3).const_mul ((2 / 5 : ℝ) * v ^ 2)).div_const 3)
    convert hh using 1
    dsimp [P, A, B]
    ring
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (by apply Continuous.intervalIntegrable; fun_prop :
      IntervalIntegrable (fun t : ℝ => (x0 + v * t) * (v + (2 / 5 : ℝ) * (x0 + v * t - 1)))
        MeasureTheory.volume 0 duration)
  rw [hf]
  dsimp [P, A, B, v, linearSegmentDollars]
  field_simp [hτ.ne']
  ring

def physicalSegmentDollars (x0 x1 duration : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..duration,
    (x0 + (x1 - x0) / duration * t) *
      ((x1 - x0) / duration + (2 / 5 : ℝ) * (x0 + (x1 - x0) / duration * t - 1))

def targetPhysicalTotalDollars (h : ℝ) : ℝ :=
  physicalSegmentDollars 1 h (23 / 10) + physicalSegmentDollars h h (77 / 5) +
  physicalSegmentDollars h (97 / 100) (23 / 10) +
  physicalSegmentDollars (97 / 100) (199 / 200) (23 / 10) +
  physicalSegmentDollars (199 / 200) (199 / 200) (77 / 5) +
  physicalSegmentDollars (199 / 200) (9409 / 10000) (23 / 10)

theorem target_physical_integrals_closed_of_root (h : ℝ) (hh : plateauPolynomial h = 0) :
    targetPhysicalTotalDollars h = 0 := by
  have he (x0 x1 d : ℝ) (hd : 0 < d) : physicalSegmentDollars x0 x1 d = linearSegmentDollars x0 x1 d :=
    (linearSegmentDollars_eq_physical_integral x0 x1 d hd).symm
  unfold targetPhysicalTotalDollars
  rw [he 1 h _ (by norm_num), he h h _ (by norm_num), he h (97 / 100) _ (by norm_num),
    he (97 / 100) (199 / 200) _ (by norm_num), he (199 / 200) (199 / 200) _ (by norm_num),
    he (199 / 200) (9409 / 10000) _ (by norm_num)]
  exact exact_root_closes_target_formula h hh

/-- The endpoint product test is exact arithmetic; the exp enclosure and ODE
endpoint enclosure themselves still need a soundness proof. -/
theorem reported_endpoint_product_margin :
    (20882528819217335957269139578158522089 : ℝ) / 17097168546330468750000000000000000000 *
      ((9409 : ℝ) / 10000) ^ 9 *
      ((140555423111958453123472102742373 : ℝ) / 100000000000000000000000000000000) < 1 := by
  norm_num

theorem reported_resource_margins :
    (284480404287 : ℚ) / 1000000000000 < 285 / 1000 ∧
    (187934212473014020097377836279580 : ℚ) / 100000000000000000000000000000000 < 2 ∧
    (16925450899741382062689416295734 : ℚ) / 100000000000000000000000000000000 < 2 ∧
    (298308878179821217357707560765354 : ℚ) / 100000000000000000000000000000000 < 3 := by
  norm_num

/-- A purely analytic rational-power alternative to the exp(0.20) output:
this remains conditional on the actual compensator endpoint enclosure. -/
theorem terminal_log_margins_of_endpoint_bound (y : ℝ) (hy : 0 < y)
    (hymax : y ≤ (140555423111958453123472102742373 : ℝ) / 100000000000000000000000000000000) :
    (201 : ℝ) / 10000 < -Real.log ((9409 : ℝ) / 10000) ∧
    (201 : ℝ) / 10000 < (-9 * Real.log ((9409 : ℝ) / 10000) - Real.log y) / 10 := by
  have hsmall := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 98489 / 100000)
  have htarget := Real.log_le_log (by norm_num : (0 : ℝ) < 97 / 100)
    (show (97 : ℝ) / 100 ≤ ((98489 : ℝ) / 100000) ^ 2 by norm_num)
  rw [Real.log_pow] at htarget
  have htarget2 : Real.log ((9409 : ℝ) / 10000) = 2 * Real.log ((97 : ℝ) / 100) := by
    have he : ((9409 : ℝ) / 10000) = ((97 : ℝ) / 100) ^ 2 := by norm_num
    rw [he, Real.log_pow]
    norm_num
  have htargetBound : Real.log ((9409 : ℝ) / 10000) ≤ -(1511 : ℝ) / 25000 := by
    rw [htarget2]
    nlinarith
  have hpow : (140555423111958453123472102742373 : ℝ) / 100000000000000000000000000000000 ≤
      ((10107 : ℝ) / 10000) ^ 32 := by norm_num
  have hcomp := Real.log_le_log hy (hymax.trans hpow)
  rw [Real.log_pow] at hcomp
  have hroot := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10107 / 10000)
  constructor <;> nlinarith

def terminalPrices (y : ℝ) (i : Fin 10) : ℝ := if i.val < 9 then 9409 / 10000 else y

theorem actual_crisis_of_endpoint_bound (y : ℝ) (hy : 0 < y)
    (hymax : y ≤ (140555423111958453123472102742373 : ℝ) / 100000000000000000000000000000000) :
    (1 : ℝ) / 50 < systemicCrisis (logPriceFromBenchmark 1 (terminalPrices y))
      (requiredAssetCount (ι := Fin 10) ((9 : ℝ) / 10)) := by
  have hm := terminal_log_margins_of_endpoint_bound y hy hymax
  have hp : ∀ i, 0 < terminalPrices y i := by
    intro i
    dsimp [terminalPrices]
    split <;> positivity
  have hk : requiredAssetCount (ι := Fin 10) ((9 : ℝ) / 10) = 9 := by
    norm_num [requiredAssetCount]
  have hmean : (201 : ℝ) / 10000 ≤
      (∑ i : Fin 10, actualLogLoss 1 (terminalPrices y) i) / (Fintype.card (Fin 10) : ℝ) := by
    have hs : (∑ i : Fin 10, actualLogLoss 1 (terminalPrices y) i) =
        -9 * Real.log ((9409 : ℝ) / 10000) - Real.log y := by
      simp [Fin.sum_univ_succ, terminalPrices, actualLogLoss, Real.log_inv]
      ring
    rw [hs]
    simpa using hm.2.le
  have hcount : 9 ≤ (Finset.univ.filter (fun i : Fin 10 =>
      (201 : ℝ) / 10000 ≤ actualLogLoss 1 (terminalPrices y) i)).card := by
    have hsub : (Finset.univ.erase (⟨9, by norm_num⟩ : Fin 10)) ⊆
        Finset.univ.filter (fun i : Fin 10 => (201 : ℝ) / 10000 ≤ actualLogLoss 1 (terminalPrices y) i) := by
      intro i hi
      have hne : i ≠ (⟨9, by norm_num⟩ : Fin 10) := (Finset.mem_erase.mp hi).1
      have hil : i.val < 9 := by
        have ht := i.isLt
        have hv : i.val ≠ 9 := fun he => hne (Fin.ext he)
        omega
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [actualLogLoss, terminalPrices, if_pos hil, one_div, Real.log_inv] using hm.1.le
    have hh := Finset.card_le_card hsub
    simpa using hh
  have hc := (actual_systemic_crisis_threshold_iff 1 (terminalPrices y) (by norm_num) hp
    ((9 : ℝ) / 10) (by norm_num) (by norm_num) ((201 : ℝ) / 10000)).mpr
      ⟨hmean, by simpa only [hk] using hcount⟩
  exact lt_of_lt_of_le (by norm_num) hc

def targetBuyingDollars (u : ℝ) : ℝ := max u 0
def targetSellingDollars (u : ℝ) : ℝ := max (-u) 0

/-- The directed controls are gross, nonnegative, and never count the same
paired dollar a second time at its receiving endpoint. -/
theorem directed_dollar_controls (u : ℝ) :
    0 ≤ targetBuyingDollars u ∧ 0 ≤ targetSellingDollars u ∧
    targetBuyingDollars u - targetSellingDollars u = u ∧
    targetBuyingDollars u + targetSellingDollars u = |u| ∧
    targetBuyingDollars u * targetSellingDollars u = 0 := by
  by_cases hu : 0 ≤ u
  · simp [targetBuyingDollars, targetSellingDollars, max_eq_left hu,
      max_eq_right (neg_nonpos.mpr hu), abs_of_nonneg hu, hu]
  · have hun : u ≤ 0 := le_of_not_ge hu
    simp [targetBuyingDollars, targetSellingDollars, max_eq_right hun,
      max_eq_left (neg_nonneg.mpr hun), abs_of_nonpos hun, hun]

theorem target_physical_rate_identity (x velocity : ℝ) (hx : x ≠ 0) :
    let u := x * (velocity + (2 / 5 : ℝ) * (x - 1))
    (targetBuyingDollars u - targetSellingDollars u) / x =
      velocity + (2 / 5 : ℝ) * (x - 1) := by
  dsimp
  rw [(directed_dollar_controls _).2.2.1]
  exact mul_div_cancel_left₀ _ hx

theorem nine_edges_single_count (u : ℝ) :
    (∑ _i : Fin 9, (targetBuyingDollars u + targetSellingDollars u)) = 9 * |u| ∧
    (∑ _i : Fin 9, (targetBuyingDollars u - targetSellingDollars u)) + (-9 * u) = 0 := by
  rw [(directed_dollar_controls u).2.2.2.1, (directed_dollar_controls u).2.2.1]
  simp

theorem directed_share_rate_bounds (u x y R : ℝ)
    (hx : 0 < x) (hy : 0 < y) (_hR : 0 ≤ R)
    (ht : |u| ≤ R * x) (hc : 9 * |u| ≤ R * y) :
    (targetBuyingDollars u + targetSellingDollars u) / x ≤ R ∧
    (9 * (targetBuyingDollars u + targetSellingDollars u)) / y ≤ R := by
  rw [(directed_dollar_controls u).2.2.2.1]
  exact ⟨(div_le_iff₀ hx).mpr ht, (div_le_iff₀ hy).mpr hc⟩

/-- Inventory is controlled by integrated selling shares, with purchases
retained in the physical primitive instead of an assumed inventory bound. -/
theorem inventory_positive_of_selling_bound (U P : ℝ → ℝ) (a b s₀ : ℝ)
    (hab : a ≤ b) (hp : ∀ t ∈ Set.Icc a b, 0 < P t)
    (hbuy : IntervalIntegrable (fun t => targetBuyingDollars (U t) / P t)
      MeasureTheory.volume a b)
    (hsell : IntervalIntegrable (fun t => targetSellingDollars (U t) / P t)
      MeasureTheory.volume a b)
    (hbound : (∫ t in a..b, targetSellingDollars (U t) / P t) < s₀) :
    0 < s₀ + ∫ t in a..b, U t / P t := by
  have hidentity : (∫ t in a..b, U t / P t) =
      (∫ t in a..b, targetBuyingDollars (U t) / P t) -
        (∫ t in a..b, targetSellingDollars (U t) / P t) := by
    rw [← intervalIntegral.integral_sub hbuy hsell]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [← sub_div, (directed_dollar_controls (U t)).2.2.1]
  have hb : 0 ≤ ∫ t in a..b, targetBuyingDollars (U t) / P t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (directed_dollar_controls (U t)).1 (hp t ht).le
  rw [hidentity]
  linarith

theorem inventory_positive_on_Icc_of_selling_bound (U P : ℝ → ℝ) (a b s₀ : ℝ)
    (hab : a ≤ b) (hp : ∀ t ∈ Set.Icc a b, 0 < P t)
    (hbuy : IntervalIntegrable (fun t => targetBuyingDollars (U t) / P t)
      MeasureTheory.volume a b)
    (hsell : IntervalIntegrable (fun t => targetSellingDollars (U t) / P t)
      MeasureTheory.volume a b)
    (hbound : (∫ t in a..b, targetSellingDollars (U t) / P t) < s₀) :
    ∀ t ∈ Set.Icc a b, 0 < s₀ + ∫ u in a..t, U u / P u := by
  intro t ht
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hnon : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ioc a b)]
      (fun u => targetSellingDollars (U u) / P u) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    exact div_nonneg (directed_dollar_controls (U u)).2.1 (hp u ⟨hu.1.le, hu.2⟩).le
  have hle := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 hnon hsell
  apply inventory_positive_of_selling_bound U P a t s₀ ht.1
    (fun u hu => hp u ⟨hu.1, hu.2.trans ht.2⟩)
    (hbuy.mono_set hsub) (hsell.mono_set hsub)
  exact hle.trans_lt hbound

def targetLine (x₀ x₁ a b t : ℝ) : ℝ := x₀ + (x₁ - x₀) / (b - a) * (t - a)

def targetSchedule (h t : ℝ) : ℝ :=
  if t ≤ 23 / 10 then targetLine 1 h 0 (23 / 10) t
  else if t ≤ 177 / 10 then h
  else if t ≤ 20 then targetLine h (97 / 100) (177 / 10) 20 t
  else if t ≤ 223 / 10 then targetLine (97 / 100) (199 / 200) 20 (223 / 10) t
  else if t ≤ 377 / 10 then 199 / 200
  else targetLine (199 / 200) (9409 / 10000) (377 / 10) 40 t

theorem targetLine_continuous (x₀ x₁ a b : ℝ) : Continuous (targetLine x₀ x₁ a b) := by
  unfold targetLine
  fun_prop

theorem continuous_join_le (f g : ℝ → ℝ) (b : ℝ)
    (hf : Continuous f) (hg : Continuous g) (heq : f b = g b) :
    Continuous (fun t => if t ≤ b then f t else g t) := by
  apply hf.if_le hg continuous_id continuous_const
  intro t ht
  change t = b at ht
  subst t
  exact heq

theorem targetSchedule_continuous (h : ℝ) : Continuous (targetSchedule h) := by
  unfold targetSchedule
  apply continuous_join_le _ _ _ (targetLine_continuous _ _ _ _)
  · apply continuous_join_le _ _ _ continuous_const
    · apply continuous_join_le _ _ _ (targetLine_continuous _ _ _ _)
      · apply continuous_join_le _ _ _ (targetLine_continuous _ _ _ _)
        · apply continuous_join_le _ _ _ continuous_const (targetLine_continuous _ _ _ _)
          norm_num [targetLine]
        · norm_num [targetLine]
      · norm_num [targetLine]
    · norm_num [targetLine]
  · norm_num [targetLine]

theorem targetSchedule_knots (h : ℝ) :
    targetSchedule h 0 = 1 ∧ targetSchedule h (23 / 10) = h ∧
    targetSchedule h (177 / 10) = h ∧ targetSchedule h 20 = 97 / 100 ∧
    targetSchedule h (223 / 10) = 199 / 200 ∧
    targetSchedule h (377 / 10) = 199 / 200 ∧ targetSchedule h 40 = 9409 / 10000 := by
  norm_num [targetSchedule, targetLine]

theorem targetLine_mem (x₀ x₁ a b t lower upper : ℝ) (hab : a < b)
    (ht : t ∈ Set.Icc a b) (hx₀ : x₀ ∈ Set.Icc lower upper)
    (hx₁ : x₁ ∈ Set.Icc lower upper) : targetLine x₀ x₁ a b t ∈ Set.Icc lower upper := by
  let θ := (t - a) / (b - a)
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.mpr ht.1) (sub_nonneg.mpr hab.le)
  have hθ1 : θ ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith [ht.2])
  have hm := (convex_Icc lower upper) hx₀ hx₁ (sub_nonneg.mpr hθ1) hθ0
    (show (1 - θ) + θ = 1 by ring)
  convert hm using 1; simp only [smul_eq_mul]; dsimp [targetLine, θ]; ring

/-- Both target rolling bands follow from the actual continuous schedule;
the second reference is the actual close x(20)=0.97. -/
theorem targetSchedule_rolling_bands (h : ℝ) (hh : h ∈ Set.Icc (1 : ℝ) (103 / 100)) :
    (∀ t ∈ Set.Icc (0 : ℝ) 20, targetSchedule h t ∈ Set.Icc (97 / 100) (103 / 100)) ∧
    (∀ t ∈ Set.Icc (20 : ℝ) 40, targetSchedule h t ∈
      Set.Icc ((97 / 100 : ℝ) * (97 / 100)) ((103 / 100 : ℝ) * (97 / 100))) := by
  constructor
  · intro t ht
    by_cases h1 : t ≤ 23 / 10
    · simp only [targetSchedule, if_pos h1]
      apply targetLine_mem _ _ _ _ _ _ _ (by norm_num) ⟨ht.1, h1⟩
      · norm_num
      · constructor <;> linarith [hh.1, hh.2]
    · by_cases h2 : t ≤ 177 / 10
      · simp only [targetSchedule, if_neg h1, if_pos h2]
        constructor <;> linarith [hh.1, hh.2]
      · simp only [targetSchedule, if_neg h1, if_neg h2, if_pos ht.2]
        apply targetLine_mem _ _ _ _ _ _ _ (by norm_num) ⟨(lt_of_not_ge h2).le, ht.2⟩
        · constructor <;> linarith [hh.1, hh.2]
        · norm_num
  · intro t ht
    by_cases heq : t = 20
    · subst t
      rw [(targetSchedule_knots h).2.2.2.1]
      norm_num
    have h20 : 20 < t := lt_of_le_of_ne ht.1 (Ne.symm heq)
    have h1 : ¬t ≤ 23 / 10 := by linarith
    have h2 : ¬t ≤ 177 / 10 := by linarith
    have h3 : ¬t ≤ 20 := not_le.mpr h20
    simp only [targetSchedule, if_neg h1, if_neg h2, if_neg h3]
    by_cases h4 : t ≤ 223 / 10
    · rw [if_pos h4]
      apply targetLine_mem _ _ _ _ _ _ _ (by norm_num) ⟨ht.1, h4⟩ <;> norm_num
    · rw [if_neg h4]
      by_cases h5 : t ≤ 377 / 10
      · rw [if_pos h5]
        norm_num
      · rw [if_neg h5]
        apply targetLine_mem _ _ _ _ _ _ _ (by norm_num) ⟨(lt_of_not_ge h5).le, ht.2⟩ <;> norm_num

theorem targetLine_hasDerivAt (x₀ x₁ a b t : ℝ) :
    HasDerivAt (targetLine x₀ x₁ a b) ((x₁ - x₀) / (b - a)) t := by
  simpa only [targetLine, mul_one, sub_zero] using
    ((((hasDerivAt_id t).sub_const a).const_mul ((x₁ - x₀) / (b - a))).const_add x₀)

theorem targetLine_lipschitz (x₀ x₁ a b s t : ℝ) (K : NNReal)
    (hslope : |(x₁ - x₀) / (b - a)| ≤ K) :
    LipschitzOnWith K (targetLine x₀ x₁ a b) (Set.Icc s t) := by
  apply (convex_Icc s t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun u _ => (targetLine_hasDerivAt x₀ x₁ a b u).hasDerivWithinAt)
  intro u _
  rw [← NNReal.coe_le_coe]
  exact hslope

theorem targetSchedule_positive (h : ℝ) (hh : h ∈ Set.Icc (1 : ℝ) (103 / 100)) :
    ∀ t ∈ Set.Icc (0 : ℝ) 40, 0 < targetSchedule h t := by
  intro t ht
  obtain ⟨hday1, hday2⟩ := targetSchedule_rolling_bands h hh
  by_cases ht20 : t ≤ 20
  · have hm := (hday1 t ⟨ht.1, ht20⟩).1
    linarith
  · have hm := (hday2 t ⟨(lt_of_not_ge ht20).le, ht.2⟩).1
    norm_num at hm
    linarith

theorem targetSchedule_lipschitz (h : ℝ) (hh : h ∈ Set.Icc (1 : ℝ) (103 / 100)) :
    LipschitzOnWith (3 / 100 : NNReal) (targetSchedule h) (Set.Icc (0 : ℝ) 40) := by
  let K : NNReal := 3 / 100
  have hc (r s t : ℝ) : LipschitzOnWith K (fun _ : ℝ => r) (Set.Icc s t) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x _ y _
    simp only [dist_self]
    exact mul_nonneg K.coe_nonneg dist_nonneg
  let L5 := targetLine (199 / 200) (9409 / 10000) (377 / 10) 40
  have h5 : LipschitzOnWith K L5 (Set.Icc (377 / 10) 40) := by
    apply targetLine_lipschitz
    norm_num [K, abs_div]
  let L4 := joinSolutions (fun _ => (199 / 200 : ℝ)) L5 (377 / 10)
  have h4 : LipschitzOnWith K L4 (Set.Icc (223 / 10) 40) := by
    apply joinSolutions_lipschitz _ _ _ _ _ K (by norm_num) (by norm_num)
      (hc _ _ _) h5
    norm_num [L5, targetLine]
  let L3 := joinSolutions (targetLine (97 / 100) (199 / 200) 20 (223 / 10)) L4 (223 / 10)
  have h3 : LipschitzOnWith K L3 (Set.Icc 20 40) := by
    refine joinSolutions_lipschitz _ _ _ _ _ K (by norm_num) (by norm_num) ?_ h4 ?_
    · apply targetLine_lipschitz
      norm_num [K, abs_div]
    · norm_num [L4, joinSolutions, targetLine]
  let L2 := joinSolutions (targetLine h (97 / 100) (177 / 10) 20) L3 20
  have h2 : LipschitzOnWith K L2 (Set.Icc (177 / 10) 40) := by
    refine joinSolutions_lipschitz _ _ _ _ _ K (by norm_num) (by norm_num) ?_ h3 ?_
    · apply targetLine_lipschitz
      rw [abs_le]
      constructor <;> norm_num [K] <;> linarith [hh.1, hh.2]
    · norm_num [L3, joinSolutions, targetLine]
  let L1 := joinSolutions (fun _ => h) L2 (177 / 10)
  have h1 : LipschitzOnWith K L1 (Set.Icc (23 / 10) 40) := by
    apply joinSolutions_lipschitz _ _ _ _ _ K (by norm_num) (by norm_num)
      (hc _ _ _) h2
    norm_num [L2, joinSolutions, targetLine]
  have h0 : LipschitzOnWith K
      (joinSolutions (targetLine 1 h 0 (23 / 10)) L1 (23 / 10)) (Set.Icc 0 40) := by
    refine joinSolutions_lipschitz _ _ _ _ _ K (by norm_num) (by norm_num) ?_ h1 ?_
    · apply targetLine_lipschitz
      rw [abs_le]
      constructor <;> norm_num [K] <;> linarith [hh.1, hh.2]
    · norm_num [L1, joinSolutions, targetLine]
  simpa only [targetSchedule, L1, L2, L3, L4, L5, joinSolutions, K] using h0

def targetVelocity (h t : ℝ) : ℝ :=
  if t ≤ 23 / 10 then (h - 1) / (23 / 10)
  else if t ≤ 177 / 10 then 0
  else if t ≤ 20 then (97 / 100 - h) / (23 / 10)
  else if t ≤ 223 / 10 then (199 / 200 - 97 / 100) / (23 / 10)
  else if t ≤ 377 / 10 then 0
  else (9409 / 10000 - 199 / 200) / (23 / 10)

def actualTargetDollars (h t : ℝ) : ℝ :=
  targetSchedule h t * (targetVelocity h t + (2 / 5 : ℝ) * (targetSchedule h t - 1))

theorem targetSchedule_hasDerivAt_away (h t : ℝ)
    (h₁ : t ≠ 23 / 10) (h₂ : t ≠ 177 / 10) (h₃ : t ≠ 20)
    (h₄ : t ≠ 223 / 10) (h₅ : t ≠ 377 / 10) :
    HasDerivAt (targetSchedule h) (targetVelocity h t) t := by
  unfold targetVelocity
  split_ifs with q₁ q₂ q₃ q₄ q₅
  · have ht := lt_of_le_of_ne q₁ h₁
    have hd : HasDerivAt (targetLine 1 h 0 (23 / 10)) ((h - 1) / (23 / 10)) t := by
      simpa only [sub_zero] using targetLine_hasDerivAt 1 h 0 (23 / 10) t
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ht] with s hs
    change s < 23 / 10 at hs
    simp only [targetSchedule, if_pos hs.le]
  · have hlo : 23 / 10 < t := lt_of_not_ge q₁
    have hhi := lt_of_le_of_ne q₂ h₂
    apply (hasDerivAt_const t h).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
    simp only [targetSchedule, if_neg (not_le.mpr hs.1), if_pos hs.2.le]
  · have hlo : 177 / 10 < t := lt_of_not_ge q₂
    have hhi := lt_of_le_of_ne q₃ h₃
    have hd := targetLine_hasDerivAt h (97 / 100) (177 / 10) 20 t
    norm_num at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
    have hn₁ : ¬s ≤ 23 / 10 := by linarith [hs.1]
    simp only [targetSchedule, if_neg hn₁, if_neg (not_le.mpr hs.1), if_pos hs.2.le]
  · have hlo : 20 < t := lt_of_not_ge q₃
    have hhi := lt_of_le_of_ne q₄ h₄
    have hd := targetLine_hasDerivAt (97 / 100) (199 / 200) 20 (223 / 10) t
    norm_num at hd
    norm_num
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
    have hn₁ : ¬s ≤ 23 / 10 := by linarith [hs.1]
    have hn₂ : ¬s ≤ 177 / 10 := by linarith [hs.1]
    simp only [targetSchedule, if_neg hn₁, if_neg hn₂, if_neg (not_le.mpr hs.1), if_pos hs.2.le]
  · have hlo : 223 / 10 < t := lt_of_not_ge q₄
    have hhi := lt_of_le_of_ne q₅ h₅
    apply (hasDerivAt_const t (199 / 200)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hlo hhi] with s hs
    have hn₁ : ¬s ≤ 23 / 10 := by linarith [hs.1]
    have hn₂ : ¬s ≤ 177 / 10 := by linarith [hs.1]
    have hn₃ : ¬s ≤ 20 := by linarith [hs.1]
    simp only [targetSchedule, if_neg hn₁, if_neg hn₂, if_neg hn₃,
      if_neg (not_le.mpr hs.1), if_pos hs.2.le]
  · have hlo : 377 / 10 < t := lt_of_not_ge q₅
    have hd := targetLine_hasDerivAt (199 / 200) (9409 / 10000) (377 / 10) 40 t
    norm_num at hd
    norm_num
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hlo] with s hs
    change 377 / 10 < s at hs
    have hn₁ : ¬s ≤ 23 / 10 := by linarith
    have hn₂ : ¬s ≤ 177 / 10 := by linarith
    have hn₃ : ¬s ≤ 20 := by linarith
    have hn₄ : ¬s ≤ 223 / 10 := by linarith
    simp only [targetSchedule, if_neg hn₁, if_neg hn₂, if_neg hn₃, if_neg hn₄,
      if_neg (not_le.mpr hs)]

theorem targetSchedule_ae_hasDerivAt (h : ℝ) :
    ∀ᵐ t ∂MeasureTheory.volume, HasDerivAt (targetSchedule h) (targetVelocity h t) t := by
  have hne (r : ℝ) : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ r := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne (23 / 10), hne (177 / 10), hne 20, hne (223 / 10), hne (377 / 10)]
    with t h₁ h₂ h₃ h₄ h₅
  exact targetSchedule_hasDerivAt_away h t h₁ h₂ h₃ h₄ h₅

theorem targetSchedule_actual_ode (h : ℝ) (hh : h ∈ Set.Icc (1 : ℝ) (103 / 100)) :
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 40 →
      HasDerivAt (targetSchedule h)
        (compensatorField (-actualTargetDollars h t / 9) (targetSchedule h t)) t := by
  filter_upwards [targetSchedule_ae_hasDerivAt h] with t hd ht
  have hp : targetSchedule h t ≠ 0 :=
    (targetSchedule_positive h hh t ⟨ht.1.le, ht.2.le⟩).ne'
  have heq : compensatorField (-actualTargetDollars h t / 9) (targetSchedule h t) =
      targetVelocity h t := by
    dsimp [compensatorField, actualTargetDollars]
    field_simp [hp]
    ring
  rw [heq]
  exact hd

theorem targetSchedule_physical_primitive (h s t : ℝ)
    (hh : h ∈ Set.Icc (1 : ℝ) (103 / 100))
    (hs : s ∈ Set.Icc (0 : ℝ) 40) (ht : t ∈ Set.Icc (0 : ℝ) 40) (hst : s ≤ t) :
    IntervalIntegrable (fun u => actualTargetDollars h u / targetSchedule h u)
      MeasureTheory.volume s t ∧
    targetSchedule h t - targetSchedule h s =
      (∫ u in s..t, -(2 / 5 : ℝ) * (targetSchedule h u - 1)) +
      (∫ u in s..t, actualTargetDollars h u / targetSchedule h u) := by
  have hp := compensator_physical_price_primitive_on
    (fun u => -actualTargetDollars h u / 9) (targetSchedule h) 0 40 s t (3 / 100)
    hs ht hst (targetSchedule_lipschitz h hh) (targetSchedule_actual_ode h hh)
  have heq : (fun u => -9 * (-actualTargetDollars h u / 9) / targetSchedule h u) =
      (fun u => actualTargetDollars h u / targetSchedule h u) := by
    funext u
    ring
  simpa only [heq] using hp

theorem dollars_segment_from_open_formula (f : ℝ → ℝ) (x₀ x₁ a b : ℝ) (hab : a ≤ b)
    (heq : ∀ t ∈ Set.Ioo a b, f t = targetLine x₀ x₁ a b t *
      ((x₁ - x₀) / (b - a) + (2 / 5 : ℝ) * (targetLine x₀ x₁ a b t - 1))) :
    IntervalIntegrable f MeasureTheory.volume a b ∧
      (∫ t in a..b, f t) = physicalSegmentDollars x₀ x₁ (b - a) := by
  let G := fun t => targetLine x₀ x₁ a b t *
    ((x₁ - x₀) / (b - a) + (2 / 5 : ℝ) * (targetLine x₀ x₁ a b t - 1))
  have hg : Continuous G := by dsimp [G, targetLine]; fun_prop
  have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ b := by
    rw [MeasureTheory.ae_iff]
    simp
  have hae : f =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] G := by
    rw [Set.uIoc_of_le hab]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hne] with t ht hn
    exact heq t ⟨ht.1, lt_of_le_of_ne ht.2 hn⟩
  refine ⟨(hg.intervalIntegrable a b).congr hae.symm, ?_⟩
  rw [intervalIntegral.integral_congr_ae_restrict hae]
  let L := fun z => (x₀ + (x₁ - x₀) / (b - a) * z) *
    ((x₁ - x₀) / (b - a) + (2 / 5 : ℝ) * (x₀ + (x₁ - x₀) / (b - a) * z - 1))
  simpa only [G, L, targetLine, physicalSegmentDollars, sub_self] using
    (intervalIntegral.integral_comp_sub_right (a := a) (b := b) L a)

theorem actual_target_dollars_integral (h : ℝ) :
    IntervalIntegrable (actualTargetDollars h) MeasureTheory.volume 0 40 ∧
    (∫ t in (0 : ℝ)..40, actualTargetDollars h t) = targetPhysicalTotalDollars h := by
  have h₁ := dollars_segment_from_open_formula (actualTargetDollars h) 1 h 0 (23 / 10)
    (by norm_num) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso; linarith [ht.1, ht.2]) | (norm_num [targetLine]))
  have h₂ := dollars_segment_from_open_formula (actualTargetDollars h) h h (23 / 10) (177 / 10)
    (by norm_num) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso; linarith [ht.1, ht.2]) | (norm_num [targetLine]))
  have h₃ := dollars_segment_from_open_formula (actualTargetDollars h) h (97 / 100) (177 / 10) 20
    (by norm_num) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso; linarith [ht.1, ht.2]) | (norm_num [targetLine]))
  have h₄ := dollars_segment_from_open_formula (actualTargetDollars h) (97 / 100) (199 / 200) 20 (223 / 10)
    (by norm_num) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso; linarith [ht.1, ht.2]) | (norm_num [targetLine]))
  have h₅ := dollars_segment_from_open_formula (actualTargetDollars h) (199 / 200) (199 / 200)
    (223 / 10) (377 / 10) (by norm_num) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso; linarith [ht.1, ht.2]) | (norm_num [targetLine]))
  have h₆ := dollars_segment_from_open_formula (actualTargetDollars h) (199 / 200) (9409 / 10000)
    (377 / 10) 40 (by norm_num) (by
      intro t ht
      unfold actualTargetDollars targetSchedule targetVelocity
      split_ifs <;> first | (exfalso; linarith [ht.1, ht.2]) | (norm_num [targetLine]))
  have i₂ := h₁.1.trans h₂.1
  have i₃ := i₂.trans h₃.1
  have i₄ := i₃.trans h₄.1
  have i₅ := i₄.trans h₅.1
  refine ⟨i₅.trans h₆.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals i₅ h₆.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₄ h₅.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₃ h₄.1,
    ← intervalIntegral.integral_add_adjacent_intervals i₂ h₃.1,
    ← intervalIntegral.integral_add_adjacent_intervals h₁.1 h₂.1,
    h₁.2, h₂.2, h₃.2, h₄.2, h₅.2, h₆.2]
  norm_num [targetPhysicalTotalDollars]

theorem actual_target_dollar_ledger_closed (h : ℝ) (hh : plateauPolynomial h = 0) :
    (∫ t in (0 : ℝ)..40, actualTargetDollars h t) = 0 := by
  rw [(actual_target_dollars_integral h).2, target_physical_integrals_closed_of_root h hh]

theorem buyingDollars_formula (u : ℝ) : targetBuyingDollars u = (u + |u|) / 2 := by
  have h := directed_dollar_controls u
  linarith [h.2.2.1, h.2.2.2.1]

theorem sellingDollars_formula (u : ℝ) : targetSellingDollars u = (|u| - u) / 2 := by
  have h := directed_dollar_controls u
  linarith [h.2.2.1, h.2.2.2.1]

theorem actual_target_gross_integrable (h : ℝ) :
    IntervalIntegrable (fun t => targetBuyingDollars (actualTargetDollars h t))
      MeasureTheory.volume 0 40 ∧
    IntervalIntegrable (fun t => targetSellingDollars (actualTargetDollars h t))
      MeasureTheory.volume 0 40 := by
  have hi := (actual_target_dollars_integral h).1
  constructor
  · simpa only [buyingDollars_formula] using (hi.add hi.abs).div_const 2
  · simpa only [sellingDollars_formula] using (hi.abs.sub hi).div_const 2

theorem nonnegative_primitive_monotone (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hi : IntervalIntegrable f MeasureTheory.volume a b)
    (hn : ∀ t ∈ Set.Icc a b, 0 ≤ f t) :
    MonotoneOn (fun t => ∫ u in a..t, f u) (Set.Icc a b) := by
  intro s hs t ht hst
  have hsub : Set.uIcc a t ⊆ Set.uIcc a b := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le hab]
    exact fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  apply intervalIntegral.integral_mono_interval le_rfl hs.1 hst _ (hi.mono_set hsub)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
  exact hn u ⟨hu.1.le, hu.2.trans ht.2⟩

theorem integrable_primitive_continuous (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hi : IntervalIntegrable f MeasureTheory.volume a b) :
    ContinuousOn (fun t => ∫ u in a..t, f u) (Set.Icc a b) := by
  simpa only [Set.uIcc_of_le hab] using
    intervalIntegral.continuousOn_primitive_interval' hi
      (show a ∈ Set.uIcc a b from Set.left_mem_uIcc)

def targetBuyingCumulative (h t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t,
  targetBuyingDollars (actualTargetDollars h u)
def targetSellingCumulative (h t : ℝ) : ℝ := ∫ u in (0 : ℝ)..t,
  targetSellingDollars (actualTargetDollars h u)

theorem targetBuyingCumulative_monotone (h : ℝ) :
    MonotoneOn (targetBuyingCumulative h) (Set.Icc (0 : ℝ) 40) :=
  nonnegative_primitive_monotone _ 0 40 (by norm_num)
    (actual_target_gross_integrable h).1 (fun t _ => (directed_dollar_controls _).1)
theorem targetSellingCumulative_monotone (h : ℝ) :
    MonotoneOn (targetSellingCumulative h) (Set.Icc (0 : ℝ) 40) :=
  nonnegative_primitive_monotone _ 0 40 (by norm_num)
    (actual_target_gross_integrable h).2 (fun t _ => (directed_dollar_controls _).2.1)
theorem targetBuyingCumulative_continuous (h : ℝ) :
    ContinuousOn (targetBuyingCumulative h) (Set.Icc (0 : ℝ) 40) :=
  integrable_primitive_continuous _ 0 40 (by norm_num) (actual_target_gross_integrable h).1
theorem targetSellingCumulative_continuous (h : ℝ) :
    ContinuousOn (targetSellingCumulative h) (Set.Icc (0 : ℝ) 40) :=
  integrable_primitive_continuous _ 0 40 (by norm_num) (actual_target_gross_integrable h).2

def targetBuyingStieltjes (h : ℝ) : StieltjesFunction :=
  finiteContinuousStieltjesExtension 0 40 (by norm_num) (targetBuyingCumulative h)
    (targetBuyingCumulative_monotone h) (targetBuyingCumulative_continuous h)
def targetSellingStieltjes (h : ℝ) : StieltjesFunction :=
  finiteContinuousStieltjesExtension 0 40 (by norm_num) (targetSellingCumulative h)
    (targetSellingCumulative_monotone h) (targetSellingCumulative_continuous h)

theorem targetBuyingStieltjes_eq (h t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 40) :
    targetBuyingStieltjes h t = targetBuyingCumulative h t :=
  finiteContinuousStieltjesExtension_eq 0 40 (by norm_num) _ _ _ t ht
theorem targetSellingStieltjes_eq (h t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 40) :
    targetSellingStieltjes h t = targetSellingCumulative h t :=
  finiteContinuousStieltjesExtension_eq 0 40 (by norm_num) _ _ _ t ht

def targetIndex (i : Fin 9) : Fin 10 := ⟨i.val, by omega⟩

def certificateEdges (e : Fin 9 × Bool) : PairedEdge (Fin 10) :=
  if e.2 then
    ⟨9, targetIndex e.1, by
      intro he
      have hv := congrArg Fin.val he
      change 9 = e.1.val at hv
      have hi := e.1.isLt
      omega⟩
  else
    ⟨targetIndex e.1, 9, by
      intro he
      have hv := congrArg Fin.val he
      change e.1.val = 9 at hv
      have hi := e.1.isLt
      omega⟩

def directedAmounts (buy sell : ℝ) (e : Fin 9 × Bool) : ℝ := if e.2 then buy else sell

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem certificate_directed_input (buy sell : ℝ) (i : Fin 10) :
    tradingInput (pairedMatrix certificateEdges) (directedAmounts buy sell) i =
      if i.val < 9 then buy - sell else -9 * (buy - sell) := by
  fin_cases i <;>
    norm_num [tradingInput, pairedMatrix, certificateEdges, directedAmounts, targetIndex,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  all_goals norm_num only [Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]
  all_goals simp only [if_true, if_false]
  all_goals ring

def certificateExecution (h : ℝ) : StieltjesPairedExecution certificateEdges where
  cumulative := fun e => if e.2 then targetBuyingStieltjes h else targetSellingStieltjes h

theorem certificateExecution_continuous (h : ℝ) (e : Fin 9 × Bool) :
    Continuous ((certificateExecution h).cumulative e) := by
  have hb : Continuous (targetBuyingStieltjes h) :=
    finiteContinuousStieltjesExtension_continuous 0 40 (by norm_num) _ _ _
  have hs : Continuous (targetSellingStieltjes h) :=
    finiteContinuousStieltjesExtension_continuous 0 40 (by norm_num) _ _ _
  by_cases he : e.2
  · simpa only [certificateExecution, if_pos he] using hb
  · simpa only [certificateExecution, if_neg he] using hs

theorem target_gross_cumulative_difference (h t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 40) :
    targetBuyingCumulative h t - targetSellingCumulative h t =
      ∫ u in (0 : ℝ)..t, actualTargetDollars h u := by
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) 40 := by
    rw [Set.uIcc_of_le ht.1, Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 40)]
    exact fun u hu => ⟨hu.1, hu.2.trans ht.2⟩
  have hb := (actual_target_gross_integrable h).1.mono_set hsub
  have hs := (actual_target_gross_integrable h).2.mono_set hsub
  dsimp [targetBuyingCumulative, targetSellingCumulative]
  rw [← intervalIntegral.integral_sub hb hs]
  apply intervalIntegral.integral_congr
  intro u _
  exact (directed_dollar_controls _).2.2.1

def positiveDollarMajorant (h : ℝ) : ℝ :=
  linearSegmentDollars 1 h (23 / 10) + linearSegmentDollars h h (77 / 5) +
    linearSegmentDollars (179 / 184) (199 / 200) (51 / 25)

theorem positiveDollarMajorant_strictMono : StrictMonoOn positiveDollarMajorant (Set.Ici (1 : ℝ)) := by
  intro x hx y _ hxy
  have hcoef : 0 < (209 / 30 : ℝ) * (y + x) - 947 / 150 := by
    have hxx : 1 ≤ x := hx
    linarith
  have hp := mul_pos (sub_pos.mpr hxy) hcoef
  have he : positiveDollarMajorant y - positiveDollarMajorant x =
      (y - x) * ((209 / 30 : ℝ) * (y + x) - 947 / 150) := by
    dsimp [positiveDollarMajorant, linearSegmentDollars]
    ring
  linarith

theorem positiveDollarMajorant_turnover_margin (h : ℝ)
    (hh : h ∈ Set.Icc (1 : ℝ) plateauUpper) : 18 * positiveDollarMajorant h < 2984 / 1000 := by
  have hu : (1 : ℝ) ≤ plateauUpper := by norm_num [plateauUpper]
  have hm := positiveDollarMajorant_strictMono.monotoneOn hh.1 hu hh.2
  have hp : 18 * positiveDollarMajorant plateauUpper < 2984 / 1000 := by
    norm_num [positiveDollarMajorant, linearSegmentDollars, plateauUpper]
  linarith

def certificateDollarLedger (h t : ℝ) (i : Fin 10) : ℝ :=
  tradingInput (pairedMatrix certificateEdges)
    (fun e => (certificateExecution h).cumulative e t - (certificateExecution h).cumulative e 0) i

theorem certificateDollarLedger_primitive (h s t : ℝ) (i : Fin 10) :
    certificateDollarLedger h t i - certificateDollarLedger h s i =
      tradingInput (pairedMatrix certificateEdges)
        (fun e => (certificateExecution h).cumulative e t -
          (certificateExecution h).cumulative e s) i := by
  unfold certificateDollarLedger tradingInput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem certificateDollarLedger_continuous (h : ℝ) (i : Fin 10) :
    Continuous (fun t => certificateDollarLedger h t i) := by
  unfold certificateDollarLedger tradingInput
  apply continuous_finset_sum
  intro e _
  exact continuous_const.mul ((certificateExecution_continuous h e).sub continuous_const)

theorem certificateDollarLedger_explicit (h t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 40)
    (i : Fin 10) : certificateDollarLedger h t i =
      if i.val < 9 then (∫ u in (0 : ℝ)..t, actualTargetDollars h u)
      else -9 * (∫ u in (0 : ℝ)..t, actualTargetDollars h u) := by
  have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 40 := by norm_num
  have heq : (fun e => (certificateExecution h).cumulative e t -
      (certificateExecution h).cumulative e 0) =
      directedAmounts (targetBuyingCumulative h t) (targetSellingCumulative h t) := by
    funext e
    by_cases hd : e.2
    · simp only [certificateExecution, if_pos hd, directedAmounts,
        targetBuyingStieltjes_eq h t ht, targetBuyingStieltjes_eq h 0 hz]
      simp [targetBuyingCumulative]
    · simp only [certificateExecution, if_neg hd, directedAmounts,
        targetSellingStieltjes_eq h t ht, targetSellingStieltjes_eq h 0 hz]
      simp [targetSellingCumulative]
  rw [certificateDollarLedger, heq, certificate_directed_input,
    target_gross_cumulative_difference h t ht]

theorem certificateDollarLedger_closed (h : ℝ) (hh : plateauPolynomial h = 0) :
    ∀ i : Fin 10, certificateDollarLedger h 40 i = 0 := by
  intro i
  rw [certificateDollarLedger_explicit h 40 (by norm_num) i,
    actual_target_dollar_ledger_closed h hh]
  split_ifs <;> ring

def certificateGrossDollars (buy sell : ℝ) (i : Fin 10) : ℝ :=
  ∑ e, |pairedMatrix certificateEdges i e| * directedAmounts buy sell e

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem certificate_gross_input (buy sell : ℝ) (i : Fin 10) :
    certificateGrossDollars buy sell i =
      if i.val < 9 then buy + sell else 9 * (buy + sell) := by
  fin_cases i <;>
    norm_num [certificateGrossDollars, pairedMatrix, certificateEdges, directedAmounts, targetIndex,
      Fintype.sum_prod_type, Fintype.sum_bool, Fin.sum_univ_succ]
  all_goals norm_num only [Fin.ext_iff, Fin.val_natCast, Fin.coe_ofNat_eq_mod]
  all_goals simp only [if_true, if_false]
  all_goals norm_num
  all_goals ring

theorem certificate_paired_dollars_once (buy sell : ℝ) :
    (∑ e : Fin 9 × Bool, directedAmounts buy sell e) = 9 * (buy + sell) := by
  simp [directedAmounts, Fintype.sum_prod_type, Fintype.sum_bool]
  ring

def certificatePrices (h : ℝ) (Y : ℝ → ℝ) (t : ℝ) (i : Fin 10) : ℝ :=
  if i.val < 9 then targetSchedule h t else Y t

theorem certificate_actual_gross_rate (h : ℝ) (Y : ℝ → ℝ) (t : ℝ) (i : Fin 10) :
    certificateGrossDollars (targetBuyingDollars (actualTargetDollars h t))
      (targetSellingDollars (actualTargetDollars h t)) i / certificatePrices h Y t i =
      if i.val < 9 then |actualTargetDollars h t| / targetSchedule h t
      else 9 * |actualTargetDollars h t| / Y t := by
  rw [certificate_gross_input, (directed_dollar_controls _).2.2.2.1]
  by_cases hi : i.val < 9 <;> simp only [certificatePrices, hi, if_true, if_false]

theorem certificate_actual_paired_turnover_rate (h t : ℝ) :
    (∑ e : Fin 9 × Bool, directedAmounts (targetBuyingDollars (actualTargetDollars h t))
      (targetSellingDollars (actualTargetDollars h t)) e) = 9 * |actualTargetDollars h t| := by
  rw [certificate_paired_dollars_once, (directed_dollar_controls _).2.2.2.1]

/-- A bounded actual flow gives a Lipschitz cumulative on the physical interval.
This will be applied to the checked within-step bounds, rather than postulated
as regularity of an execution input. -/
theorem integral_primitive_lipschitz (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (C : NNReal) (hi : IntervalIntegrable f MeasureTheory.volume a b)
    (hb : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Icc a b → |f t| ≤ C) :
    LipschitzOnWith C (fun t => ∫ u in a..t, f u) (Set.Icc a b) := by
  apply lipschitzOn_of_bounded_primitive _ f a b C _ hb
  intro s hs t ht
  have sub (r : ℝ) (hr : r ∈ Set.Icc a b) :
      IntervalIntegrable f MeasureTheory.volume a r := by
    apply hi.mono_set
    rw [Set.uIcc_of_le hr.1, Set.uIcc_of_le hab]
    exact fun u hu => ⟨hu.1, hu.2.trans hr.2⟩
  exact intervalIntegral.integral_interval_sub_left (sub t ht) (sub s hs)

theorem finiteContinuousStieltjesExtension_lipschitz (a b : ℝ) (hab : a ≤ b)
    (f : ℝ → ℝ) (hm : MonotoneOn f (Set.Icc a b))
    (hc : ContinuousOn f (Set.Icc a b)) (C : NNReal)
    (hl : LipschitzOnWith C f (Set.Icc a b)) :
    LipschitzWith C (finiteContinuousStieltjesExtension a b hab f hm hc) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hp : dist (Set.projIcc a b hab x) (Set.projIcc a b hab y) ≤ dist x y := by
    simpa only [NNReal.coe_one, one_mul] using (LipschitzWith.projIcc hab).dist_le_mul x y
  exact (hl.dist_le_mul _ (Set.projIcc a b hab x).property
    _ (Set.projIcc a b hab y).property).trans (mul_le_mul_of_nonneg_left hp C.coe_nonneg)

/-- Summing outward step budgets bounds the actual integral; no numerical
quadrature value is identified with the physical integral. -/
theorem integral_le_of_step_budgets (T : ℕ → ℝ) (f : ℝ → ℝ)
    (budget : ℕ → ℝ) (N : ℕ)
    (hi : ∀ k < N, IntervalIntegrable f MeasureTheory.volume (T k) (T (k + 1)))
    (hb : ∀ k < N, (∫ t in T k..T (k + 1), f t) ≤ budget (k + 1) - budget k) :
    (∫ t in (T 0)..(T N), f t) ≤ budget N - budget 0 := by
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi]
  have ht : ∀ n : ℕ, (∑ k ∈ Finset.range n, (budget (k + 1) - budget k)) =
      budget n - budget 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ ≤ ∑ k ∈ Finset.range N, (budget (k + 1) - budget k) :=
      Finset.sum_le_sum (fun k hk => hb k (Finset.mem_range.mp hk))
    _ = budget N - budget 0 := ht N

namespace ValidatedBlocks
open RationalInterval RationalInterval.CertificateReplay
open RationalInterval.CertificateReplay.IntegerReplay

theorem block_checks (g : ℕ) (hg : g < 800) :
    IntegerReplay.checkBlock g = true := by
  exact List.all_eq_true.mp IntegerReplay.kernel_all_blocks_valid g (List.mem_range.mpr hg)

theorem block_run_valid (g : ℕ) (hg : g < 800) :
    (IntegerReplay.run (IntegerReplay.segment g) 100 (blockStart g)
      (IntegerReplay.state g)).valid = true := by
  have hc := block_checks g hg
  simp only [IntegerReplay.checkBlock, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact hc.1.1

theorem block_current_valid (g m : ℕ) (hg : g < 800) (hm : m < 100) :
    (IntegerReplay.step (IntegerReplay.segment g) (blockStart g + m)
      (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g)
        (IntegerReplay.state g))).valid = true :=
  IntegerChecks.run_step_valid _ 100 _ _ (block_run_valid g hg) m hm

theorem margin_of_checked_step (s : IntegerReplay.Segment) (j : ℕ)
    (st : IntegerReplay.State) (hv : (IntegerReplay.step s j st).valid = true) :
    (73 / 100 : ℝ) ≤ (IntegerReplay.view st.enclosure).lo ∧
      ((IntegerReplay.view st.enclosure).hi : ℝ) ≤ 157 / 100 := by
  have hb := IntegerChecks.step_valid_old_bounds s j st hv
  have hl : ((73 * IntegerReplay.Q / 100 : Int) : ℝ) < (st.enclosure.lo : ℝ) := by
    exact_mod_cast hb.1
  have hh : (st.enclosure.hi : ℝ) < ((157 * IntegerReplay.Q / 100 : Int) : ℝ) := by
    exact_mod_cast hb.2
  norm_num [IntegerReplay.Q] at hl hh
  norm_num [IntegerReplay.view, grid]
  constructor <;> linarith

/-- The kernel-checked discrete block constructs a genuine positive physical
ODE solution from every actual initial value in its checkpoint box. -/
theorem actual_block_exists_with_mesh (h : ℝ) (hh : Contains plateau h)
    (g : ℕ) (hg : g < 800) (y₀ : ℝ)
    (hy : Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) y₀) :
    let T := fun m : ℕ => (g : ℝ) / 20 + (m : ℝ) / 2000
    let U := affineForcing (WitnessMesh.actualStart h g)
      ((WitnessMesh.actualEnd h g - WitnessMesh.actualStart h g) / WitnessMesh.duration g)
      (WitnessMesh.startTime g)
    ∃ Y : ℝ → ℝ, Y (T 0) = y₀ ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc (T 0) (T 100)) ∧
      (∀ t ∈ Set.Icc (T 0) (T 100), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (T 0) (T 100) →
        HasDerivAt Y (compensatorField (U t) (Y t)) t) ∧
      Contains (IntegerReplay.view (IntegerReplay.state (g + 1)).enclosure) (Y (T 100)) ∧
      (∀ m ≤ 100, Contains (IntegerReplay.view
        (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g)
          (IntegerReplay.state g)).enclosure) (Y (T m))) := by
  let T := fun m : ℕ => (g : ℝ) / 20 + (m : ℝ) / 2000
  let U := affineForcing (WitnessMesh.actualStart h g)
    ((WitnessMesh.actualEnd h g - WitnessMesh.actualStart h g) / WitnessMesh.duration g)
    (WitnessMesh.startTime g)
  let st := fun m => IntegerReplay.run (IntegerReplay.segment g) m (blockStart g)
    (IntegerReplay.state g)
  have hT : StrictMono T := by
    intro m n hmn
    have hr : (m : ℝ) < n := by exact_mod_cast hmn
    dsimp [T]
    linarith
  have hmargin := margin_of_checked_step _ _ _ (block_current_valid g 0 hg (by omega))
  have hstrip : y₀ ∈ Set.Icc (7 / 10 : ℝ) (8 / 5) := by
    simp only [IntegerReplay.run, Nat.add_zero] at hmargin
    constructor <;> linarith [hmargin.1, hmargin.2, hy.1, hy.2]
  have hp := WitnessMesh.parameter_boxes_contain h hh g
  have hc := WitnessMesh.static_piece_checks g
  have hstep : ∀ m < 100, ∀ y : ℝ, Contains (IntegerReplay.view (st m).enclosure) y →
      ∃ W : ℝ → ℝ, W (T m) = y ∧
        LipschitzOnWith (17 / 10 : NNReal) W (Set.Icc (T m) (T (m + 1))) ∧
        (∀ t ∈ Set.Icc (T m) (T (m + 1)), W t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
        (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (T m) (T (m + 1)) →
          HasDerivAt W (compensatorField (U t) (W t)) t) ∧
        Contains (IntegerReplay.view (st (m + 1)).enclosure) (W (T (m + 1))) := by
    intro m hm y hmy
    have hd := ForcingBoxes.prepared_affine_step
      (WitnessMesh.startBox g) (WitnessMesh.endBox g) (WitnessMesh.duration g)
      (WitnessMesh.actualStart h g) (WitnessMesh.actualEnd h g) (WitnessMesh.startTime g)
      y (blockStart g + m) (st m) hc.1 hc.2.1 hp.1 hp.2
      (WitnessMesh.step_within_piece g m hg hm) hc.2.2.1.le hmy
      (margin_of_checked_step _ _ _ (block_current_valid g m hg hm))
    have ha : WitnessMesh.startTime g + ((blockStart g + m : ℕ) : ℝ) / 2000 = T m := by
      rw [WitnessMesh.block_clock]
      simp only [T, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring
    have he : T m + 1 / 2000 = T (m + 1) := by
      simp only [T, Nat.cast_add, Nat.cast_one]
      ring
    dsimp only at hd
    rw [ha, he, WitnessMesh.integer_segment_eq] at hd
    obtain ⟨W, hWa, hWL, hWs, hWd, hWb⟩ := hd
    refine ⟨W, hWa, hWL, hWs, Filter.Eventually.of_forall (fun t ht => ?_), ?_⟩
    · exact (hWd t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    · simpa only [st, IntegerChecks.run_succ_last] using hWb
  obtain ⟨Y, hYa, hYL, hYs, hYd, hYb⟩ := finite_scalar_trajectory T hT
    (fun m => IntegerReplay.view (st m).enclosure)
    (fun t y => compensatorField (U t) y) (17 / 10 : NNReal) (7 / 10) (8 / 5) y₀
    hy hstrip 100 hstep
  refine ⟨Y, hYa, hYL, hYs, hYd, ?_, hYb⟩
  have hf := hYb 100 le_rfl
  have hk := block_checks g hg
  simp only [IntegerReplay.checkBlock, Bool.and_eq_true, decide_eq_true_eq] at hk
  simpa only [st, IntegerReplay.view, hk.1.2, hk.2] using hf

theorem actual_block_exists (h : ℝ) (hh : Contains plateau h)
    (g : ℕ) (hg : g < 800) (y₀ : ℝ)
    (hy : Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) y₀) :
    let T := fun m : ℕ => (g : ℝ) / 20 + (m : ℝ) / 2000
    let U := affineForcing (WitnessMesh.actualStart h g)
      ((WitnessMesh.actualEnd h g - WitnessMesh.actualStart h g) / WitnessMesh.duration g)
      (WitnessMesh.startTime g)
    ∃ Y : ℝ → ℝ, Y (T 0) = y₀ ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc (T 0) (T 100)) ∧
      (∀ t ∈ Set.Icc (T 0) (T 100), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (T 0) (T 100) →
        HasDerivAt Y (compensatorField (U t) (Y t)) t) ∧
      Contains (IntegerReplay.view (IntegerReplay.state (g + 1)).enclosure) (Y (T 100)) := by
  obtain ⟨Y, hYa, hYL, hYs, hYd, hYb, _⟩ :=
    actual_block_exists_with_mesh h hh g hg y₀ hy
  exact ⟨Y, hYa, hYL, hYs, hYd, hYb⟩

set_option maxHeartbeats 2000000 in
theorem block_forcing_eq_actual (h : ℝ) (g : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ioc ((g : ℝ) / 20) (((g + 1 : ℕ) : ℝ) / 20)) :
    affineForcing (WitnessMesh.actualStart h g)
      ((WitnessMesh.actualEnd h g - WitnessMesh.actualStart h g) / WitnessMesh.duration g)
      (WitnessMesh.startTime g) t = actualTargetDollars h t := by
  have h46 : (g < 46) ↔ ((g : ℝ) < 46) := by norm_cast
  have h354 : (g < 354) ↔ ((g : ℝ) < 354) := by norm_cast
  have h400 : (g < 400) ↔ ((g : ℝ) < 400) := by norm_cast
  have h446 : (g < 446) ↔ ((g : ℝ) < 446) := by norm_cast
  have h754 : (g < 754) ↔ ((g : ℝ) < 754) := by norm_cast
  have upper (n : ℕ) (hn : (g : ℝ) < n) : (g : ℝ) + 1 ≤ n := by
    have hnat : g < n := by exact_mod_cast hn
    have hsucc : g + 1 ≤ n := by omega
    exact_mod_cast hsucc
  simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioc] at ht
  unfold WitnessMesh.actualStart WitnessMesh.actualEnd WitnessMesh.duration
    WitnessMesh.startTime WitnessMesh.offset
  simp only [h46, h354, h400, h446, h754]
  unfold actualTargetDollars targetSchedule targetVelocity
  split_ifs
  all_goals try have hg46 := upper 46 (by assumption)
  all_goals try have hg354 := upper 354 (by assumption)
  all_goals try have hg400 := upper 400 (by assumption)
  all_goals try have hg446 := upper 446 (by assumption)
  all_goals try have hg754 := upper 754 (by assumption)
  all_goals norm_num only [Nat.cast_ofNat] at *
  all_goals try (exfalso; linarith [ht.1, ht.2])
  all_goals norm_num [affineForcing, targetLine] <;> ring

set_option maxHeartbeats 2000000 in
theorem block_price_eq_actual (h : ℝ) (g : ℕ) (t : ℝ)
    (ht : t ∈ Set.Ioc ((g : ℝ) / 20) (((g + 1 : ℕ) : ℝ) / 20)) :
    WitnessMesh.actualStart h g +
      ((WitnessMesh.actualEnd h g - WitnessMesh.actualStart h g) / WitnessMesh.duration g) *
        (t - WitnessMesh.startTime g) = targetSchedule h t := by
  have h46 : (g < 46) ↔ ((g : ℝ) < 46) := by norm_cast
  have h354 : (g < 354) ↔ ((g : ℝ) < 354) := by norm_cast
  have h400 : (g < 400) ↔ ((g : ℝ) < 400) := by norm_cast
  have h446 : (g < 446) ↔ ((g : ℝ) < 446) := by norm_cast
  have h754 : (g < 754) ↔ ((g : ℝ) < 754) := by norm_cast
  have upper (n : ℕ) (hn : (g : ℝ) < n) : (g : ℝ) + 1 ≤ n := by
    have hnat : g < n := by exact_mod_cast hn
    have hsucc : g + 1 ≤ n := by omega
    exact_mod_cast hsucc
  simp only [Nat.cast_add, Nat.cast_one, Set.mem_Ioc] at ht
  unfold WitnessMesh.actualStart WitnessMesh.actualEnd WitnessMesh.duration
    WitnessMesh.startTime WitnessMesh.offset
  simp only [h46, h354, h400, h446, h754]
  unfold targetSchedule
  split_ifs
  all_goals try have hg46 := upper 46 (by assumption)
  all_goals try have hg354 := upper 354 (by assumption)
  all_goals try have hg400 := upper 400 (by assumption)
  all_goals try have hg446 := upper 446 (by assumption)
  all_goals try have hg754 := upper 754 (by assumption)
  all_goals norm_num only [Nat.cast_ofNat] at *
  all_goals try (exfalso; linarith [ht.1, ht.2])
  all_goals norm_num [targetLine] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem actual_compensator_exists (h : ℝ) (hh : Contains plateau h) :
    ∃ Y : ℝ → ℝ, Y 0 = 1 ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc (0 : ℝ) 40) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 40, Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 40 →
        HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t) ∧
      (∀ g ≤ 800, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure)
        (Y ((g : ℝ) / 20))) := by
  let T := fun g : ℕ => (g : ℝ) / 20
  have hT : StrictMono T := by
    intro m n hmn
    exact div_lt_div_of_pos_right (by exact_mod_cast hmn) (by norm_num)
  have hinit : Contains (IntegerReplay.view (IntegerReplay.state 0).enclosure) (1 : ℝ) := by
    norm_num [Contains, IntegerReplay.view, IntegerReplay.state, replayCheckpoints, grid]
  have hs : (1 : ℝ) ∈ Set.Icc (7 / 10 : ℝ) (8 / 5) := by norm_num
  have hstep : ∀ g < 800, ∀ y : ℝ,
      Contains (IntegerReplay.view (IntegerReplay.state g).enclosure) y →
      ∃ W : ℝ → ℝ, W (T g) = y ∧
        LipschitzOnWith (17 / 10 : NNReal) W (Set.Icc (T g) (T (g + 1))) ∧
        (∀ t ∈ Set.Icc (T g) (T (g + 1)), W t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
        (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (T g) (T (g + 1)) →
          HasDerivAt W (compensatorField (actualTargetDollars h t) (W t)) t) ∧
        Contains (IntegerReplay.view (IntegerReplay.state (g + 1)).enclosure)
          (W (T (g + 1))) := by
    intro g hg y hy
    have hb := actual_block_exists h hh g hg y hy
    dsimp only at hb
    have he : (g : ℝ) / 20 + ((100 : ℕ) : ℝ) / 2000 = T (g + 1) := by
      simp only [T, Nat.cast_add, Nat.cast_one]
      ring
    simp only [Nat.cast_zero, zero_div, add_zero] at hb
    rw [he] at hb
    obtain ⟨W, hWa, hWL, hWs, hWd, hWb⟩ := hb
    refine ⟨W, hWa, hWL, hWs, ?_, hWb⟩
    filter_upwards [hWd] with t hdt ht
    have heq := block_forcing_eq_actual h g t ⟨ht.1, ht.2.le⟩
    simpa only [heq] using hdt ht
  have hhyp := finite_scalar_trajectory T hT
    (fun g => IntegerReplay.view (IntegerReplay.state g).enclosure)
    (fun t y => compensatorField (actualTargetDollars h t) y)
    (17 / 10 : NNReal) (7 / 10) (8 / 5) 1 hinit hs 800 hstep
  norm_num only [T, Nat.cast_zero, zero_div, Nat.cast_ofNat, show (800 : ℝ) / 20 = 40 by norm_num] at hhyp
  exact hhyp

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem actual_compensator_exists_with_mesh (h : ℝ) (hh : Contains plateau h) :
    ∀ N : ℕ, N ≤ 800 → ∃ Y : ℝ → ℝ, Y 0 = 1 ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc 0 ((N : ℝ) / 20)) ∧
      (∀ t ∈ Set.Icc 0 ((N : ℝ) / 20), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo 0 ((N : ℝ) / 20) →
        HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t) ∧
      (∀ g ≤ N, Contains (IntegerReplay.view (IntegerReplay.state g).enclosure)
        (Y ((g : ℝ) / 20))) ∧
      (∀ g < N, ∀ m ≤ 100, Contains (IntegerReplay.view
        (IntegerReplay.run (IntegerReplay.segment g) m (blockStart g)
          (IntegerReplay.state g)).enclosure) (Y ((g : ℝ) / 20 + (m : ℝ) / 2000))) := by
  have hi : Contains (IntegerReplay.view (IntegerReplay.state 0).enclosure) (1 : ℝ) := by
    norm_num [Contains, IntegerReplay.view, IntegerReplay.state, replayCheckpoints, grid]
  intro N
  induction N with
  | zero =>
    intro _
    refine ⟨fun _ => 1, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      simp only [dist_self]
      exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg
    · intro t ht; norm_num
    · filter_upwards [] with t ht
      have hlt : t < 0 := by simpa using ht.2
      linarith [ht.1]
    · intro g hg
      have he : g = 0 := Nat.eq_zero_of_le_zero hg
      subst g
      exact hi
    · intro g hg; omega
  | succ n ih =>
    intro hn
    obtain ⟨Y, hYa, hYL, hYs, hYd, hYb, hYm⟩ := ih (by omega)
    have hng : n < 800 := by omega
    have hw := actual_block_exists_with_mesh h hh n hng (Y ((n : ℝ) / 20)) (hYb n le_rfl)
    dsimp only at hw
    have he : (n : ℝ) / 20 + ((100 : ℕ) : ℝ) / 2000 = ((n + 1 : ℕ) : ℝ) / 20 := by
      push_cast
      ring
    simp only [Nat.cast_zero, zero_div, add_zero] at hw
    rw [he] at hw
    obtain ⟨W, hWa, hWL, hWs, hWd, hWb, hWm⟩ := hw
    have hWd' : ∀ᵐ t ∂MeasureTheory.volume,
        t ∈ Set.Ioo ((n : ℝ) / 20) (((n + 1 : ℕ) : ℝ) / 20) →
        HasDerivAt W (compensatorField (actualTargetDollars h t) (W t)) t := by
      filter_upwards [hWd] with t hd ht
      simpa only [block_forcing_eq_actual h n t ⟨ht.1, ht.2.le⟩] using hd ht
    have hn0 : (0 : ℝ) ≤ (n : ℝ) / 20 := div_nonneg (Nat.cast_nonneg n) (by norm_num)
    have hnn : (n : ℝ) / 20 < ((n + 1 : ℕ) : ℝ) / 20 := by
      push_cast
      linarith
    let Z := joinSolutions Y W ((n : ℝ) / 20)
    have zY (t : ℝ) (ht : t ≤ (n : ℝ) / 20) : Z t = Y t := by
      simp only [Z, joinSolutions, if_pos ht]
    have zW (t : ℝ) (ht : (n : ℝ) / 20 ≤ t) : Z t = W t := by
      dsimp [Z, joinSolutions]
      split_ifs with ht'
      · have heq : t = (n : ℝ) / 20 := le_antisymm ht' ht
        subst t
        exact hWa.symm
      · rfl
    refine ⟨Z, (zY 0 hn0).trans hYa,
      joinSolutions_lipschitz Y W 0 ((n : ℝ) / 20) (((n + 1 : ℕ) : ℝ) / 20)
        (17 / 10 : NNReal) hn0 hnn.le hYL hWL hWa.symm, ?_,
      joinSolutions_ae_ode Y W (fun t y => compensatorField (actualTargetDollars h t) y)
        0 ((n : ℝ) / 20) (((n + 1 : ℕ) : ℝ) / 20) hYd hWd', ?_, ?_⟩
    · intro t ht
      by_cases htn : t ≤ (n : ℝ) / 20
      · rw [zY t htn]; exact hYs t ⟨ht.1, htn⟩
      · rw [zW t (le_of_not_ge htn)]; exact hWs t ⟨le_of_not_ge htn, ht.2⟩
    · intro g hg
      by_cases hgn : g ≤ n
      · have hgt : (g : ℝ) / 20 ≤ (n : ℝ) / 20 :=
          div_le_div_of_nonneg_right (by exact_mod_cast hgn) (by norm_num)
        rw [zY _ hgt]; exact hYb g hgn
      · have heq : g = n + 1 := by omega
        subst g
        rw [zW _ hnn.le]
        exact hWb
    · intro g hg m hm
      by_cases hgn : g < n
      · have hgn' : (g : ℝ) + 1 ≤ n := by exact_mod_cast (show g + 1 ≤ n by omega)
        have hm' : (m : ℝ) ≤ 100 := by exact_mod_cast hm
        have htime : (g : ℝ) / 20 + (m : ℝ) / 2000 ≤ (n : ℝ) / 20 := by linarith
        rw [zY _ htime]
        exact hYm g hgn m hm
      · have heq : g = n := by omega
        subst g
        have htime : (n : ℝ) / 20 ≤ (n : ℝ) / 20 + (m : ℝ) / 2000 :=
          le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg m) (by norm_num))
        rw [zW _ htime]
        exact hWm m hm

end ValidatedBlocks

namespace ResourceSoundness
open Set
open RationalInterval RationalInterval.CertificateReplay
open RationalInterval.CertificateReplay.IntegerReplay
open ResourceCertificate

theorem integer_state_ext (x y : IntegerReplay.State)
    (hl : x.enclosure.lo = y.enclosure.lo) (hh : x.enclosure.hi = y.enclosure.hi)
    (hv : x.valid = y.valid) : x = y := by
  rcases x with ⟨⟨xl, xh⟩, xv⟩
  rcases y with ⟨⟨yl, yh⟩, yv⟩
  simp_all

theorem checked_step (k : ℕ) (hk : checkRow k = true) :
    IntegerReplay.step (IntegerReplay.segment (k / 100)) (localIndex k) (stateAt k) =
      stateAt (k + 1) := by
  have hc := hk
  simp [checkRow, Id.run] at hc
  have he : (estimate k).nextState =
      IntegerReplay.step (IntegerReplay.segment (k / 100)) (localIndex k) (stateAt k) := rfl
  apply integer_state_ext
  · have hl : (estimate k).nextState.enclosure.lo = (rowAt (k + 1)).lo := by tauto
    simpa only [he, stateAt] using hl
  · have hh : (estimate k).nextState.enclosure.hi = (rowAt (k + 1)).hi := by tauto
    simpa only [he, stateAt] using hh
  · have hv : (estimate k).nextState.valid = true := by tauto
    simpa only [he, stateAt] using hv

theorem row_run (hrows : ∀ k < 80000, checkRow k = true)
    (g : ℕ) (hg : g < 800) (m : ℕ) (hm : m ≤ 100) :
    IntegerReplay.run (IntegerReplay.segment g) m (blockStart g) (stateAt (100 * g)) =
      stateAt (100 * g + m) := by
  induction m with
  | zero => simp only [IntegerReplay.run, Nat.add_zero]
  | succ m ih =>
    have hmlt : m < 100 := by omega
    rw [IntegerChecks.run_succ_last, ih (by omega)]
    have hd : (100 * g + m) / 100 = g := by omega
    have hi : localIndex (100 * g + m) = blockStart g + m := by
      unfold localIndex
      rw [hd]
      have he : (100 * g + m) % 100 = m := by omega
      rw [he]
    have hs := checked_step (100 * g + m) (hrows _ (by omega))
    simpa only [hd, hi, Nat.add_assoc] using hs

theorem old_block_endpoint (g : ℕ) (hg : g < 800) :
    IntegerReplay.run (IntegerReplay.segment g) 100 (blockStart g) (IntegerReplay.state g) =
      IntegerReplay.state (g + 1) := by
  have hc := ValidatedBlocks.block_checks g hg
  simp only [IntegerReplay.checkBlock, Bool.and_eq_true, decide_eq_true_eq] at hc
  exact integer_state_ext _ _ hc.1.2 hc.2 hc.1.1

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem row_checkpoint (hrows : ∀ k < 80000, checkRow k = true) :
    ∀ g : ℕ, g ≤ 800 → stateAt (100 * g) = IntegerReplay.state g := by
  intro g
  induction g with
  | zero =>
    intro _
    apply integer_state_ext
    · norm_num [stateAt, rowAt, initialRow, IntegerReplay.state, replayCheckpoints, IntegerReplay.Q]
    · norm_num [stateAt, rowAt, initialRow, IntegerReplay.state, replayCheckpoints, IntegerReplay.Q]
    · rfl
  | succ g ih =>
    intro hg
    have hgl : g < 800 := by omega
    have hr := row_run hrows g hgl 100 le_rfl
    rw [ih (by omega), old_block_endpoint g hgl] at hr
    simpa only [Nat.mul_add, Nat.mul_one] using hr.symm

theorem row_microstate (hrows : ∀ k < 80000, checkRow k = true)
    (g : ℕ) (hg : g < 800) (m : ℕ) (hm : m ≤ 100) :
    stateAt (100 * g + m) = IntegerReplay.run (IntegerReplay.segment g) m
      (blockStart g) (IntegerReplay.state g) := by
  have hr := row_run hrows g hg m hm
  rw [row_checkpoint hrows g hg.le] at hr
  exact hr.symm

set_option maxHeartbeats 1000000 in
theorem actual_compensator_exists_with_rows
    (hrows : ∀ k < 80000, checkRow k = true) (h : ℝ) (hh : Contains plateau h) :
    ∃ Y : ℝ → ℝ, Y 0 = 1 ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Icc (0 : ℝ) 40) ∧
      (∀ t ∈ Icc (0 : ℝ) 40, Y t ∈ Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ᵐ t ∂MeasureTheory.volume, t ∈ Ioo (0 : ℝ) 40 →
        HasDerivAt Y (compensatorField (actualTargetDollars h t) (Y t)) t) ∧
      (∀ k ≤ 80000, Contains (IntegerReplay.view (stateAt k).enclosure)
        (Y ((k : ℝ) / 2000))) := by
  obtain ⟨Y, hY0, hYL, hYs, hYd, hYb, hYm⟩ :=
    ValidatedBlocks.actual_compensator_exists_with_mesh h hh 800 le_rfl
  have h40 : ((800 : ℕ) : ℝ) / 20 = 40 := by norm_num
  rw [h40] at hYL hYs hYd
  refine ⟨Y, hY0, hYL, hYs, hYd, ?_⟩
  intro k hk
  by_cases hklt : k < 80000
  · let g := k / 100
    let m := k % 100
    have hg : g < 800 := by dsimp [g]; omega
    have hm : m ≤ 100 := by dsimp [m]; omega
    have he : 100 * g + m = k := by dsimp [g, m]; omega
    have ht : (g : ℝ) / 20 + (m : ℝ) / 2000 = (k : ℝ) / 2000 := by
      have hcast : (100 : ℝ) * g + m = k := by exact_mod_cast he
      linarith
    have hb := hYm g hg m hm
    rw [← row_microstate hrows g hg m hm] at hb
    simpa only [he, ht] using hb
  · have he : k = 80000 := by omega
    subst k
    have hb := hYb 800 le_rfl
    rw [row_checkpoint hrows 800 le_rfl]
    convert hb using 1 <;> norm_num

def scaledInt (n : Int) : ℝ := (n : ℝ) / (10 : ℝ) ^ 32

theorem scaledInt_mono : Monotone scaledInt := by
  intro m n hmn
  exact div_le_div_of_nonneg_right (by exact_mod_cast hmn) (by positivity)

@[simp] theorem view_lo_scaled (I : IntegerReplay.Interval) :
    ((IntegerReplay.view I).lo : ℝ) = scaledInt I.lo := by
  norm_num [IntegerReplay.view, grid, scaledInt]

@[simp] theorem view_hi_scaled (I : IntegerReplay.Interval) :
    ((IntegerReplay.view I).hi : ℝ) = scaledInt I.hi := by
  norm_num [IntegerReplay.view, grid, scaledInt]

theorem scaledInt_add (m n : Int) : scaledInt (m + n) = scaledInt m + scaledInt n := by
  simp only [scaledInt, Int.cast_add, add_div]

theorem scaledInt_sub (m n : Int) : scaledInt (m - n) = scaledInt m - scaledInt n := by
  simp only [scaledInt, Int.cast_sub, sub_div]

theorem scaledInt_floor_half (n : Int) : scaledInt (n / 2) ≤ scaledInt n / 2 := by
  have hq : ((n / 2 : Int) : ℚ) ≤ (n : ℚ) / 2 := by
    rw [← IntegerReplay.floor_int_div_int n 2 (by norm_num)]
    exact Int.floor_le _
  have hr : ((n / 2 : Int) : ℝ) ≤ (n : ℝ) / 2 := by exact_mod_cast hq
  have hh := div_le_div_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ 10 ^ 32)
  convert hh using 1 <;> dsimp [scaledInt] <;> ring

theorem scaledInt_ceil_half (n : Int) : scaledInt n / 2 ≤ scaledInt (IntegerReplay.ceilDiv n 2) := by
  have hq : (n : ℚ) / 2 ≤ ((IntegerReplay.ceilDiv n 2 : Int) : ℚ) := by
    rw [← IntegerReplay.ceil_int_div_int n 2 (by norm_num)]
    exact Int.le_ceil _
  have hr : (n : ℝ) / 2 ≤ ((IntegerReplay.ceilDiv n 2 : Int) : ℝ) := by exact_mod_cast hq
  have hh := div_le_div_of_nonneg_right hr (by positivity : (0 : ℝ) ≤ 10 ^ 32)
  convert hh using 1 <;> dsimp [scaledInt] <;> ring

def roundedEndpointBox (A B : IntegerReplay.Interval) (motion : Int) : IntegerReplay.Interval :=
  ⟨(A.lo + B.lo - motion) / 2, IntegerReplay.ceilDiv (A.hi + B.hi + motion) 2⟩

theorem roundedEndpointBox_lower (A B : IntegerReplay.Interval) (motion : Int) :
    scaledInt (roundedEndpointBox A B motion).lo ≤
      (scaledInt A.lo + scaledInt B.lo - scaledInt motion) / 2 := by
  simpa only [roundedEndpointBox, scaledInt_sub, scaledInt_add] using
    scaledInt_floor_half (A.lo + B.lo - motion)

theorem roundedEndpointBox_upper (A B : IntegerReplay.Interval) (motion : Int) :
    (scaledInt A.hi + scaledInt B.hi + scaledInt motion) / 2 ≤
      scaledInt (roundedEndpointBox A B motion).hi := by
  simpa only [roundedEndpointBox, scaledInt_add] using
    scaledInt_ceil_half (A.hi + B.hi + motion)

theorem roundedEndpointBox_sound (Y : ℝ → ℝ) (a b : ℝ) (A B : IntegerReplay.Interval)
    (L : NNReal) (motion : Int) (hab : a ≤ b) (hYL : LipschitzOnWith L Y (Icc a b))
    (ha : Contains (IntegerReplay.view A) (Y a)) (hb : Contains (IntegerReplay.view B) (Y b))
    (hmotion : L * (b - a) ≤ scaledInt motion) :
    ∀ t ∈ Icc a b, Contains (IntegerReplay.view (roundedEndpointBox A B motion)) (Y t) := by
  have ha' : Y a ∈ Icc (scaledInt A.lo) (scaledInt A.hi) := by
    simpa only [Contains, view_lo_scaled, view_hi_scaled] using ha
  have hb' : Y b ∈ Icc (scaledInt B.lo) (scaledInt B.hi) := by
    simpa only [Contains, view_lo_scaled, view_hi_scaled] using hb
  have hc := certificateBootstrap_uniform_box hab hYL ha' hb'
  intro t ht
  have hh := hc t ht
  have hl := roundedEndpointBox_lower A B motion
  have hu := roundedEndpointBox_upper A B motion
  simp only [Contains, view_lo_scaled, view_hi_scaled]
  constructor <;> linarith [hh.1, hh.2]

def compensatorInterval (U P : IntegerReplay.Interval) : IntegerReplay.Interval :=
  IntegerReplay.minus
    (IntegerReplay.negate (IntegerReplay.multiply (IntegerReplay.lit (2 / 5))
      (IntegerReplay.minus P (IntegerReplay.lit 1))))
    (IntegerReplay.quotient (IntegerReplay.multiply (IntegerReplay.lit 9) U) P)

theorem compensatorInterval_sound {U P : IntegerReplay.Interval} {u y : ℝ}
    (hl : 0 < P.lo) (hh : 0 ≤ P.hi)
    (hu : Contains (IntegerReplay.view U) u) (hy : Contains (IntegerReplay.view P) y) :
    Contains (IntegerReplay.view (compensatorInterval U P)) (compensatorField u y) := by
  have hr := IntegerReplay.negate_sound (IntegerReplay.multiply_sound (IntegerReplay.lit_sound (2 / 5))
    (IntegerReplay.minus_sound hy (IntegerReplay.lit_sound 1)))
  have ht := IntegerReplay.quotient_sound hl hh
    (IntegerReplay.multiply_sound (IntegerReplay.lit_sound 9) hu) hy
  simpa only [compensatorInterval, compensatorField, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_one, neg_mul] using
    IntegerReplay.minus_sound hr ht

theorem interval_abs_bound {I : IntegerReplay.Interval} {x : ℝ}
    (hx : Contains (IntegerReplay.view I) x) :
    |x| ≤ scaledInt (max |I.lo| |I.hi|) := by
  let M := max |I.lo| |I.hi|
  have hl : -M ≤ I.lo :=
    (neg_le_neg (le_max_left |I.lo| |I.hi|)).trans (neg_abs_le I.lo)
  have hh : I.hi ≤ M := (le_abs_self I.hi).trans (le_max_right |I.lo| |I.hi|)
  have hlr := scaledInt_mono hl
  have hhr := scaledInt_mono hh
  have hn : scaledInt (-M) = -scaledInt M := by simp only [scaledInt, Int.cast_neg, neg_div]
  rw [hn] at hlr
  simp only [Contains, view_lo_scaled, view_hi_scaled] at hx
  rw [abs_le]
  exact ⟨hlr.trans hx.1, hx.2.trans hhr⟩

def intervalMagnitude (I : IntegerReplay.Interval) : NNReal :=
  ⟨scaledInt (max |I.lo| |I.hi|), by
    have hm : (0 : Int) ≤ max |I.lo| |I.hi| := (abs_nonneg I.lo).trans (le_max_left _ _)
    simpa only [scaledInt, Int.cast_zero, zero_div] using scaledInt_mono hm⟩

theorem affine_integer_hull_contains (I J : IntegerReplay.Interval)
    (x₀ v t₀ a b t : ℝ)
    (ha : Contains (IntegerReplay.view I) (x₀ + v * (a - t₀)))
    (hb : Contains (IntegerReplay.view J) (x₀ + v * (b - t₀)))
    (ht : t ∈ Icc a b) :
    Contains (IntegerReplay.view ⟨min I.lo J.lo, max I.hi J.hi⟩) (x₀ + v * (t - t₀)) := by
  have hli := scaledInt_mono (min_le_left I.lo J.lo)
  have hlj := scaledInt_mono (min_le_right I.lo J.lo)
  have hui := scaledInt_mono (le_max_left I.hi J.hi)
  have huj := scaledInt_mono (le_max_right I.hi J.hi)
  simp only [Contains, view_lo_scaled, view_hi_scaled] at ha hb ⊢
  by_cases hv : 0 ≤ v
  · constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2, ht.1, ht.2]
  · have hv' : v ≤ 0 := le_of_not_ge hv
    constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2, ht.1, ht.2]

theorem interval_intersection_sound {I J : IntegerReplay.Interval} {x : ℝ}
    (hi : Contains (IntegerReplay.view I) x) (hj : Contains (IntegerReplay.view J) x) :
    Contains (IntegerReplay.view ⟨max I.lo J.lo, min I.hi J.hi⟩) x := by
  simp only [Contains, view_lo_scaled, view_hi_scaled] at hi hj ⊢
  constructor
  · by_cases h : I.lo ≤ J.lo
    · simpa only [max_eq_right h] using hj.1
    · simpa only [max_eq_left (le_of_not_ge h)] using hi.1
  · by_cases h : I.hi ≤ J.hi
    · simpa only [min_eq_left h] using hi.2
    · simpa only [min_eq_right (le_of_not_ge h)] using hj.2

end ResourceSoundness

end OriginalCertificate
end MarketCrash
