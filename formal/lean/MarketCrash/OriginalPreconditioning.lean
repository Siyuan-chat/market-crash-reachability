import MarketCrash.PhysicalBVNormalForm
import MarketCrash.OriginalVisitedPrices
import MarketCrash.ResponseFamilies

noncomputable section
namespace MarketCrash
open Set MeasureTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}
variable {F rho : ι → ℝ} {response : ι → Response}
variable {s mid t : PhysicalMarketState ι}

/-- Physical-time recovery, with zero contribution from every instantaneous pulse. -/
def OriginalPhysicalStep.recoveryIntegral
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : ℝ :=
  match step with
  | .continuous m _ _ _ _ => ∫ u in m.a..m.b,
      m.prices u i * (m.prices u i - F i) / (response i).impact (m.prices u i)
  | .pulse _ _ _ _ => 0

/-- Lebesgue trading-time measure, never pulse-parameter measure. -/
def OriginalPhysicalStep.aboveBenchmarkMeasure
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : ENNReal :=
  match step with
  | .continuous m _ _ _ _ => volume {u | u ∈ Ioc m.a m.b ∧ F i < m.prices u i}
  | .pulse _ _ _ _ => 0

def OriginalPhysicalReachable.recoveryIntegral {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ι → ℝ
  | _, .refl _, _ => 0
  | _, .append previous step, i => previous.recoveryIntegral i + step.recoveryIntegral i

def OriginalPhysicalReachable.aboveBenchmarkMeasure {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ι → ENNReal
  | _, .refl _, _ => 0
  | _, .append previous step, i => previous.aboveBenchmarkMeasure i + step.aboveBenchmarkMeasure i

theorem OriginalPhysicalStep.recovery_normal_form
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) :
    coordinate (F i) (response i).impact (t.prices i) -
      coordinate (F i) (response i).impact (s.prices i) =
      t.dollars i - s.dollars i - rho i * step.recoveryIntegral i := by
  cases step with
  | continuous m hF hr hg _ =>
    have hh := m.normal_form m.b ⟨m.time_order, le_rfl⟩ i
    have hl := m.marginal_dollar_primitive i m.a ⟨le_rfl, m.time_order⟩ m.b ⟨m.time_order, le_rfl⟩
    simp only [hF, hr, hg] at hh
    change coordinate (F i) (response i).impact (m.prices m.b i) -
      coordinate (F i) (response i).impact (m.prices m.a i) = _
    dsimp [OriginalPhysicalStep.recoveryIntegral]
    linarith
  | pulse p hF hg _ =>
    have hc := p.coordinate_endpoint i
    have hl := p.ledger_endpoint i
    simp only [hF, hg] at hc
    dsimp [OriginalPhysicalStep.recoveryIntegral]
    linarith

theorem OriginalPhysicalReachable.recovery_normal_form
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    coordinate (F i) (response i).impact (t.prices i) -
      coordinate (F i) (response i).impact (s.prices i) =
      t.dollars i - s.dollars i - rho i * trace.recoveryIntegral i := by
  induction trace with
  | refl => simp [OriginalPhysicalReachable.recoveryIntegral]
  | append previous step ih =>
    have hh := step.recovery_normal_form i
    dsimp [OriginalPhysicalReachable.recoveryIntegral]
    linarith

theorem OriginalPhysicalStep.recovery_nonpositive_of_zero_excursion
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι)
    (hzero : step.aboveBenchmarkMeasure i = 0) : step.recoveryIntegral i ≤ 0 := by
  cases step with
  | continuous m _ _ _ _ =>
    have hz : ∀ᵐ u ∂volume, u ∉ {u | u ∈ Ioc m.a m.b ∧ F i < m.prices u i} :=
      measure_zero_iff_ae_nmem.mp hzero
    dsimp [OriginalPhysicalStep.recoveryIntegral]
    rw [intervalIntegral.integral_of_le m.time_order]
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_of_ae hz, ae_restrict_mem measurableSet_Ioc] with u hu hm
    have hb : m.prices u i ≤ F i := le_of_not_gt (fun hh => hu ⟨hm, hh⟩)
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (m.positive_prices u ⟨hm.1.le, hm.2⟩ i).le (sub_nonpos.mpr hb))
      ((response i).positive _ (m.positive_prices u ⟨hm.1.le, hm.2⟩ i)).le
  | pulse => exact le_rfl

theorem OriginalPhysicalReachable.recovery_nonpositive_of_zero_excursion
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι)
    (hzero : trace.aboveBenchmarkMeasure i = 0) : trace.recoveryIntegral i ≤ 0 := by
  induction trace with
  | refl => exact le_rfl
  | append previous step ih =>
    have hz : previous.aboveBenchmarkMeasure i = 0 ∧ step.aboveBenchmarkMeasure i = 0 :=
      add_eq_zero.mp hzero
    exact add_nonpos (ih hz.1) (step.recovery_nonpositive_of_zero_excursion i hz.2)

theorem integral_required_eq_neg_coordinate (F S : ℝ) (g : Response) :
    (∫ u in S..F, u / g.impact u) = -coordinate F g.impact S := by
  unfold coordinate
  exact intervalIntegral.integral_symm F S

/-- First clause of Proposition 7.4 for the actual complete physical trace. -/
theorem proposition_7_4_original_excursion
    (p : OriginalAdmissiblePhysicalPath F rho response edges) (i : ι)
    (hfinal : p.terminal.prices i < F i) :
    rho i * p.trace.recoveryIntegral i =
      (∫ u in p.terminal.prices i..F i, u / (response i).impact u) ∧
    0 < (∫ u in p.terminal.prices i..F i, u / (response i).impact u) ∧
    0 < p.trace.aboveBenchmarkMeasure i := by
  have hpos := p.endpoint_conditions.2.1 i
  have hc : coordinate (F i) (response i).impact (p.terminal.prices i) < 0 := by
    have hh := coordinate_strictMonoOn (F i) (response i) (p.benchmark_positive i)
      hpos (p.benchmark_positive i) hfinal
    simpa only [coordinate_at_benchmark] using hh
  have hn := p.trace.recovery_normal_form i
  rw [p.initial_prices i, coordinate_at_benchmark, p.initial_dollars i, p.terminal_dollars i] at hn
  have he : rho i * p.trace.recoveryIntegral i =
      (∫ u in p.terminal.prices i..F i, u / (response i).impact u) := by
    rw [integral_required_eq_neg_coordinate]
    linarith
  have hcost : 0 < (∫ u in p.terminal.prices i..F i, u / (response i).impact u) := by
    rw [integral_required_eq_neg_coordinate]
    linarith
  refine ⟨he, hcost, ?_⟩
  apply bot_lt_iff_ne_bot.mpr
  intro hz
  have hrec := p.trace.recovery_nonpositive_of_zero_excursion i hz
  have hh := mul_nonpos_of_nonneg_of_nonpos (p.resilience_nonnegative i) hrec
  rw [he] at hh
  linarith

theorem OriginalPhysicalReachable.recovery_upper_of_visited
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) (C : ℝ)
    (hbound : ∀ x, trace.Visited i x → x * (x - F i) / (response i).impact x ≤ C) :
    trace.recoveryIntegral i ≤ (t.time - s.time) * C := by
  induction trace with
  | refl => simp [OriginalPhysicalReachable.recoveryIntegral]
  | @append mid t previous step ih =>
    have hp := ih (fun x hx => hbound x (Or.inl hx))
    have hs : step.recoveryIntegral i ≤ (t.time - mid.time) * C := by
      cases step with
      | continuous m hF hr hg _ =>
        dsimp [OriginalPhysicalStep.recoveryIntegral]
        have hi : IntervalIntegrable
            (fun u => m.prices u i * (m.prices u i - F i) / (response i).impact (m.prices u i))
            volume m.a m.b := by
          have hh : IntervalIntegrable (fun u => m.prices u i * (m.prices u i - m.F i) /
              (m.response i).impact (m.prices u i)) volume m.a m.b :=
            ((m.recovery_integrand_continuous i).mono (by rw [uIcc_of_le m.time_order])).intervalIntegrable
          simpa only [hF, hg] using hh
        have hh := intervalIntegral.integral_mono_on m.time_order hi
          (intervalIntegrable_const (c := C)) (fun u hu => hbound _ (Or.inr ⟨u, hu, rfl⟩))
        simpa only [intervalIntegral.integral_const, smul_eq_mul] using hh
      | pulse => simp [OriginalPhysicalStep.recoveryIntegral]
    change previous.recoveryIntegral i + step.recoveryIntegral i ≤ _
    linarith

def recoveryCeiling (F U : ℝ) (g : Response) : ℝ :=
  sSup ((fun x => x * (x - F) / g.impact x) '' Icc F U)

theorem recovery_on_benchmark_interval_continuous (F U : ℝ) (g : Response) (hF : 0 < F) :
    ContinuousOn (fun x => x * (x - F) / g.impact x) (Icc F U) := by
  exact (continuousOn_id.mul (continuousOn_id.sub continuousOn_const)).div
    (g.continuousOn_positive.mono (fun _ hx => hF.trans_le hx.1))
    (fun x hx => (g.positive x (hF.trans_le hx.1)).ne')

theorem recoveryCeiling_properties (F U : ℝ) (g : Response) (hF : 0 < F) (hU : F ≤ U) :
    0 ≤ recoveryCeiling F U g ∧
    (∀ x, 0 < x → x ≤ U → x * (x - F) / g.impact x ≤ recoveryCeiling F U g) ∧
    ∃ x ∈ Icc F U, recoveryCeiling F U g = x * (x - F) / g.impact x := by
  have hc := recovery_on_benchmark_interval_continuous F U g hF
  have hb := isCompact_Icc.bddAbove_image hc
  have hmem : F ∈ Icc F U := ⟨le_rfl, hU⟩
  have hn : 0 ≤ recoveryCeiling F U g := by
    have hh := le_csSup hb (mem_image_of_mem (fun x => x * (x - F) / g.impact x) hmem)
    simpa only [sub_self, mul_zero, zero_div] using hh
  refine ⟨hn, ?_, ?_⟩
  · intro x hx hxU
    by_cases hxF : F ≤ x
    · exact le_csSup hb (mem_image_of_mem _ ⟨hxF, hxU⟩)
    · exact (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hx.le (sub_nonpos.mpr (le_of_not_ge hxF)))
        (g.positive x hx).le).trans hn
  · obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨F, hmem⟩ hc
    refine ⟨x, hx, le_antisymm ?_ (le_csSup hb (mem_image_of_mem _ hx))⟩
    apply csSup_le ⟨_, mem_image_of_mem _ hmem⟩
    rintro _ ⟨y, hy, rfl⟩
    exact hmax hy

theorem preconditioning_upper_of_recovery_bound
    (first : OriginalPhysicalReachable F rho response edges s mid)
    (later : OriginalPhysicalReachable F rho response edges mid t)
    (i : ι) (C : ℝ) (hrho : 0 ≤ rho i) (hpstart : ∀ j, 0 < s.prices j)
    (hstart : s.prices i = F i) (hclosure : t.dollars i = s.dollars i)
    (hbound : ∀ x, first.Visited i x → x * (x - F i) / (response i).impact x ≤ C)
    (hbelow : ∀ x, later.Visited i x → x ≤ F i) :
    (∫ u in t.prices i..F i, u / (response i).impact u) ≤
      rho i * (mid.time - s.time) * C := by
  have hfirst := first.recovery_upper_of_visited i C hbound
  have hlater := later.recovery_upper_of_visited i 0 (fun x hx => by
    have hp := later.visited_positive (first.endpoint_positive hpstart) i x hx
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hp.le (sub_nonpos.mpr (hbelow x hx)))
      ((response i).positive x hp).le)
  have hn1 := first.recovery_normal_form i
  have hn2 := later.recovery_normal_form i
  rw [hstart, coordinate_at_benchmark] at hn1
  rw [integral_required_eq_neg_coordinate]
  have hh := mul_le_mul_of_nonneg_left hfirst hrho
  have hh2 : rho i * later.recoveryIntegral i ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hrho (by simpa using hlater)
  nlinarith

/-- Full session-one maximum budget, with all later sessions aggregated as a trace. -/
theorem proposition_7_4_first_session
    (first : OriginalPhysicalReachable F rho response edges s mid)
    (later : OriginalPhysicalReachable F rho response edges mid t)
    (i : ι) (U : ℝ) (hF : 0 < F i) (hU : F i < U) (hrho : 0 ≤ rho i)
    (hpstart : ∀ j, 0 < s.prices j) (hstart : s.prices i = F i)
    (hclosure : t.dollars i = s.dollars i)
    (hupper : ∀ x, first.Visited i x → x ≤ U)
    (hbelow : ∀ x, later.Visited i x → x ≤ F i) :
    (∫ u in t.prices i..F i, u / (response i).impact u) ≤
      rho i * (mid.time - s.time) * recoveryCeiling (F i) U (response i) := by
  apply preconditioning_upper_of_recovery_bound first later i _ hrho hpstart hstart hclosure
    (hbelow := hbelow)
  intro x hx
  exact (recoveryCeiling_properties _ _ _ hF hU.le).2.1 x
    (first.visited_positive hpstart i x hx) (hupper x hx)

theorem preconditioning_integer_log_bound (q H : ℝ) (D : ℕ)
    (hq : 0 < q) (hq1 : q < 1) (hH : 2 * H < 1)
    (hbudget : 1 - 2 * H ≤ q ^ (2 * D)) :
    (D : ℝ) ≤ Real.log (1 - 2 * H) / (2 * Real.log q) := by
  have hp : 0 < 1 - 2 * H := by linarith
  have hl := Real.log_le_log hp hbudget
  rw [Real.log_pow] at hl
  have hqlog : Real.log q < 0 := Real.log_neg hq hq1
  apply (le_div_iff_of_neg (show 2 * Real.log q < 0 by linarith)).mpr
  push_cast at hl
  nlinarith

/-- Constant-impact specialization, including the natural-number streak-length bound. -/
theorem proposition_7_4_constant
    (first : OriginalPhysicalReachable F rho response edges s mid)
    (later : OriginalPhysicalReachable F rho response edges mid t)
    (i : ι) (η beta q : ℝ) (D : ℕ)
    (hF : 0 < F i) (hη : 0 < η) (hbeta : 0 < beta) (hq : 0 < q) (hq1 : q < 1)
    (hrho : 0 ≤ rho i) (hpstart : ∀ j, 0 < s.prices j)
    (hstart : s.prices i = F i) (hclosure : t.dollars i = s.dollars i)
    (himpact : (response i).impact = fun _ => η)
    (hend : t.prices i = F i * q ^ D)
    (hupper : ∀ x, first.Visited i x → x ≤ F i * (1 + beta))
    (hbelow : ∀ x, later.Visited i x → x ≤ F i) :
    (1 - q ^ (2 * D)) / (2 * beta * (1 + beta)) ≤ rho i * (mid.time - s.time) ∧
    (2 * (rho i * (mid.time - s.time) * beta * (1 + beta)) < 1 →
      (D : ℝ) ≤ Real.log (1 - 2 * (rho i * (mid.time - s.time) * beta * (1 + beta))) /
        (2 * Real.log q)) := by
  let C := (F i) ^ 2 * beta * (1 + beta) / η
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb : (∫ u in t.prices i..F i, u / (response i).impact u) ≤
      rho i * (mid.time - s.time) * C := by
    apply preconditioning_upper_of_recovery_bound first later i C hrho hpstart hstart hclosure
      (hbelow := hbelow)
    intro x hx
    rw [himpact]
    have hxp := first.visited_positive hpstart i x hx
    by_cases hxF : x ≤ F i
    · exact (div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hxp.le (sub_nonpos.mpr hxF)) hη.le).trans hC
    · have hprod : x * (x - F i) ≤ (F i * (1 + beta)) * (F i * beta) := by
        apply mul_le_mul (hupper x hx) (by linarith [hupper x hx])
          (by linarith [le_of_not_ge hxF]) (by positivity)
      have hh := div_le_div_of_nonneg_right hprod hη.le
      dsimp [C]
      convert hh using 1
      ring
  have hcost : (∫ u in t.prices i..F i, u / (response i).impact u) =
      (F i) ^ 2 * (1 - q ^ (2 * D)) / (2 * η) := by
    rw [integral_required_eq_neg_coordinate, himpact, hend,
      ← constantCoordinate_eq_integral (F i) η hF hη (mul_pos hF (pow_pos hq D))]
    dsimp [constantCoordinate]
    simp only [mul_pow, ← pow_mul, Nat.mul_comm D 2]
    ring
  rw [hcost] at hb
  have hrate : (1 - q ^ (2 * D)) / (2 * beta * (1 + beta)) ≤
      rho i * (mid.time - s.time) := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * beta * (1 + beta))).mpr
    have hηm := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 2 * η)
    have hcostcancel : ((F i) ^ 2 * (1 - q ^ (2 * D)) / (2 * η)) * (2 * η) =
        (F i) ^ 2 * (1 - q ^ (2 * D)) := div_mul_cancel₀ _ (by positivity)
    have hCcancel : rho i * (mid.time - s.time) * C * (2 * η) =
        (F i) ^ 2 * (rho i * (mid.time - s.time) * (2 * beta * (1 + beta))) := by
      dsimp [C]
      field_simp
      ring
    rw [hcostcancel, hCcancel] at hηm
    exact (mul_le_mul_left (sq_pos_of_pos hF)).mp hηm
  refine ⟨hrate, ?_⟩
  intro hsmall
  apply preconditioning_integer_log_bound q _ D hq hq1 hsmall
  have hh := (div_le_iff₀ (by positivity : 0 < 2 * beta * (1 + beta))).mp hrate
  nlinarith

def OriginalPhysicalReachable.preconditioningConcat
    (first : OriginalPhysicalReachable F rho response edges s mid) :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges mid t →
      OriginalPhysicalReachable F rho response edges s t
  | _, .refl _ => first
  | _, .append previous step => (first.preconditioningConcat previous).append step

theorem OriginalPhysicalReachable.recoveryIntegral_preconditioningConcat
    (first : OriginalPhysicalReachable F rho response edges s mid)
    (later : OriginalPhysicalReachable F rho response edges mid t) (i : ι) :
    (first.preconditioningConcat later).recoveryIntegral i = first.recoveryIntegral i + later.recoveryIntegral i := by
  induction later with
  | refl => simp [OriginalPhysicalReachable.preconditioningConcat, OriginalPhysicalReachable.recoveryIntegral]
  | append previous step ih =>
    simp only [OriginalPhysicalReachable.preconditioningConcat, OriginalPhysicalReachable.recoveryIntegral, ih, add_assoc]

theorem OriginalPhysicalReachable.aboveMeasure_preconditioningConcat
    (first : OriginalPhysicalReachable F rho response edges s mid)
    (later : OriginalPhysicalReachable F rho response edges mid t) (i : ι) :
    (first.preconditioningConcat later).aboveBenchmarkMeasure i =
      first.aboveBenchmarkMeasure i + later.aboveBenchmarkMeasure i := by
  induction later with
  | refl => simp [OriginalPhysicalReachable.preconditioningConcat, OriginalPhysicalReachable.aboveBenchmarkMeasure]
  | append previous step ih =>
    simp only [OriginalPhysicalReachable.preconditioningConcat, OriginalPhysicalReachable.aboveBenchmarkMeasure, ih, add_assoc]

def OriginalPhysicalStep.aboveBenchmarkTimes
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : Set ℝ :=
  match step with
  | .continuous m _ _ _ _ => {u | u ∈ Ioc m.a m.b ∧ F i < m.prices u i}
  | .pulse _ _ _ _ => ∅

def OriginalPhysicalReachable.aboveBenchmarkTimes {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ι → Set ℝ
  | _, .refl _, _ => ∅
  | _, .append previous step, i => previous.aboveBenchmarkTimes i ∪ step.aboveBenchmarkTimes i

theorem OriginalPhysicalStep.aboveTimes_measurable
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) :
    MeasurableSet (step.aboveBenchmarkTimes i) := by
  cases step with
  | continuous m _ _ _ _ =>
    have hc : Continuous (fun u : ℝ => m.prices (projIcc m.a m.b m.time_order u) i) :=
      (m.continuous_prices i).restrict.comp continuous_projIcc
    have he : {u | u ∈ Ioc m.a m.b ∧ F i < m.prices u i} =
        Ioc m.a m.b ∩ {u | F i < m.prices (projIcc m.a m.b m.time_order u) i} := by
      ext u
      constructor
      · rintro ⟨hu, hb⟩
        exact ⟨hu, by simpa only [mem_setOf_eq, projIcc_of_mem m.time_order ⟨hu.1.le, hu.2⟩] using hb⟩
      · rintro ⟨hu, hb⟩
        exact ⟨hu, by simpa only [mem_setOf_eq, projIcc_of_mem m.time_order ⟨hu.1.le, hu.2⟩] using hb⟩
    change MeasurableSet {u | u ∈ Ioc m.a m.b ∧ F i < m.prices u i}
    rw [he]
    exact measurableSet_Ioc.inter (measurableSet_lt measurable_const hc.measurable)
  | pulse => exact MeasurableSet.empty

theorem OriginalPhysicalStep.aboveTimes_subset
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) :
    step.aboveBenchmarkTimes i ⊆ Ioc s.time t.time := by
  cases step with
  | continuous => exact fun _ h => h.1
  | pulse => exact empty_subset _

theorem OriginalPhysicalReachable.aboveTimes_subset
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    trace.aboveBenchmarkTimes i ⊆ Ioc s.time t.time := by
  induction trace with
  | refl => exact empty_subset _
  | append previous step ih =>
    intro u hu
    rcases hu with hu | hu
    · have hh := ih hu
      exact ⟨hh.1, hh.2.trans step.chronological⟩
    · have hh := step.aboveTimes_subset i hu
      exact ⟨previous.chronological.trans_lt hh.1, hh.2⟩

/-- The accumulated measure is exactly volume of actual physical-time excursions.
Chronological Ioc pieces are disjoint; fixed-time pulses contribute nothing. -/
theorem OriginalPhysicalReachable.aboveTimes_volume
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    volume (trace.aboveBenchmarkTimes i) = trace.aboveBenchmarkMeasure i := by
  induction trace with
  | refl => simp [OriginalPhysicalReachable.aboveBenchmarkTimes, OriginalPhysicalReachable.aboveBenchmarkMeasure]
  | append previous step ih =>
    have hd : Disjoint (previous.aboveBenchmarkTimes i) (step.aboveBenchmarkTimes i) := by
      apply Set.disjoint_left.mpr
      intro u hu hv
      have hp := previous.aboveTimes_subset i hu
      have hs := step.aboveTimes_subset i hv
      exact (not_lt_of_ge hp.2) hs.1
    change volume (previous.aboveBenchmarkTimes i ∪ step.aboveBenchmarkTimes i) =
      previous.aboveBenchmarkMeasure i + step.aboveBenchmarkMeasure i
    rw [measure_union hd (step.aboveTimes_measurable i), ih]
    congr 1
    cases step <;> simp [OriginalPhysicalStep.aboveBenchmarkTimes, OriginalPhysicalStep.aboveBenchmarkMeasure]

/-- Proposition 7.4, all clauses. The two traces represent session one and
all subsequent sessions, with genuine physical durations and zero-time pulses.
Only the selected asset's dollar closure is needed.

Manuscript statement (paper/main.tex, prop:streak-precondition):
Let an asset begin at F and finish D sessions at s_D<F, with X_i(T_D)=0.
Then its trajectory necessarily visits S_i>F on a set of positive trading-time
measure and satisfies rho*integral_0^{T_D} S_i(S_i-F)/g(S_i) dt
= integral_{s_D}^F u/g(u) du > 0.
If every session after the first keeps the asset at or below F, and the
first-session upper band is U_1>F, a necessary condition is
rho*tau_1*max_{F<=u<=U_1} u(u-F)/g(u) >= integral_{s_D}^F u/g(u) du.
For constant impact g=eta, and s_D=F*q^D, U_1=F*(1+beta_+), this simplifies
to rho*tau_1 >= (1-q^(2D))/(2*beta_+*(1+beta_+)).
Writing H_+=rho*tau_1*beta_+*(1+beta_+), whenever 2H_+<1 this imposes
the additional necessary streak-length bound D<=log(1-2H_+)/(2*log q).
This bound is specific to terminal dollar closure and the absence of
above-fundamental excursions in later sessions. It is not sufficient
to produce a consecutive limit-down path. -/
theorem proposition_7_4_original
    (first : OriginalPhysicalReachable F rho response edges s mid)
    (later : OriginalPhysicalReachable F rho response edges mid t)
    (i : ι) (hF : 0 < F i) (hrho : 0 ≤ rho i) (hpstart : ∀ j, 0 < s.prices j)
    (hstart : s.prices i = F i) (hclosure : t.dollars i = s.dollars i)
    (hfinal : t.prices i < F i) :
    rho i * (first.recoveryIntegral i + later.recoveryIntegral i) =
      (∫ u in t.prices i..F i, u / (response i).impact u) ∧
    0 < (∫ u in t.prices i..F i, u / (response i).impact u) ∧
    0 < volume ((first.preconditioningConcat later).aboveBenchmarkTimes i) ∧
    (∀ U : ℝ, F i < U →
      (∀ x, first.Visited i x → x ≤ U) →
      (∀ x, later.Visited i x → x ≤ F i) →
      (∫ u in t.prices i..F i, u / (response i).impact u) ≤
        rho i * (mid.time - s.time) * recoveryCeiling (F i) U (response i)) ∧
    (∀ η beta q : ℝ, ∀ D : ℕ, 0 < η → 0 < beta → 0 < q → q < 1 →
      (response i).impact = (fun _ => η) → t.prices i = F i * q ^ D →
      (∀ x, first.Visited i x → x ≤ F i * (1 + beta)) →
      (∀ x, later.Visited i x → x ≤ F i) →
      (1 - q ^ (2 * D)) / (2 * beta * (1 + beta)) ≤ rho i * (mid.time - s.time) ∧
      (2 * (rho i * (mid.time - s.time) * beta * (1 + beta)) < 1 →
        (D : ℝ) ≤ Real.log (1 - 2 * (rho i * (mid.time - s.time) * beta * (1 + beta))) /
          (2 * Real.log q))) := by
  let trace := first.preconditioningConcat later
  have htpos := trace.endpoint_positive hpstart i
  have hc : coordinate (F i) (response i).impact (t.prices i) < 0 := by
    simpa only [coordinate_at_benchmark] using
      coordinate_strictMonoOn (F i) (response i) hF htpos hF hfinal
  have hn := trace.recovery_normal_form i
  rw [hstart, coordinate_at_benchmark, hclosure] at hn
  have he : rho i * trace.recoveryIntegral i =
      (∫ u in t.prices i..F i, u / (response i).impact u) := by
    rw [integral_required_eq_neg_coordinate]
    linarith
  have hcost : 0 < (∫ u in t.prices i..F i, u / (response i).impact u) := by
    rw [integral_required_eq_neg_coordinate]
    linarith
  have hmeasure : 0 < trace.aboveBenchmarkMeasure i := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have hh := mul_nonpos_of_nonneg_of_nonpos hrho
      (trace.recovery_nonpositive_of_zero_excursion i hz)
    rw [he] at hh
    linarith
  have hphysical : 0 < volume ((first.preconditioningConcat later).aboveBenchmarkTimes i) := by
    rw [OriginalPhysicalReachable.aboveTimes_volume]
    exact hmeasure
  dsimp [trace] at he hmeasure
  rw [first.recoveryIntegral_preconditioningConcat later i] at he
  rw [first.aboveMeasure_preconditioningConcat later i] at hmeasure
  refine ⟨he, hcost, hphysical, ?_, ?_⟩
  · intro U hU hupper hbelow
    exact proposition_7_4_first_session first later i U hF hU hrho hpstart hstart hclosure hupper hbelow
  · intro η beta q D hη hb hq hq1 hg hend hupper hbelow
    exact proposition_7_4_constant first later i η beta q D hF hη hb hq hq1 hrho hpstart
      hstart hclosure hg hend hupper hbelow

end MarketCrash
