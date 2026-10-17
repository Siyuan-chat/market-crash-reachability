import MarketCrash.ContinuousClock
import Mathlib.Topology.Order.ProjIcc
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section
namespace MarketCrash
open Set MeasureTheory

/-- A continuous piece has a genuine inverse, extended only by endpoint clamping. -/
theorem continuous_piece_clamped_inverse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (exec : StieltjesPairedExecution edges)
    (scale a b : ℝ) (hs : 0 < scale) (hab : a ≤ b)
    (hc : ∀ e, ContinuousOn (exec.cumulative e) (Icc a b)) :
    ∃ time : ℝ → ℝ, Continuous time ∧ Monotone time ∧
      (∀ u, time u ∈ Icc a b) ∧
      (∀ u, exec.variationClock scale (time u) =
        max (exec.variationClock scale a) (min (exec.variationClock scale b) u)) ∧
      (∀ t ∈ Icc a b, time (exec.variationClock scale t) = t) := by
  obtain ⟨T, hright, hmap, hleft, _, _, hLip, _⟩ :=
    exec.continuous_clock_inverse scale a b hs hab hc
  have hmono := exec.variationClock_strictMono scale hs.le
  let p := projIcc (exec.variationClock scale a) (exec.variationClock scale b)
    (hmono.monotone hab)
  let time : ℝ → ℝ := fun u => T (p u)
  have htime : Continuous time := hLip.continuous.comp continuous_projIcc
  refine ⟨time, htime, ?_, (fun u => (T (p u)).property), ?_, ?_⟩
  · intro u v huv
    apply hmono.le_iff_le.mp
    change exec.variationClock scale (T (p u) : ℝ) ≤ exec.variationClock scale (T (p v) : ℝ)
    rw [hright, hright]
    exact monotone_projIcc _ huv
  · intro u
    exact hright (p u)
  · intro t ht
    dsimp [time, p]
    rw [projIcc_of_mem _ (hmap t ht)]
    exact hleft ⟨t, ht⟩ _

/-- Endpoint-clamped reparametrization of a continuous Stieltjes cumulative. -/
def clockTransformedCumulative (G : StieltjesFunction) (time : ℝ → ℝ)
    (a b : ℝ) (ht : Continuous time) (hm : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b)) : StieltjesFunction where
  toFun := fun u => G (time u)
  mono' := G.mono.comp hm
  right_continuous' := fun _ =>
    (hG.comp_continuous ht hr).continuousAt.continuousWithinAt

/-- Exact pushforward for a strictly increasing continuous-piece clock.
The inverse identities and clamp are properties proved above, not change-of-variable premises. -/
theorem clamped_clock_measure_map
    (G : StieltjesFunction) (clock time : ℝ → ℝ) (a b : ℝ)
    (_hab : a ≤ b) (hm : StrictMono clock)
    (ht : Continuous time) (hmt : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b))
    (hct : ∀ u, clock (time u) = max (clock a) (min (clock b) u)) :
    Measure.map clock (G.measure.restrict (Ioc a b)) =
      (clockTransformedCumulative G time a b ht hmt hr hG).measure := by
  have hset (s t : ℝ) : clock ⁻¹' Ioc s t ∩ Ioc a b = Ioc (time s) (time t) := by
    have hiff (u x : ℝ) (hx : x ∈ Ioc a b) :
        (u < clock x ↔ time u < x) ∧ (clock x ≤ u ↔ x ≤ time u) := by
      have hA : clock a < clock x := hm hx.1
      have hB : clock x ≤ clock b := hm.monotone hx.2
      have hclamp : (max (clock a) (min (clock b) u) < clock x ↔ u < clock x) ∧
          (clock x ≤ max (clock a) (min (clock b) u) ↔ clock x ≤ u) := by
        constructor
        · rw [max_lt_iff, min_lt_iff]
          constructor
          · rintro ⟨_, h | h⟩
            · exact False.elim ((not_lt_of_ge hB) h)
            · exact h
          · intro h
            exact ⟨hA, Or.inr h⟩
        · rw [le_max_iff, le_min_iff]
          constructor
          · rintro (h | ⟨_, h⟩)
            · exact False.elim ((not_le_of_gt hA) h)
            · exact h
          · intro h
            exact Or.inr ⟨hB, h⟩
      constructor
      · have hi := hm.lt_iff_lt (a := time u) (b := x)
        rw [hct] at hi
        exact hclamp.1.symm.trans hi
      · have hi := hm.le_iff_le (a := x) (b := time u)
        rw [hct] at hi
        exact hclamp.2.symm.trans hi
    ext x
    constructor
    · rintro ⟨hx, hxrange⟩
      exact ⟨((hiff s x hxrange).1.mp hx.1), ((hiff t x hxrange).2.mp hx.2)⟩
    · intro hx
      have hxrange : x ∈ Ioc a b := ⟨(hr s).1.trans_lt hx.1, hx.2.trans (hr t).2⟩
      exact ⟨⟨(hiff s x hxrange).1.mpr hx.1, (hiff t x hxrange).2.mpr hx.2⟩, hxrange⟩
  symm
  apply Measure.ext_of_Ioc
  intro s t _
  rw [Measure.map_apply hm.monotone.measurable measurableSet_Ioc,
    Measure.restrict_apply (measurableSet_Ioc.preimage hm.monotone.measurable), hset, G.measure_Ioc]
  exact (clockTransformedCumulative G time a b ht hmt hr hG).measure_Ioc s t

theorem clamped_clock_integral
    (G : StieltjesFunction) (clock time : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : StrictMono clock)
    (ht : Continuous time) (hmt : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b))
    (hct : ∀ u, clock (time u) = max (clock a) (min (clock b) u))
    (htc : ∀ x ∈ Icc a b, time (clock x) = x)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) :
    (∫ x in Ioc a b, w x ∂G.measure) =
      ∫ u, w (time u) ∂(clockTransformedCumulative G time a b ht hmt hr hG).measure := by
  rw [← clamped_clock_measure_map G clock time a b hab hm ht hmt hr hG hct]
  have hmeas : AEStronglyMeasurable (fun u => w (time u))
      (Measure.map clock (G.measure.restrict (Ioc a b))) :=
    (hw.comp_continuous ht hr).stronglyMeasurable.aestronglyMeasurable
  rw [integral_map hm.monotone.measurable.aemeasurable hmeas]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [htc x ⟨hx.1.le, hx.2⟩]

theorem clamped_clock_measure_map_restrict
    (G : StieltjesFunction) (clock time : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : StrictMono clock)
    (ht : Continuous time) (hmt : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b))
    (hct : ∀ u, clock (time u) = max (clock a) (min (clock b) u)) :
    Measure.map clock (G.measure.restrict (Ioc a b)) =
      (clockTransformedCumulative G time a b ht hmt hr hG).measure.restrict
        (Ioc (clock a) (clock b)) := by
  have he := clamped_clock_measure_map G clock time a b hab hm ht hmt hr hG hct
  rw [← he]
  symm
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_map_iff hm.monotone.measurable.aemeasurable measurableSet_Ioc).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact ⟨hm hx.1, hm.monotone hx.2⟩

theorem clamped_clock_integral_restrict
    (G : StieltjesFunction) (clock time : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : StrictMono clock)
    (ht : Continuous time) (hmt : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b))
    (hct : ∀ u, clock (time u) = max (clock a) (min (clock b) u))
    (htc : ∀ x ∈ Icc a b, time (clock x) = x)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) :
    (∫ x in Ioc a b, w x ∂G.measure) =
      ∫ u in Ioc (clock a) (clock b), w (time u)
        ∂(clockTransformedCumulative G time a b ht hmt hr hG).measure := by
  have he := clamped_clock_measure_map G clock time a b hab hm ht hmt hr hG hct
  have her := clamped_clock_measure_map_restrict G clock time a b hab hm ht hmt hr hG hct
  have hs : (clockTransformedCumulative G time a b ht hmt hr hG).measure.restrict
      (Ioc (clock a) (clock b)) =
      (clockTransformedCumulative G time a b ht hmt hr hG).measure := her.symm.trans he
  change _ = ∫ u, w (time u) ∂((clockTransformedCumulative G time a b ht hmt hr hG).measure.restrict _)
  rw [hs]
  exact clamped_clock_integral G clock time a b hab hm ht hmt hr hG hct htc w hw

theorem identity_stieltjes_measure_eq_volume : StieltjesFunction.id.measure = volume := by
  apply Measure.ext_of_Ioc
  intro a b _
  rw [StieltjesFunction.measure_Ioc, Real.volume_Ioc]
  rfl

/-- Concrete original continuous piece: the SAME constructed inverse works for
every edge cumulative and also the identity cumulative (physical time). -/
theorem continuous_piece_change_of_variables
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (exec : StieltjesPairedExecution edges)
    (scale a b : ℝ) (hs : 0 < scale) (hab : a ≤ b)
    (hc : ∀ e, ContinuousOn (exec.cumulative e) (Icc a b)) :
    ∃ time : ℝ → ℝ, ∃ ht : Continuous time, ∃ hmt : Monotone time,
      ∃ hr : ∀ u, time u ∈ Icc a b,
      (∀ G : StieltjesFunction, ∀ hG : ContinuousOn G (Icc a b),
        Measure.map (exec.variationClock scale) (G.measure.restrict (Ioc a b)) =
          (clockTransformedCumulative G time a b ht hmt hr hG).measure.restrict
            (Ioc (exec.variationClock scale a) (exec.variationClock scale b)) ∧
        ∀ w : ℝ → ℝ, ContinuousOn w (Icc a b) →
          (∫ t in Ioc a b, w t ∂G.measure) =
            ∫ u in Ioc (exec.variationClock scale a) (exec.variationClock scale b),
              w (time u) ∂(clockTransformedCumulative G time a b ht hmt hr hG).measure) ∧
      (Measure.map (exec.variationClock scale) (volume.restrict (Ioc a b)) =
        (clockTransformedCumulative StieltjesFunction.id time a b ht hmt hr
          continuousOn_id).measure.restrict
            (Ioc (exec.variationClock scale a) (exec.variationClock scale b))) ∧
      (∀ w : ℝ → ℝ, ContinuousOn w (Icc a b) →
        (∫ t in Ioc a b, w t) =
          ∫ u in Ioc (exec.variationClock scale a) (exec.variationClock scale b),
            w (time u) ∂(clockTransformedCumulative StieltjesFunction.id time a b ht hmt hr
              continuousOn_id).measure) := by
  obtain ⟨time, ht, hmt, hr, hct, htc⟩ := continuous_piece_clamped_inverse exec scale a b hs hab hc
  have hm := exec.variationClock_strictMono scale hs.le
  refine ⟨time, ht, hmt, hr, ?_, ?_, ?_⟩
  · intro G hG
    exact ⟨clamped_clock_measure_map_restrict G _ _ a b hab hm ht hmt hr hG hct,
      fun w hw => clamped_clock_integral_restrict G _ _ a b hab hm ht hmt hr hG hct htc w hw⟩
  · simpa only [identity_stieltjes_measure_eq_volume] using
      clamped_clock_measure_map_restrict StieltjesFunction.id _ _ a b hab hm ht hmt hr
        continuousOn_id hct
  · intro w hw
    simpa only [identity_stieltjes_measure_eq_volume] using
      clamped_clock_integral_restrict StieltjesFunction.id _ _ a b hab hm ht hmt hr
        continuousOn_id hct htc w hw

/-- Prefix/subinterval restriction for the SAME global transformed cumulative. -/
theorem clamped_clock_measure_map_subinterval
    (G : StieltjesFunction) (clock time : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : StrictMono clock)
    (ht : Continuous time) (hmt : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b))
    (hct : ∀ u, clock (time u) = max (clock a) (min (clock b) u))
    (s t : ℝ) (hs : s ∈ Icc a b) (ht' : t ∈ Icc a b) :
    Measure.map clock (G.measure.restrict (Ioc s t)) =
      (clockTransformedCumulative G time a b ht hmt hr hG).measure.restrict
        (Ioc (clock s) (clock t)) := by
  have hp : clock ⁻¹' Ioc (clock s) (clock t) = Ioc s t := by
    ext x
    exact and_congr hm.lt_iff_lt hm.le_iff_le
  rw [← clamped_clock_measure_map G clock time a b hab hm ht hmt hr hG hct,
    Measure.restrict_map hm.monotone.measurable measurableSet_Ioc,
    Measure.restrict_restrict (measurableSet_Ioc.preimage hm.monotone.measurable), hp]
  rw [inter_eq_left.mpr]
  intro x hx
  exact ⟨hs.1.trans_lt hx.1, hx.2.trans ht'.2⟩

theorem clamped_clock_integral_subinterval
    (G : StieltjesFunction) (clock time : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hm : StrictMono clock)
    (ht : Continuous time) (hmt : Monotone time)
    (hr : ∀ u, time u ∈ Icc a b) (hG : ContinuousOn G (Icc a b))
    (hct : ∀ u, clock (time u) = max (clock a) (min (clock b) u))
    (htc : ∀ x ∈ Icc a b, time (clock x) = x)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht' : t ∈ Icc a b) (hst : s ≤ t)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) :
    (∫ x in s..t, w x ∂G.measure) =
      ∫ u in clock s..clock t, w (time u)
        ∂(clockTransformedCumulative G time a b ht hmt hr hG).measure := by
  rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le (hm.monotone hst)]
  rw [← clamped_clock_measure_map_subinterval G clock time a b hab hm ht hmt hr hG hct s t hs ht']
  have hmeas : AEStronglyMeasurable (fun u => w (time u))
      (Measure.map clock (G.measure.restrict (Ioc s t))) :=
    (hw.comp_continuous ht hr).stronglyMeasurable.aestronglyMeasurable
  rw [integral_map hm.monotone.measurable.aemeasurable hmeas]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [htc x ⟨hs.1.trans hx.1.le, hx.2.trans ht'.2⟩]

end MarketCrash
