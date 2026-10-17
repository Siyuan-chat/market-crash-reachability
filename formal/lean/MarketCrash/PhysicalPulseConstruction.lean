import MarketCrash.OriginalInputPackaging
import MarketCrash.LocalResponseFlow

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace MarketCrash

/-- Any actual positive single-edge price flow on its closed dollar interval
has a finite inventory reserve realizing the literal original pulse. -/
theorem exists_original_single_edge_pulse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t : ℝ) (F : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i)
    (S : ℝ → ι → ℝ)
    (hc : ∀ i, ContinuousOn (fun a => S a i) (Icc 0 z))
    (hp : ∀ a ∈ Icc 0 z, ∀ i, 0 < S a i)
    (hd : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (fun u => S u i)
      ((g i).impact (S a i) / S a i * pairedMatrix edges i e) a) :
    ∃ p : OriginalDollarParameterPulse edges,
      p.edge = e ∧ p.z = z ∧ p.physicalTime = t ∧ p.F = F ∧ p.response = g ∧
      p.prices = S ∧ ∀ i, p.dollarLedger 0 i = 0 := by
  let w : ι → ℝ → ℝ := fun i a => pairedMatrix edges i e / S a i
  let V : ι → ℝ → ℝ := fun i a => ∫ u in (0 : ℝ)..a, w i u
  have hw : ∀ i, ContinuousOn (w i) (Icc 0 z) := fun i =>
    continuousOn_const.div (hc i) (fun a ha => (hp a ha i).ne')
  have hi : ∀ i, IntervalIntegrable (w i) volume 0 z := fun i =>
    (hw i).intervalIntegrable_of_Icc hz.le
  have hV : ∀ i, ContinuousOn (V i) (Icc 0 z) := by
    intro i
    simpa only [V, uIcc_of_le hz.le] using
      (intervalIntegral.continuousOn_primitive_interval' (hi i) left_mem_uIcc)
  let H : ι → ℝ := fun i => sSup ((fun a => -V i a) '' Icc 0 z)
  have hreserve : ∀ a ∈ Icc 0 z, ∀ i, 0 ≤ H i + V i a := by
    intro a ha i
    have hh : -V i a ≤ H i := le_csSup
      (isCompact_Icc.bddAbove_image (hV i).neg) (mem_image_of_mem _ ha)
    linarith
  have hVd : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (V i) (w i a) a := by
    intro a ha i
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hw i).mono (fun x hx => ⟨hx.1, hx.2.trans ha.2.le⟩)
        |>.intervalIntegrable_of_Icc ha.1.le
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo
        ((hw i).mono Ioo_subset_Icc_self) a ha
    · exact (hw i).continuousAt (Icc_mem_nhds ha.1 ha.2)
  let p : OriginalDollarParameterPulse edges := {
    physicalTime := t
    edge := e
    z := z
    z_positive := hz
    F := F
    response := g
    benchmark_positive := hF
    prices := S
    shares := fun a i => H i + V i a
    dollarLedger := fun a i => a * pairedMatrix edges i e
    continuous_prices := hc
    continuous_shares := fun i => continuousOn_const.add (hV i)
    continuous_ledgers := fun i => (continuous_id.mul continuous_const).continuousOn
    positive_prices := hp
    no_short_sales := hreserve
    price_flow := hd
    share_flow := fun a ha i => (hVd a ha i).const_add (H i)
    ledger_flow := fun a _ i => by simpa using (hasDerivAt_id a).mul_const (pairedMatrix edges i e) }
  exact ⟨p, rfl, rfl, rfl, rfl, rfl, rfl, fun i => by simp [p]⟩

/-- A coordinate segment lying in genuine local inverse charts gives an
actual single-edge pulse, including finite no-short inventory. -/
theorem exists_original_chart_edge_pulse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t : ℝ) (F : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i)
    (R : ι → ℝ → ℝ) (ε x : ι → ℝ)
    (hR : ∀ i, ContDiffOn ℝ 3 (R i) (Metric.ball 0 (ε i)))
    (hp : ∀ i, ∀ y ∈ Metric.ball 0 (ε i), 0 < R i y ∧
      coordinate (F i) (g i).impact (R i y) = y ∧
      HasDerivAt (R i) ((g i).impact (R i y) / R i y) y)
    (hseg : ∀ a ∈ Icc 0 z, ∀ i,
      x i + a * pairedMatrix edges i e ∈ Metric.ball 0 (ε i)) :
    ∃ p : OriginalDollarParameterPulse edges,
      p.edge = e ∧ p.z = z ∧ p.physicalTime = t ∧ p.F = F ∧ p.response = g ∧
      (∀ a i, p.prices a i = R i (x i + a * pairedMatrix edges i e)) ∧
      (∀ a ∈ Icc 0 z, ∀ i, coordinate (F i) (g i).impact (p.prices a i) =
        x i + a * pairedMatrix edges i e) ∧
      ∀ i, p.dollarLedger 0 i = 0 := by
  let S := fun a i => R i (x i + a * pairedMatrix edges i e)
  have hc : ∀ i, ContinuousOn (fun a => S a i) (Icc 0 z) := by
    intro i
    exact (hR i).continuousOn.comp
      (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
      (fun a ha => hseg a ha i)
  have hpos : ∀ a ∈ Icc 0 z, ∀ i, 0 < S a i :=
    fun a ha i => (hp i _ (hseg a ha i)).1
  have hd : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (fun u => S u i)
      ((g i).impact (S a i) / S a i * pairedMatrix edges i e) a := by
    intro a ha i
    have hh := (hp i _ (hseg a ⟨ha.1.le, ha.2.le⟩ i)).2.2
    convert hh.comp a (((hasDerivAt_id a).mul_const (pairedMatrix edges i e)).const_add (x i)) using 1
    simp [S]
  obtain ⟨p, he, hz', ht, hF', hg, hS, hL⟩ :=
    exists_original_single_edge_pulse edges e z hz t F g hF S hc hpos hd
  refine ⟨p, he, hz', ht, hF', hg, ?_, ?_, hL⟩
  · intro a i
    rw [hS]
  · intro a ha i
    rw [hS]
    exact (hp i _ (hseg a ha i)).2.1

/-- One shared primitive makes stock joins exact across ordered pulses. -/
def chartSharePrimitive (R : ℝ → ℝ) (y : ℝ) : ℝ := ∫ u in (0 : ℝ)..y, 1 / R u

def chartInventoryReserve (R : ℝ → ℝ) (ε : ℝ) : ℝ :=
  sSup ((fun y => -chartSharePrimitive R y) '' Icc (-ε) ε)

theorem chart_share_regular (R : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hc : ContinuousOn R (Metric.ball 0 (2 * ε)))
    (hp : ∀ y ∈ Metric.ball 0 (2 * ε), 0 < R y) :
    ContinuousOn (chartSharePrimitive R) (Icc (-ε) ε) ∧
    (∀ y ∈ Icc (-ε) ε, HasDerivAt (chartSharePrimitive R) (1 / R y) y) ∧
    ∀ y ∈ Icc (-ε) ε, 0 ≤ chartInventoryReserve R ε + chartSharePrimitive R y := by
  have hs : Icc (-ε) ε ⊆ Metric.ball 0 (2 * ε) := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hz : (0 : ℝ) ∈ Icc (-ε) ε := ⟨by linarith, hε.le⟩
  have hw : ContinuousOn (fun u => 1 / R u) (Metric.ball 0 (2 * ε)) :=
    continuousOn_const.div hc (fun u hu => (hp u hu).ne')
  have hi : IntervalIntegrable (fun u => 1 / R u) volume (-ε) ε :=
    (hw.mono hs).intervalIntegrable_of_Icc (by linarith)
  have hA : ContinuousOn (chartSharePrimitive R) (Icc (-ε) ε) := by
    simpa only [chartSharePrimitive, uIcc_of_le (show -ε ≤ ε by linarith)] using
      intervalIntegral.continuousOn_primitive_interval' hi
        (show (0 : ℝ) ∈ uIcc (-ε) ε by rw [uIcc_of_le (by linarith)]; exact hz)
  refine ⟨hA, ?_, ?_⟩
  · intro y hy
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hw.mono ((uIcc_subset_Icc hz hy).trans hs)).intervalIntegrable
    · exact hw.stronglyMeasurableAtFilter Metric.isOpen_ball y (hs hy)
    · exact hw.continuousAt (Metric.isOpen_ball.mem_nhds (hs hy))
  · intro y hy
    have hh : -chartSharePrimitive R y ≤ chartInventoryReserve R ε :=
      le_csSup (isCompact_Icc.bddAbove_image hA.neg) (mem_image_of_mem _ hy)
    linarith

def chartEdgePulse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t : ℝ) (F : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i)
    (R : ι → ℝ → ℝ) (ε x H ℓ : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hR : ∀ i, ContinuousOn (R i) (Metric.ball 0 (2 * ε i)))
    (hp : ∀ i, ∀ y ∈ Metric.ball 0 (2 * ε i), 0 < R i y ∧
      coordinate (F i) (g i).impact (R i y) = y ∧
      HasDerivAt (R i) ((g i).impact (R i y) / R i y) y)
    (hseg : ∀ a ∈ Icc 0 z, ∀ i, x i + a * pairedMatrix edges i e ∈ Icc (-ε i) (ε i))
    (hstock : ∀ i, chartInventoryReserve (R i) (ε i) ≤ H i) :
    OriginalDollarParameterPulse edges := by
  have hs : ∀ i, Icc (-ε i) (ε i) ⊆ Metric.ball 0 (2 * ε i) := by
    intro i y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hy.1, hy.2, hε i]
  have hA := fun i => chart_share_regular (R i) (ε i) (hε i) (hR i)
    (fun y hy => (hp i y hy).1)
  refine {
    physicalTime := t
    edge := e
    z := z
    z_positive := hz
    F := F
    response := g
    benchmark_positive := hF
    prices := fun a i => R i (x i + a * pairedMatrix edges i e)
    shares := fun a i => H i + chartSharePrimitive (R i) (x i + a * pairedMatrix edges i e)
    dollarLedger := fun a i => ℓ i + a * pairedMatrix edges i e
    continuous_prices := ?_
    continuous_shares := ?_
    continuous_ledgers := fun _ => (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    positive_prices := fun a ha i => (hp i _ (hs i (hseg a ha i))).1
    no_short_sales := ?_
    price_flow := ?_
    share_flow := ?_
    ledger_flow := ?_ }
  · intro i
    exact (hR i).comp (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
      (fun a ha => hs i (hseg a ha i))
  · intro i
    exact continuousOn_const.add ((hA i).1.comp
      (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
      (fun a ha => hseg a ha i))
  · intro a ha i
    have hh := (hA i).2.2 _ (hseg a ha i)
    linarith [hstock i]
  · intro a ha i
    have hh := (hp i _ (hs i (hseg a ⟨ha.1.le, ha.2.le⟩ i))).2.2
    convert hh.comp a (((hasDerivAt_id a).mul_const (pairedMatrix edges i e)).const_add (x i)) using 1
    simp
  · intro a ha i
    have hh := (hA i).2.1 _ (hseg a ⟨ha.1.le, ha.2.le⟩ i)
    convert (hh.comp a (((hasDerivAt_id a).mul_const (pairedMatrix edges i e)).const_add (x i))).const_add (H i) using 1
    simp [div_eq_mul_inv, mul_comm]
  · intro a _ i
    simpa using ((hasDerivAt_id a).mul_const (pairedMatrix edges i e)).const_add (ℓ i)

section FiniteSchedule
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

def chartState (t : ℝ) (R : ι → ℝ → ℝ) (H x ℓ : ι → ℝ) : PhysicalMarketState ι :=
  ⟨t, fun i => R i (x i), fun i => H i + chartSharePrimitive (R i) (x i), ℓ⟩

def chartControlEndpoint (edges : κ → PairedEdge ι) :
    (ι → ℝ) → List (κ × ℝ) → (ι → ℝ)
  | x, [] => x
  | x, c :: cs => chartControlEndpoint edges (fun i => x i + c.2 * pairedMatrix edges i c.1) cs

def chartScheduleInside (edges : κ → PairedEdge ι) (ε : ι → ℝ) :
    (ι → ℝ) → List (κ × ℝ) → Prop
  | _, [] => True
  | x, c :: cs => 0 < c.2 ∧
      (∀ a ∈ Icc 0 c.2, ∀ i, x i + a * pairedMatrix edges i c.1 ∈ Icc (-ε i) (ε i)) ∧
      chartScheduleInside edges ε (fun i => x i + c.2 * pairedMatrix edges i c.1) cs

def original_reachable_trans {F rho : ι → ℝ} {g : ι → Response}
    {edges : κ → PairedEdge ι} {s m t : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m)
    (h' : OriginalPhysicalReachable F rho g edges m t) :
    OriginalPhysicalReachable F rho g edges s t := by
  induction h' with
  | refl => exact h
  | append prev step ih => exact .append ih step

/-- A finite ordered list of literal single-edge pulses, with exact joins in
all four economic fields. No simultaneous multi-edge primitive is used. -/
theorem chart_schedule_reachable
    (edges : κ → PairedEdge ι) (t : ℝ) (F rho : ι → ℝ) (g : ι → Response)
    (hF : ∀ i, 0 < F i) (R : ι → ℝ → ℝ) (ε H : ι → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hR : ∀ i, ContinuousOn (R i) (Metric.ball 0 (2 * ε i)))
    (hp : ∀ i, ∀ y ∈ Metric.ball 0 (2 * ε i), 0 < R i y ∧
      coordinate (F i) (g i).impact (R i y) = y ∧
      HasDerivAt (R i) ((g i).impact (R i y) / R i y) y)
    (hstock : ∀ i, chartInventoryReserve (R i) (ε i) ≤ H i)
    (cs : List (κ × ℝ)) (x ℓ : ι → ℝ) (hcs : chartScheduleInside edges ε x cs) :
    Nonempty (OriginalPhysicalReachable F rho g edges
      (chartState t R H x ℓ)
      (chartState t R H (chartControlEndpoint edges x cs)
        (chartControlEndpoint edges ℓ cs))) := by
  induction cs generalizing x ℓ with
  | nil => exact ⟨.refl _⟩
  | cons c cs ih =>
    obtain ⟨hz, hseg, htail⟩ := hcs
    let p := chartEdgePulse edges c.1 c.2 hz t F g hF R ε x H ℓ hε hR hp hseg hstock
    have hstep : OriginalPhysicalStep F rho g edges
        (chartState t R H x ℓ)
        (chartState t R H (fun i => x i + c.2 * pairedMatrix edges i c.1)
          (fun i => ℓ i + c.2 * pairedMatrix edges i c.1)) := by
      simpa only [p, chartEdgePulse, chartState, zero_mul, add_zero] using p.toOriginalStep rho
    obtain ⟨tail⟩ := ih (fun i => x i + c.2 * pairedMatrix edges i c.1)
      (fun i => ℓ i + c.2 * pairedMatrix edges i c.1) htail
    exact ⟨original_reachable_trans (.append (.refl _) hstep) tail⟩

omit [Fintype κ] in
theorem chart_schedule_eventually_inside (edges : κ → PairedEdge ι)
    (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) (cs : List (κ × ℝ))
    (hpos : ∀ c ∈ cs, 0 < c.2) (x : ℝ → ι → ℝ)
    (hx : ∀ i, Tendsto (fun h => x h i) (nhds 0) (nhds 0)) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0),
      chartScheduleInside edges ε (x h) (cs.map (fun c => (c.1, h * c.2))) := by
  induction cs generalizing x with
  | nil => simp [chartScheduleInside]
  | cons c cs ih =>
    have htailpos : ∀ d ∈ cs, 0 < d.2 := fun d hd => hpos d (List.mem_cons_of_mem _ hd)
    have hcz : 0 < c.2 := hpos c (by simp)
    let y : ℝ → ι → ℝ := fun h i => x h i + h * c.2 * pairedMatrix edges i c.1
    have hy : ∀ i, Tendsto (fun h => y h i) (nhds 0) (nhds 0) := by
      intro i
      simpa [y] using (hx i).add ((tendsto_id.mul_const c.2).mul_const (pairedMatrix edges i c.1))
    have htail := ih htailpos y hy
    have hxb : ∀ᶠ h in nhds 0, ∀ i, x h i ∈ Icc (-ε i) (ε i) := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((hx i).eventually (Ioo_mem_nhds (by linarith [hε i]) (hε i))).mono
        (fun _ h => ⟨h.1.le, h.2.le⟩)
    have hyb : ∀ᶠ h in nhds 0, ∀ i, y h i ∈ Icc (-ε i) (ε i) := by
      apply Filter.eventually_all.mpr
      intro i
      exact ((hy i).eventually (Ioo_mem_nhds (by linarith [hε i]) (hε i))).mono
        (fun _ h => ⟨h.1.le, h.2.le⟩)
    filter_upwards [htail, hxb.filter_mono nhdsWithin_le_nhds,
      hyb.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with h htail hxb hyb hh
    refine ⟨mul_pos hh hcz, ?_, htail⟩
    intro a ha i
    dsimp only at ha ⊢
    obtain ⟨hxlo, hxhi⟩ := hxb i
    have hyi := hyb i
    dsimp [y] at hyi
    obtain ⟨hylo, hyhi⟩ := hyi
    rcases le_total 0 (pairedMatrix edges i c.1) with hb | hb
    · constructor
      · nlinarith [mul_nonneg ha.1 hb]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ha.2) hb]
    · constructor
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha.2) hb]
      · nlinarith [mul_nonpos_of_nonneg_of_nonpos ha.1 hb]

omit [Fintype ι] [Fintype κ] in
theorem chartControlEndpoint_eq (edges : κ → PairedEdge ι) (x : ι → ℝ)
    (cs : List (κ × ℝ)) (i : ι) :
    chartControlEndpoint edges x cs i = x i + (cs.map fun c => c.2 * pairedMatrix edges i c.1).sum := by
  induction cs generalizing x with
  | nil => simp [chartControlEndpoint]
  | cons c cs ih =>
    rw [chartControlEndpoint, ih]
    simp only [List.map_cons, List.sum_cons]
    ring

def positiveDollarSchedule (d : κ → ℝ) : List (κ × ℝ) := by
  classical
  exact ((Finset.univ.filter fun e => 0 < d e).toList).map fun e => (e, d e)

theorem positiveDollarSchedule_positive (d : κ → ℝ) :
    ∀ c ∈ positiveDollarSchedule d, 0 < c.2 := by
  classical
  intro c hc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2

omit [Fintype ι] in
theorem positiveDollarSchedule_endpoint (edges : κ → PairedEdge ι)
    (d : κ → ℝ) (hd : ∀ e, 0 ≤ d e) (x : ι → ℝ) (i : ι) :
    chartControlEndpoint edges x (positiveDollarSchedule d) i =
      x i + tradingInput (pairedMatrix edges) d i := by
  classical
  rw [chartControlEndpoint_eq]
  congr 1
  simp only [positiveDollarSchedule, List.map_map, Function.comp_def,
    Finset.sum_map_toList, tradingInput]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : 0 < d e
  · simp [he, mul_comm]
  · have hz : d e = 0 := le_antisymm (not_lt.mp he) (hd e)
    simp [he, hz]

theorem positiveDollarSchedule_scaled (d : κ → ℝ) (h : ℝ) (hh : 0 < h) :
    positiveDollarSchedule (fun e => h * d e) =
      (positiveDollarSchedule d).map (fun c => (c.1, h * c.2)) := by
  classical
  simp [positiveDollarSchedule, mul_pos_iff_of_pos_left hh, List.map_map, Function.comp_def]

/-- Every sufficiently small prescribed finite nonnegative dollar vector
is executed by an ordered list of original single-edge pulses. -/
theorem small_dollar_vector_reachable
    (edges : κ → PairedEdge ι) (t : ℝ) (F rho : ι → ℝ) (g : ι → Response)
    (hF : ∀ i, 0 < F i) (R : ι → ℝ → ℝ) (ε : ι → ℝ)
    (hε : ∀ i, 0 < ε i)
    (hR : ∀ i, ContinuousOn (R i) (Metric.ball 0 (2 * ε i)))
    (hp : ∀ i, ∀ y ∈ Metric.ball 0 (2 * ε i), 0 < R i y ∧
      coordinate (F i) (g i).impact (R i y) = y ∧
      HasDerivAt (R i) ((g i).impact (R i y) / R i y) y)
    (d : κ → ℝ) (hd : ∀ e, 0 ≤ d e) (x : ℝ → ι → ℝ)
    (hx : ∀ i, Tendsto (fun h => x h i) (nhds 0) (nhds 0)) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0), ∀ H ℓ : ι → ℝ,
      (∀ i, chartInventoryReserve (R i) (ε i) ≤ H i) →
      Nonempty (OriginalPhysicalReachable F rho g edges (chartState t R H (x h) ℓ)
        (chartState t R H
          (fun i => x h i + h * tradingInput (pairedMatrix edges) d i)
          (fun i => ℓ i + h * tradingInput (pairedMatrix edges) d i))) := by
  have he := chart_schedule_eventually_inside edges ε hε (positiveDollarSchedule d)
    (positiveDollarSchedule_positive d) x hx
  filter_upwards [he, self_mem_nhdsWithin] with h he hh
  intro H ℓ hstock
  rw [← positiveDollarSchedule_scaled d h hh] at he
  have hr := chart_schedule_reachable edges t F rho g hF R ε H hε hR hp hstock
    (positiveDollarSchedule (fun e => h * d e)) (x h) ℓ he
  have hend (v : ι → ℝ) : chartControlEndpoint edges v
      (positiveDollarSchedule (fun e => h * d e)) =
        fun i => v i + h * tradingInput (pairedMatrix edges) d i := by
    funext i
    rw [positiveDollarSchedule_endpoint edges _ (fun e => mul_nonneg hh.le (hd e))]
    congr 1
    simp only [tradingInput, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  simpa only [hend] using hr

theorem chartSharePrimitive_tendsto_zero (R : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hc : ContinuousOn R (Metric.ball 0 (2 * ε)))
    (hp : ∀ y ∈ Metric.ball 0 (2 * ε), 0 < R y) (x : ℝ → ℝ)
    (hx : Tendsto x (nhds 0) (nhds 0)) :
    Tendsto (fun h => chartSharePrimitive R (x h)) (nhds 0) (nhds 0) := by
  have hA := (chart_share_regular R ε hε hc hp).1.continuousAt
    (Icc_mem_nhds (by linarith) hε)
  convert hA.tendsto.comp hx using 1
  simp [chartSharePrimitive]

omit [DecidableEq ι] in
theorem eventual_chart_inventory_reserve (R : ι → ℝ → ℝ) (ε H : ι → ℝ)
    (hH : ∀ i, chartInventoryReserve (R i) (ε i) < H i)
    (V : ℝ → ι → ℝ) (hV : ∀ i, Tendsto (fun h => V h i) (nhds 0) (nhds (H i))) :
    ∀ᶠ h in nhds 0, ∀ i, chartInventoryReserve (R i) (ε i) ≤ V h i := by
  apply Filter.eventually_all.mpr
  intro i
  exact ((hV i).eventually (Ioi_mem_nhds (hH i))).mono (fun _ hh => hh.le)

end FiniteSchedule
end MarketCrash
