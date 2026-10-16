import MarketCrash.OperationalClockMarket

/-!
Reachable-price curvature for the common operational-clock regular class.

Even with simultaneous directed edge execution and a clock that can pause
physical time, actual price trajectories are continuous in the OPERATIONAL
parameter. Starting every asset at F, the intermediate value theorem then
makes each radial interval [min F S, max F S] a set of ACTUALLY VISITED
prices. Thus e(S)>=1 need only hold along the physical path's prices.

These theorems still assume differentiability everywhere in operational
time, not merely a.e. derivatives of an arbitrary BV completed graph.
-/

noncomputable section
namespace MarketCrash

/-- Each price between the benchmark and the current physical price has
really occurred along the common operational execution clock. -/
theorem OperationalClockSegment.radial_price_attained
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges)
    (i : ι) (hinit : m.prices m.a i = F)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (x : ℝ) (hx : x ∈ Set.Icc (min F (m.prices t i))
      (max F (m.prices t i))) :
    ∃ u ∈ Set.Icc m.a t, m.prices u i = x := by
  have hc : ContinuousOn (fun u : ℝ => m.prices u i) (Set.uIcc m.a t) := by
    intro u hu
    have hui : u ∈ Set.Icc m.a t := by
      simpa only [Set.uIcc_of_le ht.1] using hu
    have hum : u ∈ Set.Icc m.a m.b :=
      ⟨hui.1, hui.2.trans ht.2⟩
    exact (m.physical_price_flow u hum i).continuousAt.continuousWithinAt
  have hbetween : x ∈ Set.uIcc (m.prices m.a i) (m.prices t i) := by
    simpa only [Set.uIcc, hinit] using hx
  obtain ⟨u, hu, heq⟩ := (intermediate_value_uIcc hc) hbetween
  refine ⟨u, ?_, heq⟩
  simpa only [Set.uIcc_of_le ht.1] using hu

/-- A simultaneous, multi-edge and recovering PHYSICAL market retains
its potential barrier if e>=1 only at prices VISITED in operational time.
The starting prices are the common benchmark, ensuring that every radial
price required for the restoring tangent inequality is attained. -/
theorem OperationalClockSegment.potential_nonnegative_of_attained_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ t ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices t i)) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  let H : ℝ → ℝ := fun t =>
    potential (fun i => coordinate F g.impact (m.prices t i))
  let slope : ℝ → ℝ := fun t =>
    -rho * m.timeSpeed t *
      ∑ i, m.prices t i * (m.prices t i - F) / g.impact (m.prices t i)
  have hd (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
      HasDerivAt H (slope t) t :=
    m.potential_ode F rho g edges hF t ht
  have hbound (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
      -rho * m.timeSpeed t * H t ≤ slope t := by
    have hrestore := restoring_drain_sum_le_potential_of_radial_elasticity
      F g hF (m.prices t) (m.positive_prices t ht)
      (fun i x hx => by
        have hp : 0 < x :=
          (lt_min hF (m.positive_prices t ht i)).trans_le hx.1
        exact hdiff x hp)
      (fun i x hx => by
        obtain ⟨u, hu, heq⟩ := m.radial_price_attained
          F rho g edges i (hinit i) t ht x hx
        have hab : u ∈ Set.Icc m.a m.b :=
          ⟨hu.1, hu.2.trans ht.2⟩
        rw [← heq]
        exact hel u hab i)
    have hfactor : 0 ≤ rho * m.timeSpeed t :=
      mul_nonneg hrho (m.nonnegative_time_speed t ht)
    have hn : 0 ≤ (rho * m.timeSpeed t) *
      (H t - ∑ i, m.prices t i * (m.prices t i - F) /
        g.impact (m.prices t i)) :=
      mul_nonneg hfactor (sub_nonneg.mpr hrestore)
    dsimp [slope]
    nlinarith
  have hstart : 0 ≤ H m.a := by
    have hz (i : ι) : coordinate F g.impact (m.prices m.a i) = 0 := by
      rw [hinit i, coordinate_at_benchmark]
    simp [H, potential, hz]
  exact nonnegative_of_variable_clock_derivative_on_Icc
    H slope m.physicalTime m.timeSpeed rho m.a m.b m.order
    hd m.physical_time_flow hbound hstart

/-- Theorem 3.1 analogue for a true physical common operational clock,
with elasticity tested only at prices attained in the market path. -/
theorem OperationalClockSegment.no_all_asset_decline_of_attained_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ t ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices t i)) :
    ¬ ∀ i, m.prices m.b i < F := by
  exact not_all_below_benchmark F g hF (m.prices m.b)
    (m.positive_prices m.b ⟨m.order, le_rfl⟩)
    (m.potential_nonnegative_of_attained_elasticity
      F rho g edges hF hrho hdiff hinit hel)

/-- Theorem 3.2 analogue for the joint physical operational-clock
segment, using the existing precise terminal log-loss semantics. For
now this e>=2 assumption is GLOBAL, not restricted to visited prices. -/
theorem OperationalClockSegment.no_systemic_crisis_of_global_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (q : ι → ℝ) (hq : ∀ i, m.prices m.b i = F * Real.exp (q i))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hel1 : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S := by
    intro S hs
    linarith [hel S hs]
  have hstart :
      0 ≤ potential (fun i => coordinate F g.impact (m.prices m.a i)) := by
    have hz (i : ι) : coordinate F g.impact (m.prices m.a i) = 0 := by
      rw [hinit i, coordinate_at_benchmark]
    simp [potential, hz]
  have hpotential :
      0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) :=
    m.potential_nonnegative F rho g edges hF hrho hdiff hel1 hstart
  have hlog :
      (∑ i, logCoordinate F g.impact (q i)) =
        potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) =
      coordinate F g.impact (m.prices m.b i)
    rw [hq i]
  apply no_positive_crisis_of_elasticity_ge_two_and_potential
    F g hF hdiff hel q k
  rw [hlog]
  exact hpotential

end MarketCrash
