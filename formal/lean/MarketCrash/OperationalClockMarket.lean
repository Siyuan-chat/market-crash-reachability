import MarketCrash.StieltjesClockPulse
import MarketCrash.AttainableElasticity

/-!
Joint physical execution and recovery under a COMMON operational clock.

The operational parameter u can keep physical time fixed while several
paired-dollar edges execute, or advance physical time while they execute.
All price/share/ledger equations are PHYSICAL; the response-adapted
coordinate equation and potential inequality are derived, not assumed.

This smooth operational-clock subclass is a constructive bridge toward a
completed-graph representation of BV controls. It does not yet cover an
arbitrary Lipschitz (a.e. differentiable) completed graph, nor establish
faithful inclusion of every manuscript M1--M5 admissible BV market path.
-/

noncomputable section
namespace MarketCrash

/-- A physical market segment in the common operational parameter u.
The time speed and all directed edge-dollar rates are nonnegative.
The same executed dollars drive prices, shares, per-asset ledgers,
and cumulative edge-dollar execution. -/
structure OperationalClockSegment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  a : ℝ
  b : ℝ
  order : a ≤ b
  physicalTime : ℝ → ℝ
  timeSpeed : ℝ → ℝ
  edgeDollars : ℝ → κ → ℝ
  edgeRates : ℝ → κ → ℝ
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  positive_prices : ∀ u ∈ Set.Icc a b, ∀ i, 0 < prices u i
  no_short_sales : ∀ u ∈ Set.Icc a b, ∀ i, 0 ≤ shares u i
  finite_share_variation : ∀ i,
    BoundedVariationOn (fun u => shares u i) (Set.Icc a b)
  nonnegative_time_speed : ∀ u ∈ Set.Icc a b, 0 ≤ timeSpeed u
  nonnegative_edge_rates : ∀ u ∈ Set.Icc a b, ∀ e, 0 ≤ edgeRates u e
  physical_time_flow : ∀ u ∈ Set.Icc a b,
    HasDerivAt physicalTime (timeSpeed u) u
  cumulative_edge_flow : ∀ u ∈ Set.Icc a b, ∀ e,
    HasDerivAt (fun v => edgeDollars v e) (edgeRates u e) u
  physical_price_flow : ∀ u ∈ Set.Icc a b, ∀ i,
    HasDerivAt (fun v => prices v i)
      (-rho * (prices u i - F) * timeSpeed u +
        g.impact (prices u i) *
          (tradingInput (pairedMatrix edges) (edgeRates u) i / prices u i)) u
  physical_share_flow : ∀ u ∈ Set.Icc a b, ∀ i,
    HasDerivAt (fun v => shares v i)
      (tradingInput (pairedMatrix edges) (edgeRates u) i / prices u i) u
  physical_ledger_flow : ∀ u ∈ Set.Icc a b, ∀ i,
    HasDerivAt (fun v => dollarLedger v i)
      (tradingInput (pairedMatrix edges) (edgeRates u) i) u

/-- Both the physical time clock and its execution parameter are
chronologically ordered, even if physical time pauses during a trade. -/
theorem OperationalClockSegment.time_monotoneOn
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges) :
    MonotoneOn m.physicalTime (Set.Icc m.a m.b) := by
  have hc : ContinuousOn m.physicalTime (Set.Icc m.a m.b) := by
    intro u hu
    exact (m.physical_time_flow u hu).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ m.physicalTime
      (interior (Set.Icc m.a m.b)) := by
    intro u hu
    exact (m.physical_time_flow u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Set.Icc m.a m.b),
      0 ≤ deriv m.physicalTime u := by
    intro u hu
    exact (m.physical_time_flow u (interior_subset hu)).deriv ▸
      m.nonnegative_time_speed u (interior_subset hu)
  exact monotoneOn_of_deriv_nonneg (convex_Icc m.a m.b) hc hd hderiv

/-- Cumulative executed dollars on every edge are nondecreasing. -/
theorem OperationalClockSegment.edgeDollars_monotoneOn
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges) (e : κ) :
    MonotoneOn (fun u => m.edgeDollars u e) (Set.Icc m.a m.b) := by
  have hc : ContinuousOn (fun u => m.edgeDollars u e) (Set.Icc m.a m.b) := by
    intro u hu
    exact (m.cumulative_edge_flow u hu e).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (fun u => m.edgeDollars u e)
      (interior (Set.Icc m.a m.b)) := by
    intro u hu
    exact (m.cumulative_edge_flow u (interior_subset hu) e).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Set.Icc m.a m.b),
      0 ≤ deriv (fun u => m.edgeDollars u e) u := by
    intro u hu
    exact (m.cumulative_edge_flow u (interior_subset hu) e).deriv ▸
      m.nonnegative_edge_rates u (interior_subset hu) e
  exact monotoneOn_of_deriv_nonneg (convex_Icc m.a m.b) hc hd hderiv

/-- Positivity plus the PHYSICAL price equation imply the transformed
joint trade-and-recovery ODE in operational time. No transformed market
equation is assumed anywhere in the model. -/
theorem OperationalClockSegment.coordinate_ode
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges) (hF : 0 < F)
    (u : ℝ) (hu : u ∈ Set.Icc m.a m.b) (i : ι) :
    HasDerivAt (fun v => coordinate F g.impact (m.prices v i))
      (tradingInput (pairedMatrix edges) (m.edgeRates u) i -
        rho * m.timeSpeed u *
          (m.prices u i * (m.prices u i - F) / g.impact (m.prices u i))) u := by
  have hs : 0 < m.prices u i := m.positive_prices u hu i
  have hp : m.prices u i ≠ 0 := hs.ne'
  have hg : g.impact (m.prices u i) ≠ 0 :=
    (g.positive (m.prices u i) hs).ne'
  have h := (coordinate_hasDerivAt F g hF hs).comp u
    (m.physical_price_flow u hu i)
  convert h using 1 <;> dsimp [Function.comp] <;> field_simp [hp, hg] <;> ring

/-- Summing the physically derived coordinate equations cancels the
simultaneously active directed paired-dollar edges EXACTLY.
The remaining term is genuine price resilience with physical-time speed. -/
theorem OperationalClockSegment.potential_ode
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges) (hF : 0 < F)
    (u : ℝ) (hu : u ∈ Set.Icc m.a m.b) :
    HasDerivAt
      (fun v => potential (fun i => coordinate F g.impact (m.prices v i)))
      (-rho * m.timeSpeed u *
        ∑ i, m.prices u i * (m.prices u i - F) /
          g.impact (m.prices u i)) u := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => m.coordinate_ode F rho g edges hF u hu i)
  have heq :
      (∑ i, (tradingInput (pairedMatrix edges) (m.edgeRates u) i -
        rho * m.timeSpeed u *
          (m.prices u i * (m.prices u i - F) / g.impact (m.prices u i)))) =
      -rho * m.timeSpeed u *
        ∑ i, m.prices u i * (m.prices u i - F) /
          g.impact (m.prices u i) := by
    rw [Finset.sum_sub_distrib, paired_trading_sum_zero]
    simp [Finset.mul_sum, mul_assoc]
  simpa [potential, heq] using hd

/-- Integrating-factor comparison with a VARIABLE physical clock.
Only differentiability in the operational parameter on [a,b] is used.
This formulation handles flat physical-time segments without dividing
by dt/du. -/
theorem nonnegative_of_variable_clock_derivative_on_Icc
    (H slope tau speed : ℝ → ℝ) (rho a b : ℝ) (hab : a ≤ b)
    (hdH : ∀ u ∈ Set.Icc a b, HasDerivAt H (slope u) u)
    (hdt : ∀ u ∈ Set.Icc a b, HasDerivAt tau (speed u) u)
    (hbound : ∀ u ∈ Set.Icc a b, -rho * speed u * H u ≤ slope u)
    (hstart : 0 ≤ H a) :
    0 ≤ H b := by
  let J : ℝ → ℝ := fun v => Real.exp (rho * tau v) * H v
  have hJ (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt J
        (Real.exp (rho * tau u) * (rho * speed u * H u + slope u)) u := by
    have hinner : HasDerivAt (fun v => rho * tau v) (rho * speed u) u :=
      (hdt u hu).const_mul rho
    have hexp : HasDerivAt (fun v => Real.exp (rho * tau v))
        (Real.exp (rho * tau u) * (rho * speed u)) u :=
      by
        convert (Real.hasDerivAt_exp (rho * tau u)).comp u hinner using 1 <;> ring
    convert (hexp.mul (hdH u hu)) using 1 <;> ring
  have hc : ContinuousOn J (Set.Icc a b) := by
    intro u hu
    exact (hJ u hu).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ J (interior (Set.Icc a b)) := by
    intro u hu
    exact (hJ u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Set.Icc a b), 0 ≤ deriv J u := by
    intro u hu
    rw [(hJ u (interior_subset hu)).deriv]
    have hnonneg : 0 ≤ rho * speed u * H u + slope u := by
      have hs := hbound u (interior_subset hu)
      linarith
    exact mul_nonneg (Real.exp_pos _).le hnonneg
  have hmono : MonotoneOn J (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hc hd hderiv
  have hJa : 0 ≤ J a := by
    change 0 ≤ Real.exp (rho * tau a) * H a
    exact mul_nonneg (Real.exp_pos _).le hstart
  have hJb : 0 ≤ J b := hJa.trans
    (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  classical
  by_contra hbad
  have hneg : H b < 0 := lt_of_not_ge hbad
  have hJneg : J b < 0 :=
    mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  exact (not_lt_of_ge hJb) hJneg

/-- The potential barrier under simultaneous multi-edge execution and
recovery follows from the PHYSICAL operational-clock ODE. The elasticity
domain is global for now; attainable-range localization is separate. -/
theorem OperationalClockSegment.potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (m.prices m.a i))) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  let H : ℝ → ℝ := fun v =>
    potential (fun i => coordinate F g.impact (m.prices v i))
  let slope : ℝ → ℝ := fun v =>
    -rho * m.timeSpeed v *
      ∑ i, m.prices v i * (m.prices v i - F) / g.impact (m.prices v i)
  have hd (u : ℝ) (hu : u ∈ Set.Icc m.a m.b) :
      HasDerivAt H (slope u) u :=
    m.potential_ode F rho g edges hF u hu
  have hb (u : ℝ) (hu : u ∈ Set.Icc m.a m.b) :
      -rho * m.timeSpeed u * H u ≤ slope u := by
    have hrest := restoring_drain_sum_le_potential_of_elasticity_ge_one
      F g hF hdiff hel (m.prices u) (m.positive_prices u hu)
    have hfactor : 0 ≤ rho * m.timeSpeed u :=
      mul_nonneg hrho (m.nonnegative_time_speed u hu)
    have hineq : 0 ≤ (rho * m.timeSpeed u) *
      (H u - ∑ i, m.prices u i * (m.prices u i - F) /
        g.impact (m.prices u i)) :=
      mul_nonneg hfactor (sub_nonneg.mpr hrest)
    dsimp [slope]
    nlinarith
  exact nonnegative_of_variable_clock_derivative_on_Icc
    H slope m.physicalTime m.timeSpeed rho m.a m.b m.order
    hd m.physical_time_flow hb hstart

/-- Even with multiple simultaneously active directed trading edges,
an operational interval with zero physical-time speed exactly preserves
the aggregate coordinate potential. This includes a flow-completed
instantaneous trade represented as a flat physical-time interval. -/
theorem OperationalClockSegment.potential_eq_of_frozen_time
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : OperationalClockSegment F rho g edges) (hF : 0 < F)
    (hfreeze : ∀ u ∈ Set.Icc m.a m.b, m.timeSpeed u = 0) :
    potential (fun i => coordinate F g.impact (m.prices m.b i)) =
      potential (fun i => coordinate F g.impact (m.prices m.a i)) := by
  have hFTC :
      (∫ u in m.a..m.b, (0 : ℝ)) =
        potential (fun i => coordinate F g.impact (m.prices m.b i)) -
          potential (fun i => coordinate F g.impact (m.prices m.a i)) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v => potential (fun i => coordinate F g.impact (m.prices v i)))
      (f' := fun _ : ℝ => (0 : ℝ))
      (a := m.a) (b := m.b)
      (fun u hu => by
        have hui : u ∈ Set.Icc m.a m.b := by
          simpa only [Set.uIcc_of_le m.order] using hu
        simpa [hfreeze u hui] using
          m.potential_ode F rho g edges hF u hui)
      intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hFTC
  linarith

end MarketCrash
