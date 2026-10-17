import MarketCrash.RadialSystemicBarrier
import MarketCrash.OperationalClockAEComparison
import Mathlib.Topology.Order.IntermediateValue

/-!
# Full attained-price 3.1 and 3.2 endpoint steps for AE physical market

Physical Lipschitz operational-clock prices are continuous in operational
time, even when the physical-time clock is frozen across atomic jumps.
Every radial price between F and a price actually visited during the
market is therefore visited by an intermediate operational-time state.
Elasticity is tested ONLY on those visited physical prices.

We deduce a.e. nonnegative derivative of the integrating factor from the
PHYSICAL marginal price/share/ledger ODE. The remaining analytical FTC
identity is explicit here, and is the next independent Lean proof gate.
No full M1--M5 original-BV path equivalence is claimed.
-/

noncomputable section
namespace MarketCrash

open MeasureTheory
open scoped Topology

/-- Every price on the radial interval between the initial benchmark F
and the current price of one asset is ACTUALLY visited in the same
Lipschitz physical operational-clock market segment. -/
theorem AEOperationalClockSegment.radial_price_attained
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (i : ι) (hinit : m.prices m.a i = F)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (x : ℝ) (hx : x ∈ Set.Icc (min F (m.prices t i))
      (max F (m.prices t i))) :
    ∃ u ∈ Set.Icc m.a t, m.prices u i = x := by
  obtain ⟨C, hC⟩ := m.prices_lipschitz i
  have hc : ContinuousOn (fun u : ℝ => m.prices u i)
      (Set.uIcc m.a t) := hC.continuous.continuousOn
  have hbetween : x ∈ Set.uIcc (m.prices m.a i) (m.prices t i) := by
    simpa only [Set.uIcc, hinit] using hx
  obtain ⟨u, hu, heq⟩ := (intermediate_value_uIcc hc) hbetween
  refine ⟨u, ?_, heq⟩
  simpa only [Set.uIcc_of_le ht.1] using hu

/-- Global in operational time, but only radial in price: e>=1 at
prices ACTUALLY VISITED by a given Lipschitz physically controlled
market implies a nonnegative integrating-factor derivative a.e. -/
theorem AEOperationalClockSegment.integrating_factor_deriv_nonneg_ae_of_visited_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i)) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b →
      0 ≤ deriv
        (fun v => Real.exp (rho * m.physicalTime v) *
          potential (fun i => coordinate F g.impact (m.prices v i))) u := by
  filter_upwards [m.integrating_factor_ode_ae F rho g edges hF]
    with u hJ hmem
  rw [(hJ hmem).deriv]
  have hrestore :
      (∑ i, m.prices u i * (m.prices u i - F) /
        g.impact (m.prices u i)) ≤
        potential (fun i => coordinate F g.impact (m.prices u i)) := by
    apply restoring_drain_sum_le_potential_of_radial_elasticity
      F g hF (m.prices u) (m.positive_prices u hmem)
    · intro i x hx
      have hxpos : 0 < x :=
        (lt_min hF (m.positive_prices u hmem i)).trans_le hx.1
      exact hdiff x hxpos
    · intro i x hx
      obtain ⟨v, hv, heq⟩ := m.radial_price_attained
        F rho g edges i (hinit i) u hmem x hx
      rw [← heq]
      exact hel v ⟨hv.1, hv.2.trans hmem.2⟩ i
  have hfactor : 0 ≤ rho * m.timeSpeed u :=
    mul_nonneg hrho (m.nonnegative_time_speed u hmem)
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le hfactor)
    (sub_nonneg.mpr hrestore)

/-- Attainable-price-1 barrier on a Lipschitz physical execution
segment, conditional ONLY on the analytically necessary a.e. FTC.
Unlike earlier theorems, e>=1 need not hold for unvisited prices. -/
theorem AEOperationalClockSegment.potential_nonnegative_of_FTC_and_visited_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i))
    (hFTC :
      (∫ u in m.a..m.b,
        deriv (fun v => Real.exp (rho * m.physicalTime v) *
          potential (fun i => coordinate F g.impact (m.prices v i))) u) =
      Real.exp (rho * m.physicalTime m.b) *
        potential (fun i => coordinate F g.impact (m.prices m.b i)) -
      Real.exp (rho * m.physicalTime m.a) *
        potential (fun i => coordinate F g.impact (m.prices m.a i))) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  let J : ℝ → ℝ := fun v => Real.exp (rho * m.physicalTime v) *
    potential (fun i => coordinate F g.impact (m.prices v i))
  have hstart : 0 ≤ J m.a := by
    have hz (i : ι) : coordinate F g.impact (m.prices m.a i) = 0 := by
      rw [hinit i, coordinate_at_benchmark]
    simp [J, potential, hz]
  have hJend : 0 ≤ J m.b :=
    nonnegative_of_ae_derivative_and_FTC J m.a m.b m.time_order
      (m.integrating_factor_deriv_nonneg_ae_of_visited_elasticity
        F rho g edges hF hrho hdiff hinit hel)
      hFTC hstart
  classical
  by_contra hbad
  have hneg : potential (fun i => coordinate F g.impact (m.prices m.b i)) < 0 :=
    lt_of_not_ge hbad
  exact (not_lt_of_ge hJend)
    (mul_neg_of_pos_of_neg (Real.exp_pos _) hneg)

/-- Any log price between the initial normalized benchmark 0 and the
terminal log price q_i occurs as an actual intermediate physical price
F exp x along the same Lipschitz physical execution. -/
theorem AEOperationalClockSegment.radial_log_price_attained
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (i : ι)
    (hinit : m.prices m.a i = F)
    (q : ℝ) (hfinal : m.prices m.b i = F * Real.exp q)
    (x : ℝ) (hx : x ∈ Set.Icc (min 0 q) (max 0 q)) :
    ∃ u ∈ Set.Icc m.a m.b, m.prices u i = F * Real.exp x := by
  have hmono : Monotone (fun y : ℝ => F * Real.exp y) :=
    fun u v huv =>
      mul_le_mul_of_nonneg_left (Real.exp_monotone huv) hF.le
  have hbetween : F * Real.exp x ∈
      Set.Icc (min F (m.prices m.b i)) (max F (m.prices m.b i)) := by
    rw [hfinal]
    have hradial : F * Real.exp x ∈
        Set.uIcc (F * Real.exp (0 : ℝ)) (F * Real.exp q) := by
      rcases le_total (0 : ℝ) q with hq | hq
      · have hx' : (0 : ℝ) ≤ x ∧ x ≤ q := by
          simpa [min_eq_left hq, max_eq_right hq] using hx
        rw [Set.uIcc_of_le (hmono hq)]
        exact ⟨hmono hx'.1, hmono hx'.2⟩
      · have hx' : q ≤ x ∧ x ≤ (0 : ℝ) := by
          simpa [min_eq_right hq, max_eq_left hq] using hx
        rw [Set.uIcc_of_ge (hmono hq)]
        exact ⟨hmono hx'.1, hmono hx'.2⟩
    simpa only [Real.exp_zero, mul_one, Set.uIcc] using hradial
  exact m.radial_price_attained F rho g edges i hinit
    m.b ⟨m.time_order, le_rfl⟩
    (F * Real.exp x) hbetween

/-- The exact systemic crisis bound for the a.e. Lipschitz physical
market, with e>=2 required only at ACTUALLY VISITED price states and
no global elasticity premise. The analytically separate FTC step
remains explicit; it is not silently made a model field. -/
theorem AEOperationalClockSegment.no_systemic_crisis_of_FTC_and_visited_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      2 ≤ responseElasticity g.impact (m.prices u i))
    (hFTC :
      (∫ u in m.a..m.b,
        deriv (fun v => Real.exp (rho * m.physicalTime v) *
          potential (fun i => coordinate F g.impact (m.prices v i))) u) =
      Real.exp (rho * m.physicalTime m.b) *
        potential (fun i => coordinate F g.impact (m.prices m.b i)) -
      Real.exp (rho * m.physicalTime m.a) *
        potential (fun i => coordinate F g.impact (m.prices m.a i)))
    (q : ι → ℝ) (hq : ∀ i, m.prices m.b i = F * Real.exp (q i))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hel1 : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i) := by
    intro u hu i
    linarith [hel u hu i]
  have hpotential :
      0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) :=
    m.potential_nonnegative_of_FTC_and_visited_elasticity
      F rho g edges hF hrho hdiff hinit hel1 hFTC
  have hlog :
      (∑ i, logCoordinate F g.impact (q i)) =
        potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) =
      coordinate F g.impact (m.prices m.b i)
    rw [hq i]
  apply no_positive_crisis_of_radial_elasticity_ge_two_and_potential
    F g hF q k
  · intro i x hx
    have hxpos : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
    exact hdiff (F * Real.exp x) hxpos
  · intro i x hx
    obtain ⟨u, hu, heq⟩ := m.radial_log_price_attained
      F rho g edges hF i (hinit i) (q i) (hq i) x hx
    rw [← heq]
    exact hel u hu i
  · rw [hlog]
    exact hpotential

end MarketCrash
