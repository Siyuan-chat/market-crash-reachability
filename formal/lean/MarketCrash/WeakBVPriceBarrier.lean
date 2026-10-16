import MarketCrash.AEAttainableBarrier
import MarketCrash.StieltjesExecution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The integrated NORMAL-FORM price law for continuous BV trade controls

The canonical manuscript derives d Phi(S_i) = Σ_e B_ie dZ_e -
rho*S_i(S_i-F)/g(S_i) dt and gives flow-completed rules for jumps.
For a continuous BV price/trading segment, its natural weak formulation
is an *integral identity for EACH asset*, with a genuine nondecreasing
Stieltjes cumulative-dollar flow on every directed edge.

Here we prove the potential law AND its nonnegative barrier FROM THESE
PER-ASSET WEAK PRICE EQUATIONS. NO invariant, Gronwall inequality, or
potential nonnegativity is included as an assumption.

A technical continuous real extension of the physical recovery drain
over the operational interval is carried as a witness for FTC-1; this
extension exists for continuous strictly positive price segments, but
that extension theorem has not yet been kernel-formalized in this project.

This module formally verifies the barrier for all paths having the
specified normal-form BV *solution semantics*. Proving that every
primitive physical M1--M5 BV execution induces this weak normal form
(the continuous-BV nonlinear chain rule) is a separate required
model-equivalence theorem. Do not silently identify the two classes.
-/

noncomputable section
namespace MarketCrash

open MeasureTheory
open scoped Topology

/-- A continuous finite-variation physical price path in the exact
response-adapted WEAK normal-form semantics of the paper.

The nonnegative right-continuous edge-dollar controls may contain
singular-continuous measures. Unlike a classical physical-time ODE,
this statement includes their ENTIRE Stieltjes executed-dollar mass
through cumulative increments in the per-asset price law.

The supplementary recoveryForce field is a globally continuous
extension of the physical recovery integrand restricted to [a,b];
it is NOT an assumed total potential law. -/
structure ContinuousWeakBVPriceSegment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  a : ℝ
  b : ℝ
  time_order : a ≤ b
  cumulative : κ → StieltjesFunction
  prices : ℝ → ι → ℝ
  prices_continuous : ∀ i, ContinuousOn
    (fun t => prices t i) (Set.Icc a b)
  positive_prices : ∀ t ∈ Set.Icc a b, ∀ i, 0 < prices t i
  recoveryForce : ℝ → ι → ℝ
  recoveryForce_continuous : ∀ i,
    Continuous (fun t => recoveryForce t i)
  recoveryForce_eq : ∀ t ∈ Set.Icc a b, ∀ i,
    recoveryForce t i =
      prices t i * (prices t i - F) / g.impact (prices t i)
  weak_physical_price_response : ∀ t ∈ Set.Icc a b, ∀ i,
    coordinate F g.impact (prices t i) =
      coordinate F g.impact (prices a i) +
        tradingInput (pairedMatrix edges)
          (fun e => (cumulative e) t - (cumulative e) a) i -
        rho * (∫ u in a..t, recoveryForce u i)

/-- Trade-normalized recovery primitive built from the REAL per-asset
recovery force. It has a classical derivative even if all cumulative
dollar controls are singular-continuous in physical time. -/
def ContinuousWeakBVPriceSegment.potentialPrimitive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : ContinuousWeakBVPriceSegment F rho g edges) (t : ℝ) : ℝ :=
  potential (fun i => coordinate F g.impact (m.prices m.a i)) -
    rho * ∑ i, (∫ u in m.a..t, m.recoveryForce u i)

/-- Exact aggregate potential identity, DERIVED by summing the
per-asset weak price equations and canceling paired edge-dollar flows,
not by postulating the aggregate invariant. -/
theorem ContinuousWeakBVPriceSegment.potential_eq_primitive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
    potential (fun i => coordinate F g.impact (m.prices t i)) =
      m.potentialPrimitive t := by
  unfold ContinuousWeakBVPriceSegment.potentialPrimitive potential
  calc
    (∑ i, coordinate F g.impact (m.prices t i)) =
      ∑ i, (coordinate F g.impact (m.prices m.a i) +
        tradingInput (pairedMatrix edges)
          (fun e => (m.cumulative e) t - (m.cumulative e) m.a) i -
        rho * (∫ u in m.a..t, m.recoveryForce u i)) := by
            apply Finset.sum_congr rfl
            intro i _
            exact m.weak_physical_price_response t ht i
    _ = (∑ i, coordinate F g.impact (m.prices m.a i)) +
        (∑ i, tradingInput (pairedMatrix edges)
          (fun e => (m.cumulative e) t - (m.cumulative e) m.a) i) -
        rho * (∑ i, (∫ u in m.a..t, m.recoveryForce u i)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
              ← Finset.mul_sum]
    _ = (∑ i, coordinate F g.impact (m.prices m.a i)) -
        rho * ∑ i, (∫ u in m.a..t, m.recoveryForce u i) := by
            rw [paired_trading_sum_zero]
            ring

/-- FTC-1 applies to each CONTINUOUS restoring drain in physical time,
irrespective of the singularity of the edge-dollar control measures. -/
theorem ContinuousWeakBVPriceSegment.recovery_integral_derivative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun v => ∫ u in m.a..v, m.recoveryForce u i)
      (m.recoveryForce t i) t := by
  have hcont : Continuous (fun v => m.recoveryForce v i) :=
    m.recoveryForce_continuous i
  have hmeas : StronglyMeasurableAtFilter
      (fun v => m.recoveryForce v i) (𝓝 t) :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_univ
      hcont.continuousOn t (Set.mem_univ t)
  exact intervalIntegral.integral_hasDerivAt_right
    (hcont.intervalIntegrable m.a t)
    hmeas hcont.continuousAt

/-- The total primitive has an everywhere-classical derivative.
ALL singular trading-dollar components disappeared by algebraic
cancellation, not by an a.e. derivative that could miss them. -/
theorem ContinuousWeakBVPriceSegment.potentialPrimitive_hasDerivAt
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (t : ℝ) :
    HasDerivAt m.potentialPrimitive
      (-rho * ∑ i, m.recoveryForce t i) t := by
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => m.recovery_integral_derivative t i)
  unfold ContinuousWeakBVPriceSegment.potentialPrimitive
  convert (hsum.const_mul (-rho)).const_add
    (potential (fun i => coordinate F g.impact (m.prices m.a i)))
      using 1 <;> ring

/-- The recovery primitive starts from the TRUE initial physical
potential, because the Lebesgue integral over a degenerate interval
vanishes. -/
theorem ContinuousWeakBVPriceSegment.potentialPrimitive_at_start
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : ContinuousWeakBVPriceSegment F rho g edges) :
    m.potentialPrimitive m.a =
      potential (fun i => coordinate F g.impact (m.prices m.a i)) := by
  simp [ContinuousWeakBVPriceSegment.potentialPrimitive]

/-- The genuinely weak Stieltjes BV physical-price law preserves
nonnegative aggregate potential at ANY requested physical time.
Proof: exact paired-dollar cancellation; classical FTC-1 on continuous
restoring integrands; local radial tangent and scalar Gronwall.

Crucially there is no C^1 price requirement and no a.e. FTC on the
singular-continuous trading controls. Only the continuous weak BV
price-law semantics already stated above is required. -/
theorem ContinuousWeakBVPriceSegment.potential_nonnegative_of_radial_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i x,
      x ∈ Set.Icc (min F (m.prices u i))
        (max F (m.prices u i)) →
      1 ≤ responseElasticity g.impact x)
    (hstart : 0 ≤ potential
      (fun i => coordinate F g.impact (m.prices m.a i)))
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices t i)) := by
  let H := m.potentialPrimitive
  let slope : ℝ → ℝ := fun u => -rho * ∑ i, m.recoveryForce u i
  have hd (u : ℝ) (hu : u ∈ Set.Icc m.a t) :
      HasDerivAt H (slope u) u :=
    m.potentialPrimitive_hasDerivAt u
  have hb (u : ℝ) (hu : u ∈ Set.Icc m.a t) :
      -rho * H u ≤ slope u := by
    have hw : u ∈ Set.Icc m.a m.b := ⟨hu.1, hu.2.trans ht.2⟩
    have hrest := restoring_drain_sum_le_potential_of_radial_elasticity
      F g hF (m.prices u) (m.positive_prices u hw)
      (fun i x hx => by
        have hxp : 0 < x :=
          (lt_min hF (m.positive_prices u hw i)).trans_le hx.1
        exact hdiff x hxp)
      (fun i x hx => hel u hw i x hx)
    have hforce :
        (∑ i, m.recoveryForce u i) =
          ∑ i, m.prices u i * (m.prices u i - F) /
            g.impact (m.prices u i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact m.recoveryForce_eq u hw i
    have hHu :
        H u = potential (fun i => coordinate F g.impact (m.prices u i)) :=
      (m.potential_eq_primitive F rho g edges u hw).symm
    have hpositive : 0 ≤ rho *
        (H u - ∑ i, m.recoveryForce u i) := by
      rw [hHu, hforce]
      exact mul_nonneg hrho (sub_nonneg.mpr hrest)
    dsimp [slope]
    nlinarith
  have hstartH : 0 ≤ H m.a := by
    change 0 ≤ m.potentialPrimitive m.a
    rw [m.potentialPrimitive_at_start]
    exact hstart
  have hbarrier : 0 ≤ H t :=
    nonnegative_of_derivative_ge_linear_on_Icc
      H slope rho m.a t ht.1 hd hb hstartH
  rw [m.potential_eq_primitive F rho g edges t ht]
  exact hbarrier

/-- Every intermediate radial price lies on the same continuous
physical-time price trajectory, even when the trading control driving
the trajectory has a singular-continuous Stieltjes component. -/
theorem ContinuousWeakBVPriceSegment.radial_price_attained
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (i : ι) (hinit : m.prices m.a i = F)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (x : ℝ) (hx : x ∈ Set.Icc (min F (m.prices t i))
      (max F (m.prices t i))) :
    ∃ u ∈ Set.Icc m.a t, m.prices u i = x := by
  have hc : ContinuousOn (fun u : ℝ => m.prices u i)
      (Set.uIcc m.a t) := by
    apply (m.prices_continuous i).mono
    intro u hu
    have hui : u ∈ Set.Icc m.a t := by
      simpa only [Set.uIcc_of_le ht.1] using hu
    exact ⟨hui.1, hui.2.trans ht.2⟩
  have hbetween : x ∈ Set.uIcc (m.prices m.a i) (m.prices t i) := by
    simpa only [Set.uIcc, hinit] using hx
  obtain ⟨u, hu, heq⟩ := (intermediate_value_uIcc hc) hbetween
  refine ⟨u, ?_, heq⟩
  simpa only [Set.uIcc_of_le ht.1] using hu

/-- A continuous genuine Stieltjes-BV weak price response path starting
from benchmark prices has H(t)>=0 at EVERY physical time, provided
elasticity e>=1 only at ACTUALLY VISITED prices of that path. -/
theorem ContinuousWeakBVPriceSegment.potential_nonnegative_of_visited_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i))
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices t i)) := by
  have hrad : ∀ u ∈ Set.Icc m.a m.b, ∀ i x,
      x ∈ Set.Icc (min F (m.prices u i))
        (max F (m.prices u i)) →
      1 ≤ responseElasticity g.impact x := by
    intro u hu i x hx
    obtain ⟨v, hv, heq⟩ :=
      m.radial_price_attained F rho g edges i (hinit i) u hu x hx
    rw [← heq]
    exact hel v ⟨hv.1, hv.2.trans hu.2⟩ i
  have hstart : 0 ≤ potential (fun i =>
      coordinate F g.impact (m.prices m.a i)) := by
    simp [potential, hinit, coordinate_at_benchmark]
  exact m.potential_nonnegative_of_radial_elasticity
    F rho g edges hF hrho hdiff hrad hstart t ht

/-- The paper's 3.1 type of barrier, for ALL continuous singular-BV
Stieltjes weak-normal-form price solutions satisfying the original
attained-price elasticity condition, at an ARBITRARY horizon t. -/
theorem ContinuousWeakBVPriceSegment.no_all_asset_decline_of_visited_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i))
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
    ¬ ∀ i, m.prices t i < F := by
  exact not_all_below_benchmark F g hF (m.prices t)
    (m.positive_prices t ht)
    (m.potential_nonnegative_of_visited_elasticity
      F rho g edges hF hrho hdiff hinit hel t ht)

/-- Every log-price between benchmark and a chosen physical-time price
is attained by the physical weak Stieltjes price trajectory. -/
theorem ContinuousWeakBVPriceSegment.radial_log_price_attained
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (hF : 0 < F) (i : ι)
    (hinit : m.prices m.a i = F)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (q : ℝ) (hfinal : m.prices t i = F * Real.exp q)
    (x : ℝ) (hx : x ∈ Set.Icc (min 0 q) (max 0 q)) :
    ∃ u ∈ Set.Icc m.a t, m.prices u i = F * Real.exp x := by
  have hmono : Monotone (fun z : ℝ => F * Real.exp z) :=
    fun a b hab => mul_le_mul_of_nonneg_left (Real.exp_monotone hab) hF.le
  have hbetween : F * Real.exp x ∈
      Set.Icc (min F (m.prices t i)) (max F (m.prices t i)) := by
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
  exact m.radial_price_attained F rho g edges i hinit t ht
    (F * Real.exp x) hbetween

/-- The paper's 3.2-type crisis exclusion for continuous BV physical
price paths with singular-continuous Stieltjes trading, and the EXACT
attained-price elasticity-2 premise. No a.e.-FTC assumption, since
paired trading cancels in the potential law and recovery is classically
differentiable in physical time by ordinary FTC-1.

The remaining physical M2-to-weak-normal-form BV chain-rule equivalence
is independent and NOT established by this statement. -/
theorem ContinuousWeakBVPriceSegment.no_systemic_crisis_of_visited_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      2 ≤ responseElasticity g.impact (m.prices u i))
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (q : ι → ℝ) (hq : ∀ i, m.prices t i = F * Real.exp (q i))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hel1 : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices u i) := by
    intro u hu i
    linarith [hel u hu i]
  have hpotential : 0 ≤ potential
      (fun i => coordinate F g.impact (m.prices t i)) :=
    m.potential_nonnegative_of_visited_elasticity
      F rho g edges hF hrho hdiff hinit hel1 t ht
  have hlog :
      (∑ i, logCoordinate F g.impact (q i)) =
        potential (fun i => coordinate F g.impact (m.prices t i)) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) =
      coordinate F g.impact (m.prices t i)
    rw [hq i]
  apply no_positive_crisis_of_radial_elasticity_ge_two_and_potential
    F g hF q k
  · intro i x hx
    have hxpos : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
    exact hdiff (F * Real.exp x) hxpos
  · intro i x hx
    obtain ⟨u, hu, heq⟩ := m.radial_log_price_attained
      F rho g edges hF i (hinit i) t ht
      (q i) (hq i) x hx
    rw [← heq]
    exact hel u ⟨hu.1, hu.2.trans ht.2⟩ i
  · rw [hlog]
    exact hpotential

end MarketCrash
