import MarketCrash.AEAttainableBarrier
import MarketCrash.StieltjesAtomicGaps
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
    rw [m.potentialPrimitive_at_start]
    exact hstart
  have hbarrier : 0 ≤ H t :=
    nonnegative_of_derivative_ge_linear_on_Icc
      H slope rho m.a t ht.1 hd hb hstartH
  rw [m.potential_eq_primitive F rho g edges t ht]
  exact hbarrier

end MarketCrash
