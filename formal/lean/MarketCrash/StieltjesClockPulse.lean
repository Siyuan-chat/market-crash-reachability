import MarketCrash.PhysicalPulse
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
Physical marginal-dollar flows under an arbitrary Stieltjes execution clock.

A `FlowCompletedPulse` solves the *physical* price/share/dollar equations
in cumulative executed dollars. Composing the complete operational-dollar
flow with a monotone right-continuous Stieltjes clock includes clocks having
absolutely continuous, singular-continuous, and atomic components.

The resulting coordinate identity at EVERY pair of physical-time endpoints
is PROVED from the physical operational-dollar ODE and the fundamental theorem
of calculus. In particular it is not a postulated coordinate chain rule.
At atoms, the intervening operational-dollar path supplies an explicitly
flow-completed jump rather than an incorrect endpoint block-price rule.

SCOPE: a single edge's trade-only subflow. This module does NOT prove the
weak physical price-response equation with simultaneous resilience, or the
model-equivalence of arbitrary mixed-edge BV paths under M1--M5.
-/
noncomputable section
namespace MarketCrash

open MeasureTheory

/-- The physical marginal-dollar ODE implies an exact *arbitrary subinterval*
coordinate response, not merely the full pulse endpoint formula. -/
theorem FlowCompletedPulse.coordinate_between
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (p : FlowCompletedPulse F g edges) (hF : 0 < F)
    (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) p.mass)
    (hv : v ∈ Set.Icc (0 : ℝ) p.mass)
    (huv : u ≤ v) (i : ι) :
    coordinate F g.impact (p.prices v i) -
      coordinate F g.impact (p.prices u i) =
      (v - u) * pairedMatrix edges i p.edge := by
  have hFTC :
      (∫ x in u..v, pairedMatrix edges i p.edge) =
        coordinate F g.impact (p.prices v i) -
          coordinate F g.impact (p.prices u i) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => coordinate F g.impact (p.prices x i))
      (f' := fun _ : ℝ => pairedMatrix edges i p.edge)
      (a := u) (b := v)
      (fun x hx => p.coordinate_hasDerivAt F g edges hF x
        (by
          have hxy : x ∈ Set.Icc u v := by
            simpa only [Set.uIcc_of_le huv] using hx
          exact ⟨hu.1.trans hxy.1, hxy.2.trans hv.2⟩) i)
      intervalIntegrable_const
  have hc :
      (∫ x in u..v, pairedMatrix edges i p.edge) =
        (v - u) * pairedMatrix edges i p.edge := by
    simp
  rw [hc] at hFTC
  exact hFTC.symm

/-- Signed marginal-dollar settlement has the same arbitrary-subinterval
increment, independently of how an external physical-time clock runs. -/
theorem FlowCompletedPulse.ledger_between
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (p : FlowCompletedPulse F g edges)
    (u v : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) p.mass)
    (hv : v ∈ Set.Icc (0 : ℝ) p.mass)
    (huv : u ≤ v) (i : ι) :
    p.dollarLedger v i - p.dollarLedger u i =
      (v - u) * pairedMatrix edges i p.edge := by
  have hFTC :
      (∫ x in u..v, pairedMatrix edges i p.edge) =
        p.dollarLedger v i - p.dollarLedger u i := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x => p.dollarLedger x i)
      (f' := fun _ : ℝ => pairedMatrix edges i p.edge)
      (a := u) (b := v)
      (fun x hx => p.ledger_flow x
        (by
          have hxy : x ∈ Set.Icc u v := by
            simpa only [Set.uIcc_of_le huv] using hx
          exact ⟨hu.1.trans hxy.1, hxy.2.trans hv.2⟩) i)
      intervalIntegrable_const
  have hc :
      (∫ x in u..v, pairedMatrix edges i p.edge) =
        (v - u) * pairedMatrix edges i p.edge := by
    simp
  rw [hc] at hFTC
  exact hFTC.symm

/-- A real-clock realization of one physically solved dollar-flow pulse.
The monotone right-continuous Stieltjes clock is allowed to be singular
continuous or to have atoms; its increment equals the pulse's dollar mass. -/
structure StieltjesClockPulse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  pulse : FlowCompletedPulse F g edges
  cumulative : StieltjesFunction
  a : ℝ
  b : ℝ
  time_order : a ≤ b
  mass_eq_delta : pulse.mass = cumulative b - cumulative a

/-- Dollar amount actually executed since the start of the time window. -/
def StieltjesClockPulse.executedDollars
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges) (t : ℝ) : ℝ :=
  m.cumulative t - m.cumulative m.a

/-- Physical prices sampled at the executed-dollar position. -/
def StieltjesClockPulse.prices
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges) (t : ℝ) (i : ι) : ℝ :=
  m.pulse.prices (m.executedDollars t) i

/-- Physical shares sampled at the same executed-dollar position. -/
def StieltjesClockPulse.shares
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges) (t : ℝ) (i : ι) : ℝ :=
  m.pulse.shares (m.executedDollars t) i

/-- Physical executed-dollar ledger sampled at the same clock. -/
def StieltjesClockPulse.dollarLedger
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges) (t : ℝ) (i : ι) : ℝ :=
  m.pulse.dollarLedger (m.executedDollars t) i

/-- Actual Lebesgue--Stieltjes mass over the half-open interval (s,t]. -/
def StieltjesClockPulse.intervalMass
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges) (s t : ℝ) : ℝ :=
  (m.cumulative.measure (Set.Ioc s t)).toReal

theorem StieltjesClockPulse.dollar_clock_mem
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
    m.executedDollars t ∈ Set.Icc (0 : ℝ) m.pulse.mass := by
  constructor
  · exact sub_nonneg.mpr (m.cumulative.mono ht.1)
  · change m.cumulative t - m.cumulative m.a ≤ m.pulse.mass
    rw [m.mass_eq_delta]
    exact sub_le_sub_right (m.cumulative.mono ht.2) _

theorem StieltjesClockPulse.positive_prices
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) (i : ι) :
    0 < m.prices t i :=
  m.pulse.positive_prices _ (m.dollar_clock_mem t ht) i

theorem StieltjesClockPulse.nonnegative_shares
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) (i : ι) :
    0 ≤ m.shares t i :=
  m.pulse.no_short_sales _ (m.dollar_clock_mem t ht) i

/-- Execution-share positions retain finite total variation even when
physical time has an atomic or singular-continuous execution clock.
This is inherited from bounded variation in operational dollars under
a monotone change of parameter. -/
theorem StieltjesClockPulse.finite_share_variation
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges) (i : ι) :
    BoundedVariationOn (fun t => m.shares t i) (Set.Icc m.a m.b) := by
  have hmono : MonotoneOn m.executedDollars (Set.Icc m.a m.b) := by
    intro x hx y hy hxy
    change m.cumulative x - m.cumulative m.a ≤
      m.cumulative y - m.cumulative m.a
    exact sub_le_sub_right (m.cumulative.mono hxy) _
  have hbound :
      eVariationOn (fun t => m.shares t i) (Set.Icc m.a m.b) ≤
        eVariationOn (fun u => m.pulse.shares u i)
          (Set.Icc (0 : ℝ) m.pulse.mass) := by
    simpa only [StieltjesClockPulse.shares, Function.comp_def] using
      (eVariationOn.comp_le_of_monotoneOn
        (fun u : ℝ => m.pulse.shares u i)
        m.executedDollars hmono (fun t ht => m.dollar_clock_mem t ht))
  exact ne_top_of_le_ne_top (m.pulse.finite_share_variation i) hbound

theorem StieltjesClockPulse.intervalMass_eq_delta
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : StieltjesClockPulse F g edges)
    (s t : ℝ) (hst : s ≤ t) :
    m.intervalMass s t = m.cumulative t - m.cumulative s := by
  unfold StieltjesClockPulse.intervalMass
  rw [StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (m.cumulative.mono hst))]

/-- The REAL Stieltjes executed-dollar mass induces the exact nonlinear
physical-price coordinate displacement on any physical-time subinterval.
There is no assumed differentiability of the clock. -/
theorem StieltjesClockPulse.coordinate_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : StieltjesClockPulse F g edges) (hF : 0 < F)
    (s t : ℝ) (hs : s ∈ Set.Icc m.a m.b)
    (ht : t ∈ Set.Icc m.a m.b) (hst : s ≤ t) (i : ι) :
    coordinate F g.impact (m.prices t i) =
      coordinate F g.impact (m.prices s i) +
        m.intervalMass s t * pairedMatrix edges i m.pulse.edge := by
  have hclock : m.executedDollars s ≤ m.executedDollars t := by
    unfold StieltjesClockPulse.executedDollars
    exact sub_le_sub_right (m.cumulative.mono hst) _
  have hphysical := m.pulse.coordinate_between F g edges hF
    (m.executedDollars s) (m.executedDollars t)
    (m.dollar_clock_mem s hs) (m.dollar_clock_mem t ht) hclock i
  change coordinate F g.impact (m.prices t i) -
    coordinate F g.impact (m.prices s i) =
      (m.executedDollars t - m.executedDollars s) *
        pairedMatrix edges i m.pulse.edge at hphysical
  rw [m.intervalMass_eq_delta s t hst]
  unfold StieltjesClockPulse.executedDollars at hphysical
  nlinarith [hphysical]

/-- Marginal-dollar ledger displacement uses precisely the same real
Stieltjes interval mass as the nonlinear price response. -/
theorem StieltjesClockPulse.ledger_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : StieltjesClockPulse F g edges)
    (s t : ℝ) (hs : s ∈ Set.Icc m.a m.b)
    (ht : t ∈ Set.Icc m.a m.b) (hst : s ≤ t) (i : ι) :
    m.dollarLedger t i = m.dollarLedger s i +
      m.intervalMass s t * pairedMatrix edges i m.pulse.edge := by
  have hclock : m.executedDollars s ≤ m.executedDollars t := by
    unfold StieltjesClockPulse.executedDollars
    exact sub_le_sub_right (m.cumulative.mono hst) _
  have hphysical := m.pulse.ledger_between F g edges
    (m.executedDollars s) (m.executedDollars t)
    (m.dollar_clock_mem s hs) (m.dollar_clock_mem t ht) hclock i
  change m.dollarLedger t i - m.dollarLedger s i =
    (m.executedDollars t - m.executedDollars s) *
      pairedMatrix edges i m.pulse.edge at hphysical
  rw [m.intervalMass_eq_delta s t hst]
  unfold StieltjesClockPulse.executedDollars at hphysical
  nlinarith [hphysical]

/-- Along this physically generated Stieltjes trade-only subflow, aggregate
generalized price is conserved, even for singular clocks and completed jumps. -/
theorem StieltjesClockPulse.potential_preserved
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : StieltjesClockPulse F g edges) (hF : 0 < F)
    (s t : ℝ) (hs : s ∈ Set.Icc m.a m.b)
    (ht : t ∈ Set.Icc m.a m.b) (hst : s ≤ t) :
    potential (fun i => coordinate F g.impact (m.prices t i)) =
      potential (fun i => coordinate F g.impact (m.prices s i)) := by
  unfold potential
  calc
    (∑ i, coordinate F g.impact (m.prices t i)) =
        ∑ i, (coordinate F g.impact (m.prices s i) +
          m.intervalMass s t * pairedMatrix edges i m.pulse.edge) := by
            apply Finset.sum_congr rfl
            intro i _
            exact m.coordinate_increment F g edges hF s t hs ht hst i
    _ = (∑ i, coordinate F g.impact (m.prices s i)) +
        m.intervalMass s t * (∑ i, pairedMatrix edges i m.pulse.edge) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i, coordinate F g.impact (m.prices s i) := by
          simp [paired_column_sum]

end MarketCrash
