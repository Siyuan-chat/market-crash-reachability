import MarketCrash.BoundedVariationLedger
import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
Stieltjes measure realization of matched-dollar cumulative execution.

Each directed edge has a monotone right-continuous cumulative
executed-dollar function. Its genuine Stieltjes measure accommodates
absolutely continuous, singular continuous and atomic (jump) components.
The half-open interval mass is the exact dollar increment.

These facts are the measure-level TRANSACTION ACCOUNTING layer. A proof
of the nonlinear physical price response's continuous-BV chain rule,
including singular trading and Marcus-completed jumps, is still pending.
-/
noncomputable section
namespace MarketCrash

open MeasureTheory

/-- A finite paired network of globally monotone, right-continuous
cumulative dollar-execution functions. -/
structure StieltjesPairedExecution
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) where
  cumulative : κ → StieltjesFunction

/-- Actual dollar mass of edge e executed during (a,b], according to
the associated Stieltjes measure (without a differentiability premise). -/
def StieltjesPairedExecution.intervalMass
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (a b : ℝ) : ℝ :=
  ((exec.cumulative e).measure (Set.Ioc a b)).toReal

/-- Stieltjes interval mass agrees exactly with the cumulative-dollar
difference for nonnegative time intervals. -/
theorem StieltjesPairedExecution.intervalMass_eq_delta
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (a b : ℝ) (hab : a ≤ b) :
    exec.intervalMass e a b =
      (exec.cumulative e) b - (exec.cumulative e) a := by
  unfold StieltjesPairedExecution.intervalMass
  rw [StieltjesFunction.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ((exec.cumulative e).mono hab))]

/-- A real executed-dollar amount on an ordered interval is nonnegative. -/
theorem StieltjesPairedExecution.intervalMass_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (a b : ℝ) (hab : a ≤ b) :
    0 ≤ exec.intervalMass e a b := by
  rw [exec.intervalMass_eq_delta e a b hab]
  exact sub_nonneg.mpr ((exec.cumulative e).mono hab)

/-- Executed dollar increments are additive on adjacent half-open
intervals. No density with respect to Lebesgue measure is needed. -/
theorem StieltjesPairedExecution.intervalMass_add
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c) :
    exec.intervalMass e a c =
      exec.intervalMass e a b + exec.intervalMass e b c := by
  rw [exec.intervalMass_eq_delta e a c (hab.trans hbc),
      exec.intervalMass_eq_delta e a b hab,
      exec.intervalMass_eq_delta e b c hbc]
  ring

/-- Dollar ledger of each asset for the Stieltjes edge masses. -/
def StieltjesPairedExecution.intervalLedger
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (a b : ℝ) (i : ι) : ℝ :=
  tradingInput (pairedMatrix edges) (fun e => exec.intervalMass e a b) i

/-- The sum of all signed executed dollars is zero on any time
interval, including any singular-continuous or atomic execution. -/
theorem StieltjesPairedExecution.intervalLedger_sum_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (a b : ℝ) :
    (∑ i, exec.intervalLedger a b i) = 0 := by
  change (∑ i, tradingInput (pairedMatrix edges)
    (fun e => exec.intervalMass e a b) i) = 0
  exact paired_trading_sum_zero edges _

/-- For ordered endpoints, the interval ledger is the same linear
combination of *actual cumulative dollar changes* as in M4. -/
theorem StieltjesPairedExecution.intervalLedger_eq_cumulative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (a b : ℝ) (hab : a ≤ b) (i : ι) :
    exec.intervalLedger a b i =
      tradingInput (pairedMatrix edges)
        (fun e => (exec.cumulative e) b - (exec.cumulative e) a) i := by
  unfold StieltjesPairedExecution.intervalLedger tradingInput
  apply Finset.sum_congr rfl
  intro e _
  change pairedMatrix edges i e * exec.intervalMass e a b =
    pairedMatrix edges i e *
      ((exec.cumulative e) b - (exec.cumulative e) a)
  rw [exec.intervalMass_eq_delta e a b hab]

end MarketCrash
