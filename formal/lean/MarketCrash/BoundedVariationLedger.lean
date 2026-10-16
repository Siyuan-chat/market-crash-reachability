import MarketCrash.Conservation
import Mathlib.Analysis.BoundedVariation

/-!
M4/M5 algebra for arbitrary finite-variation cumulative paired-dollar
execution, including continuous and singular-continuous flows.

This does NOT yet give the price response/Marcus chain rule along all
BV controls. It only derives exact dollar-ledger accounting and aggregate
zero-sum conservation without any differentiability hypothesis.
-/
noncomputable section
namespace MarketCrash

/-- A cumulative, nondecreasing, directed-edge executed-dollar control,
with finite variation on the chosen finite time interval. -/
structure BoundedVariationDollarControl
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (a b : ℝ) where
  cumulative : ℝ → κ → ℝ
  time_order : a ≤ b
  nondecreasing : ∀ e, MonotoneOn (fun t => cumulative t e) (Set.Icc a b)
  finite_variation : ∀ e, BoundedVariationOn (fun t => cumulative t e) (Set.Icc a b)

/-- Cumulative *executed* dollars since a; not inventory or share changes. -/
def BoundedVariationDollarControl.ledger
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {a b : ℝ}
    (control : BoundedVariationDollarControl edges a b) (t : ℝ) (i : ι) : ℝ :=
  tradingInput (pairedMatrix edges)
    (fun e => control.cumulative t e - control.cumulative a e) i

/-- Every directed edge executes a nonnegative dollar increment on [a,b]. -/
theorem BoundedVariationDollarControl.edge_increment_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {a b : ℝ}
    (control : BoundedVariationDollarControl edges a b)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (e : κ) :
    0 ≤ control.cumulative t e - control.cumulative a e := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, control.time_order⟩
  exact sub_nonneg.mpr (control.nondecreasing e ha ht ht.1)

/-- The per-asset dollar ledger begins at zero by construction. -/
theorem BoundedVariationDollarControl.ledger_at_start
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {a b : ℝ}
    (control : BoundedVariationDollarControl edges a b) (i : ι) :
    control.ledger a i = 0 := by
  simp [BoundedVariationDollarControl.ledger, tradingInput]

/-- All paired-dollar cumulative controls (including singular BV controls)
have zero aggregate executed-dollar ledger, without a derivative premise. -/
theorem BoundedVariationDollarControl.total_ledger_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {a b : ℝ}
    (control : BoundedVariationDollarControl edges a b) (t : ℝ) :
    (∑ i, control.ledger t i) = 0 := by
  change (∑ i, tradingInput (pairedMatrix edges)
    (fun e => control.cumulative t e - control.cumulative a e) i) = 0
  exact paired_trading_sum_zero edges _

/-- Ledger increments depend only on endpoint differences of cumulative
edge execution, not on the regularity of the intervening dollar flow. -/
theorem BoundedVariationDollarControl.ledger_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {a b : ℝ}
    (control : BoundedVariationDollarControl edges a b)
    (u v : ℝ) (i : ι) :
    control.ledger v i - control.ledger u i =
      tradingInput (pairedMatrix edges)
        (fun e => control.cumulative v e - control.cumulative u e) i := by
  unfold BoundedVariationDollarControl.ledger tradingInput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Strong terminal dollar-closure remains a separate *per-asset*
condition; aggregate zero-sum alone does not imply it. -/
def BoundedVariationDollarControl.TerminallyClosed
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {a b : ℝ}
    (control : BoundedVariationDollarControl edges a b) : Prop :=
  ∀ i, control.ledger b i = 0

end MarketCrash
