import MarketCrash.StieltjesAtomicGaps
import MarketCrash.AdmissiblePathBarrier

/-!
# Physical completion of a single Stieltjes atomic edge

A mathematical jump in an executed-dollar Stieltjes control has an actual
singleton executed-dollar mass, determined by the Stieltjes measure rather
than by a postulated discrete trade size.

For an edge whose physical marginal price/share/ledger flow is given,
the COMPLETE flow through its interior (not naive endpoint pricing)
corresponds to exactly this measure atom. The flow explicitly requires
strictly positive internal prices and nonnegative executed-share inventory.

The structure does not assert that any arbitrary atomic trade volume has
a viable physical flow: positivity and inventory feasibility remain real
constraints. Simultaneous edge atoms are not claimed to commute.
-/

noncomputable section
namespace MarketCrash

/-- One genuinely marginal-settled physical pulse, with dollar mass equal
to an ACTUAL singleton Stieltjes executed-dollar measure atom. -/
structure AtomicEdgeCompletion
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ) where
  edge : κ
  pulse : FlowCompletedPulse F g edges
  matching_edge : pulse.edge = edge
  matching_mass : pulse.mass = exec.atomicMass edge atTime

/-- The nonlinear physical marginal-dollar flow at the atom has a price
coordinate increment equal to actual Stieltjes singleton dollar mass. -/
theorem AtomicEdgeCompletion.coordinate_endpoint_atom
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    (p : AtomicEdgeCompletion F g edges exec atTime)
    (hF : 0 < F) (i : ι) :
    coordinate F g.impact (p.pulse.prices p.pulse.mass i) =
      coordinate F g.impact (p.pulse.prices 0 i) +
        ((exec.cumulative p.edge).measure {atTime}).toReal *
          pairedMatrix edges i p.edge := by
  have h := p.pulse.coordinate_endpoint F g edges hF i
  rw [p.matching_edge, p.matching_mass,
    exec.atomicMass_eq_measure p.edge atTime] at h
  exact h

/-- The SAME singleton dollar mass drives the asset's physical signed
executed-dollar ledger, not just its transformed price state. -/
theorem AtomicEdgeCompletion.ledger_endpoint_atom
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    (p : AtomicEdgeCompletion F g edges exec atTime) (i : ι) :
    p.pulse.dollarLedger p.pulse.mass i =
      p.pulse.dollarLedger 0 i +
        ((exec.cumulative p.edge).measure {atTime}).toReal *
          pairedMatrix edges i p.edge := by
  have h := p.pulse.ledger_endpoint F g edges i
  rw [p.matching_edge, p.matching_mass,
    exec.atomicMass_eq_measure p.edge atTime] at h
  exact h

/-- Every intermediate operational point of the atom's marginal flow
has a positive physical price and feasible nonnegative share inventory. -/
theorem AtomicEdgeCompletion.internal_feasibility
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    (p : AtomicEdgeCompletion F g edges exec atTime)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) p.pulse.mass) (i : ι) :
    0 < p.pulse.prices a i ∧ 0 ≤ p.pulse.shares a i :=
  ⟨p.pulse.positive_prices a ha i, p.pulse.no_short_sales a ha i⟩

/-- An actual, flow-completed Stieltjes measure atom preserves aggregate
transformed price potential because its executed dollar flow is paired. -/
theorem AtomicEdgeCompletion.potential_preserved
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    (p : AtomicEdgeCompletion F g edges exec atTime)
    (hF : 0 < F) :
    potential (fun i => coordinate F g.impact
      (p.pulse.prices p.pulse.mass i)) =
      potential (fun i => coordinate F g.impact
        (p.pulse.prices 0 i)) := by
  unfold potential
  calc
    (∑ i, coordinate F g.impact (p.pulse.prices p.pulse.mass i)) =
        ∑ i, (coordinate F g.impact (p.pulse.prices 0 i) +
          ((exec.cumulative p.edge).measure {atTime}).toReal *
            pairedMatrix edges i p.edge) := by
      apply Finset.sum_congr rfl
      intro i _
      exact p.coordinate_endpoint_atom F g edges exec atTime hF i
    _ = (∑ i, coordinate F g.impact (p.pulse.prices 0 i)) +
        ((exec.cumulative p.edge).measure {atTime}).toReal *
          ∑ i, pairedMatrix edges i p.edge := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = ∑ i, coordinate F g.impact (p.pulse.prices 0 i) := by
      simp [paired_column_sum]

end MarketCrash
