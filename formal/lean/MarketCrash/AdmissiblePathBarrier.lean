import MarketCrash.AdmissibleMarketPath
import MarketCrash.BarrierEndpoint

/-!
Structural crisis barriers derived from PHYSICAL execution paths,
for the finite regular admissible market subclass.

Notably, the pulse-coordinate law is invoked only after proving it from
the actual marginal price flow ODE and FTC in PhysicalPulse.lean; smooth
normal form is derived from the physical price/share equations in
PhysicalSmoothMarket.lean. The market-state ledger and inventory fields
are carried through every concatenation, and terminal dollar closure is
a recorded path requirement.

The result now includes physically derived joint multi-edge operational-clock
segments in addition to smooth physical-time paths and one-edge pulses.
It is NOT YET the whole BV Theorems 3.1/3.2: operational-time a.e.
regularity and faithful M1--M5 BV path inclusion are not established,
and the trace-level elasticity hypothesis remains global.
-/
noncomputable section
namespace MarketCrash

/-- A genuine physical market step preserves nonnegative potential.
The pulse case uses a proved FTC endpoint formula, not an assumed
coordinate update. -/
theorem physical_step_preserves_potential
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    {s t : PhysicalMarketState ι}
    (step : PhysicalMarketStep F rho g edges s t)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (s.prices i))) :
    0 ≤ potential (fun i => coordinate F g.impact (t.prices i)) := by
  cases step with
  | smooth seg =>
      change 0 ≤ potential (fun i => coordinate F g.impact (seg.prices seg.a i)) at hstart
      change 0 ≤ potential (fun i => coordinate F g.impact (seg.prices seg.b i))
      exact seg.potential_nonnegative F rho g edges hF hrho hdiff hel hstart
  | pulse atTime p =>
      change 0 ≤ potential (fun i => coordinate F g.impact (p.prices 0 i)) at hstart
      change 0 ≤ potential (fun i => coordinate F g.impact (p.prices p.mass i))
      have heq :
          potential (fun i => coordinate F g.impact (p.prices p.mass i)) =
            potential (fun i => coordinate F g.impact (p.prices 0 i)) := by
        unfold potential
        calc
          (∑ i, coordinate F g.impact (p.prices p.mass i)) =
              ∑ i, (coordinate F g.impact (p.prices 0 i) +
                p.mass * pairedMatrix edges i p.edge) := by
                  apply Finset.sum_congr rfl
                  intro i _
                  exact p.coordinate_endpoint F g edges hF i
          _ = (∑ i, coordinate F g.impact (p.prices 0 i)) +
              p.mass * ∑ i, pairedMatrix edges i p.edge := by
                  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ = ∑ i, coordinate F g.impact (p.prices 0 i) := by
                  simp [paired_column_sum]
      rw [heq]
      exact hstart
  | clocked seg =>
      change 0 ≤ potential (fun i => coordinate F g.impact (seg.prices seg.a i)) at hstart
      change 0 ≤ potential (fun i => coordinate F g.impact (seg.prices seg.b i))
      exact seg.potential_nonnegative F rho g edges hF hrho hdiff hel hstart

/-- Physical execution steps have strictly positive terminal prices.
Pulse positivity is a condition along the entire internal execution,
not just the terminal-price sign. -/
theorem physical_step_terminal_positive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    {s t : PhysicalMarketState ι}
    (step : PhysicalMarketStep F rho g edges s t) :
    ∀ i, 0 < t.prices i := by
  cases step with
  | smooth seg =>
      exact seg.positive_prices seg.b
  | pulse atTime p =>
      exact p.positive_prices p.mass
        ⟨p.nonnegative_mass, le_rfl⟩
  | clocked seg =>
      exact seg.positive_prices seg.b ⟨seg.order, le_rfl⟩

/-- Potential preservation by induction over finite physical execution
traces, including every physically flow-completed pulse. -/
theorem physical_reachable_preserves_potential
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    {s t : PhysicalMarketState ι}
    (path : PhysicalMarketReachable F rho g edges s t)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (s.prices i))) :
    0 ≤ potential (fun i => coordinate F g.impact (t.prices i)) := by
  induction path with
  | refl => exact hstart
  | append previous step ih =>
      exact physical_step_preserves_potential
        F rho g edges hF hrho hdiff hel step ih

theorem physical_reachable_terminal_positive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    {s t : PhysicalMarketState ι}
    (path : PhysicalMarketReachable F rho g edges s t)
    (hstart : ∀ i, 0 < s.prices i) :
    ∀ i, 0 < t.prices i := by
  induction path with
  | refl => exact hstart
  | append previous step ih =>
      exact physical_step_terminal_positive F rho g edges step

/-- The initial benchmark and the physically derived step invariants imply
H ≥ 0 for the entire finite regular admissible execution path. -/
theorem AdmissibleMarketPath.potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AdmissibleMarketPath F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S) :
    0 ≤ potential (fun i => coordinate F g.impact (m.terminal.prices i)) := by
  have hinitial :
      0 ≤ potential (fun i => coordinate F g.impact (m.initial.prices i)) := by
    simp [potential, m.initial_prices, coordinate_at_benchmark]
  exact physical_reachable_preserves_potential
    F rho g edges hF hrho hdiff hel m.trace hinitial

/-- Theorem 3.1 for the finite regular physical admissible subclass. -/
theorem admissible_regular_no_all_asset_decline
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AdmissibleMarketPath F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S) :
    ¬ ∀ i, m.terminal.prices i < F := by
  have hp : ∀ i, 0 < m.terminal.prices i :=
    physical_reachable_terminal_positive F rho g edges m.trace
      (fun i => by rw [m.initial_prices i]; exact hF)
  exact not_all_below_benchmark F g hF m.terminal.prices hp
    (m.potential_nonnegative F rho g edges hF hrho hdiff hel)

/-- Theorem 3.2 for the finite regular physical admissible subclass.
The supplied q is linked to actual positive terminal prices, rather
than postulating a nonnegative log-price sum. -/
theorem admissible_regular_no_systemic_crisis
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AdmissibleMarketPath F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S)
    (q : ι → ℝ) (hq : ∀ i, m.terminal.prices i = F * Real.exp (q i))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hel1 : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S := by
    intro S hs
    linarith [hel S hs]
  have hpotential : 0 ≤
      potential (fun i => coordinate F g.impact (m.terminal.prices i)) :=
    m.potential_nonnegative F rho g edges hF hrho hdiff hel1
  have hlog :
      (∑ i, logCoordinate F g.impact (q i)) =
        potential (fun i => coordinate F g.impact (m.terminal.prices i)) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) =
      coordinate F g.impact (m.terminal.prices i)
    rw [hq i]
  apply no_positive_crisis_of_elasticity_ge_two_and_potential
    F g hF hdiff hel q k
  rw [hlog]
  exact hpotential

end MarketCrash
