import MarketCrash.AtomicFlowCompletion

/-!
# Chronologically ordered completion of simultaneous Stieltjes atoms

A finite collection of atomic directed-edge dollars at one physical
timestamp cannot be treated as a single endpoint block-price settlement.
This typed trace executes each edge via its ACTUAL nonlinear marginal
price/share/ledger flow, one at a time, matching all physical state
fields between successive pulses.

The `used` Finset ensures no directed edge is executed twice. A trace
whose `used` set is all edges executes precisely one physical pulse per
edge with an atom mass equal to the original singleton Stieltjes measure.
Order is explicit in the trace, not silently chosen or presumed commute.

A trace is supplied as physically feasible data: this module does not
prove existence for every control, and it does not cover infinitely many
time atoms or the singular-continuous nonatomic component.
-/

noncomputable section
namespace MarketCrash

/-- Ordered completion of a fixed-time multi-edge atomic event. A physical
pulse has to be feasible throughout its internal execution. -/
inductive OrderedAtomicJumpTrace
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ) :
    PhysicalMarketState ι → PhysicalMarketState ι → Finset κ → Prop where
  | refl (s : PhysicalMarketState ι) :
      OrderedAtomicJumpTrace F g edges exec atTime s s ∅
  | append {s mid : PhysicalMarketState ι} {used : Finset κ}
      (previous : OrderedAtomicJumpTrace F g edges exec atTime s mid used)
      (p : AtomicEdgeCompletion F g edges exec atTime)
      (fresh : p.edge ∉ used)
      (match_time : mid.time = atTime)
      (match_prices : mid.prices = p.pulse.prices 0)
      (match_shares : mid.shares = p.pulse.shares 0)
      (match_ledger : mid.dollars = p.pulse.dollarLedger 0) :
      OrderedAtomicJumpTrace F g edges exec atTime s
        ⟨atTime, p.pulse.prices p.pulse.mass,
          p.pulse.shares p.pulse.mass, p.pulse.dollarLedger p.pulse.mass⟩
        (insert p.edge used)

/-- The price response's sum of normalized coordinates is unchanged
across ANY finite ordered set of physically feasible Stieltjes atoms. -/
theorem OrderedAtomicJumpTrace.potential_preserved
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    (hF : 0 < F)
    {s t : PhysicalMarketState ι} {used : Finset κ}
    (trace : OrderedAtomicJumpTrace F g edges exec atTime s t used) :
    potential (fun i => coordinate F g.impact (t.prices i)) =
      potential (fun i => coordinate F g.impact (s.prices i)) := by
  induction trace with
  | refl => rfl
  | @append s mid used previous p fresh match_time match_prices
      match_shares match_ledger ih =>
      change potential (fun i => coordinate F g.impact
        (p.pulse.prices p.pulse.mass i)) =
        potential (fun i => coordinate F g.impact (s.prices i))
      rw [p.potential_preserved F g edges exec atTime hF]
      have heq :
          potential (fun i => coordinate F g.impact (p.pulse.prices 0 i)) =
            potential (fun i => coordinate F g.impact (mid.prices i)) := by
        rw [match_prices]
      rw [heq]
      exact ih

/-- Incidence-weighted singleton Stieltjes dollar masses of precisely
the edges already completed in the ordered trace. -/
def StieltjesPairedExecution.usedAtomicLedger
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (atTime : ℝ) (used : Finset κ) (i : ι) : ℝ :=
  tradingInput (pairedMatrix edges)
    (fun e => if e ∈ used then exec.atomicMass e atTime else 0) i

/-- Insert one never-before-executed edge, adding exactly its physical
signed-dollar incidence to every asset's used-atom ledger. -/
theorem StieltjesPairedExecution.usedAtomicLedger_insert
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (atTime : ℝ) (used : Finset κ) (e : κ)
    (hfresh : e ∉ used) (i : ι) :
    exec.usedAtomicLedger atTime (insert e used) i =
      exec.usedAtomicLedger atTime used i +
        pairedMatrix edges i e * exec.atomicMass e atTime := by
  unfold StieltjesPairedExecution.usedAtomicLedger tradingInput
  calc
    (∑ x, pairedMatrix edges i x *
        (if x ∈ insert e used then exec.atomicMass x atTime else 0)) =
        ∑ x, (pairedMatrix edges i x *
          (if x ∈ used then exec.atomicMass x atTime else 0) +
          (if x = e then pairedMatrix edges i e *
            exec.atomicMass e atTime else 0)) := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x = e
      · subst x
        simp [hfresh]
      · simp [Finset.mem_insert, hx]
    _ = (∑ x, pairedMatrix edges i x *
          (if x ∈ used then exec.atomicMass x atTime else 0)) +
          pairedMatrix edges i e * exec.atomicMass e atTime := by
      rw [Finset.sum_add_distrib]
      simp

/-- Every physical asset's ACTUAL ledger increment equals its signed
incidence weighted total of the atomic-dollar edge flows already executed,
not merely the net market-wide dollar sum. -/
theorem OrderedAtomicJumpTrace.ledger_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    {s t : PhysicalMarketState ι} {used : Finset κ}
    (trace : OrderedAtomicJumpTrace F g edges exec atTime s t used)
    (i : ι) :
    t.dollars i - s.dollars i =
      exec.usedAtomicLedger atTime used i := by
  induction trace with
  | refl =>
      simp [StieltjesPairedExecution.usedAtomicLedger, tradingInput]
  | @append s mid used previous p fresh match_time match_prices
      match_shares match_ledger ih =>
      change p.pulse.dollarLedger p.pulse.mass i - s.dollars i =
        exec.usedAtomicLedger atTime (insert p.edge used) i
      have hp := p.pulse.ledger_endpoint F g edges i
      rw [p.matching_edge, p.matching_mass] at hp
      have hstep : p.pulse.dollarLedger p.pulse.mass i =
          mid.dollars i +
            exec.atomicMass p.edge atTime * pairedMatrix edges i p.edge := by
        rw [match_ledger]
        exact hp
      calc
        p.pulse.dollarLedger p.pulse.mass i - s.dollars i =
            (mid.dollars i - s.dollars i) +
              pairedMatrix edges i p.edge * exec.atomicMass p.edge atTime := by
          rw [hstep]
          ring
        _ = exec.usedAtomicLedger atTime used i +
              pairedMatrix edges i p.edge * exec.atomicMass p.edge atTime := by
          rw [ih]
        _ = exec.usedAtomicLedger atTime (insert p.edge used) i :=
          (exec.usedAtomicLedger_insert atTime used p.edge fresh i).symm

/-- A fully executed ordered co-jump (each edge used exactly once)
realizes the original input Stieltjes singleton masses in every
physical per-asset ledger, independently of the chosen feasible order. -/
theorem OrderedAtomicJumpTrace.full_atom_ledger
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (exec : StieltjesPairedExecution edges) (atTime : ℝ)
    {s t : PhysicalMarketState ι} {used : Finset κ}
    (trace : OrderedAtomicJumpTrace F g edges exec atTime s t used)
    (hall : used = Finset.univ) (i : ι) :
    t.dollars i - s.dollars i =
      tradingInput (pairedMatrix edges)
        (fun e => ((exec.cumulative e).measure {atTime}).toReal) i := by
  rw [trace.ledger_increment F g edges exec atTime i]
  simp only [StieltjesPairedExecution.usedAtomicLedger, hall,
    Finset.mem_univ, ite_true]
  unfold tradingInput
  apply Finset.sum_congr rfl
  intro e _
  rw [exec.atomicMass_eq_measure e atTime]

end MarketCrash
