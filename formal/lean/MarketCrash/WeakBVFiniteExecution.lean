import MarketCrash.WeakBVPriceBarrier
import MarketCrash.AdmissiblePathBarrier

/-!
# Finite concatenation of continuous weak BV executions and real pulses

Paper M5 permits piecewise continuous execution of finite variation and
a finite number of exactly flow-completed marginal-price pulses. Here a
finite trace can concatenate:
* continuous, possibly singular-continuous, Stieltjes-dollar weak
  normal-form price solutions;
* genuine physical marginal-price/share/ledger pulse ODE solutions.

All physical-time and price-coordinate endpoints are IDENTICAL at
joins. We prove H>=0 for every such path under the local RADIAL
elasticity-1 premise on each continuous BV piece, and a localized
elasticity-2 endpoint systemic crisis barrier.

This model is weaker than a full M1--M5 admissible state system: it
does not track inter-stage inventory or exact per-asset ledger closure,
which are irrelevant to these structural exclusion conclusions.
Its price law remains the paper's integrated weak normal form; the
generic nonlinear continuous-BV chain rule deriving it from primitive
M2 marginal share-price settlement is still a separate proof obligation.
-/

noncomputable section
namespace MarketCrash

/-- Physical time and strictly positive candidate market price vector.
No inventory/ledger assertions are needed for a no-crash impossibility,
which is valid even in a larger price-only universe. -/
structure WeakBVPriceState (ι : Type*) where
  time : ℝ
  prices : ι → ℝ

/-- One genuine physical market step under the radial elasticity-1
hypothesis needed for the comparison theorem.

For continuous BV pieces, this hypothesis is restricted to the
benchmark-to-current-price intervals, NOT all positive S. Physical
pulses conserve potential regardless of the elasticity function. -/
inductive RadiallyElasticWeakBVPriceStep
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) :
    WeakBVPriceState ι → WeakBVPriceState ι → Prop where
  | continuous (seg : ContinuousWeakBVPriceSegment F rho g edges)
      (hel : ∀ t ∈ Set.Icc seg.a seg.b, ∀ i x,
        x ∈ Set.Icc (min F (seg.prices t i))
          (max F (seg.prices t i)) →
        1 ≤ responseElasticity g.impact x) :
      RadiallyElasticWeakBVPriceStep F rho g edges
        ⟨seg.a, seg.prices seg.a⟩
        ⟨seg.b, seg.prices seg.b⟩
  | smooth (seg : PhysicalSmoothSegment F rho g edges)
      (hel : ∀ t i u,
        u ∈ Set.Icc (min F (seg.prices t i)) (max F (seg.prices t i)) →
          1 ≤ responseElasticity g.impact u) :
      RadiallyElasticWeakBVPriceStep F rho g edges
        ⟨seg.a, seg.prices seg.a⟩
        ⟨seg.b, seg.prices seg.b⟩
  | pulse (atTime : ℝ) (p : FlowCompletedPulse F g edges) :
      RadiallyElasticWeakBVPriceStep F rho g edges
        ⟨atTime, p.prices 0⟩
        ⟨atTime, p.prices p.mass⟩

/-- Finite state-matched concatenation of true weak BV price segments
and flow-completed physical marginally executed pulses. -/
inductive RadiallyElasticWeakBVPriceReachable
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) :
    WeakBVPriceState ι → WeakBVPriceState ι → Prop where
  | refl (s : WeakBVPriceState ι) :
      RadiallyElasticWeakBVPriceReachable F rho g edges s s
  | append {s mid t : WeakBVPriceState ι}
      (prev : RadiallyElasticWeakBVPriceReachable
        F rho g edges s mid)
      (step : RadiallyElasticWeakBVPriceStep F rho g edges mid t) :
      RadiallyElasticWeakBVPriceReachable F rho g edges s t

/-- Each executed physical step preserves nonnegative aggregate
transformed price potential. The continuous BV case invokes the
proved true per-asset Stieltjes weak price law; the pulse case
uses its separately verified real nonlinear physical ODE. -/
theorem RadiallyElasticWeakBVPriceStep.potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    {s t : WeakBVPriceState ι}
    (step : RadiallyElasticWeakBVPriceStep F rho g edges s t)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (s.prices i))) :
    0 ≤ potential (fun i => coordinate F g.impact (t.prices i)) := by
  cases step with
  | continuous seg hel =>
      change 0 ≤ potential
        (fun i => coordinate F g.impact (seg.prices seg.a i)) at hstart
      change 0 ≤ potential
        (fun i => coordinate F g.impact (seg.prices seg.b i))
      exact seg.potential_nonnegative_of_radial_elasticity
        F rho g edges hF hrho hdiff hel hstart
        seg.b ⟨seg.time_order, le_rfl⟩
  | smooth seg hel =>
      change 0 ≤ potential
        (fun i => coordinate F g.impact (seg.prices seg.a i)) at hstart
      change 0 ≤ potential
        (fun i => coordinate F g.impact (seg.prices seg.b i))
      exact seg.potential_nonnegative_of_radial_elasticity
        F rho g edges hF hrho
        (fun t i u hu => hdiff u
          ((lt_min hF (seg.positive_prices t i)).trans_le hu.1))
        hel hstart
  | pulse atTime p =>
      change 0 ≤ potential (fun i => coordinate F g.impact (p.prices 0 i))
        at hstart
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
      rwa [heq]

/-- Strict positivity at the terminal state of every individually
physically feasible continuous weak BV segment or complete pulse. -/
theorem RadiallyElasticWeakBVPriceStep.positive_terminal
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    {s t : WeakBVPriceState ι}
    (step : RadiallyElasticWeakBVPriceStep F rho g edges s t) :
    ∀ i, 0 < t.prices i := by
  cases step with
  | continuous seg hel =>
      exact seg.positive_prices seg.b ⟨seg.time_order, le_rfl⟩
  | smooth seg hel =>
      exact seg.positive_prices seg.b
  | pulse atTime p =>
      exact p.positive_prices p.mass ⟨p.nonnegative_mass, le_rfl⟩

/-- The exact H>=0 barrier propagates through any FINITE
chronologically matched BV weak-price / physical-pulse execution. -/
theorem RadiallyElasticWeakBVPriceReachable.potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    {s t : WeakBVPriceState ι}
    (trace : RadiallyElasticWeakBVPriceReachable F rho g edges s t)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (s.prices i))) :
    0 ≤ potential (fun i => coordinate F g.impact (t.prices i)) := by
  induction trace with
  | refl => exact hstart
  | append prev step ih =>
      exact RadiallyElasticWeakBVPriceStep.potential_nonnegative
        F rho g edges hF hrho hdiff step ih

theorem RadiallyElasticWeakBVPriceReachable.positive_terminal
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    {s t : WeakBVPriceState ι}
    (trace : RadiallyElasticWeakBVPriceReachable F rho g edges s t)
    (hstart : ∀ i, 0 < s.prices i) :
    ∀ i, 0 < t.prices i := by
  induction trace with
  | refl => exact hstart
  | append prev step ih =>
      exact RadiallyElasticWeakBVPriceStep.positive_terminal
        F rho g edges step

/-- A finite, physically flow-completed Stieltjes BV path starting
from the benchmark, with radial elasticity >=1 on each continuous
segment, cannot end with all asset prices below benchmark F. -/
theorem RadiallyElasticWeakBVPriceReachable.no_all_asset_decline
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    {s t : WeakBVPriceState ι}
    (trace : RadiallyElasticWeakBVPriceReachable F rho g edges s t)
    (hinit : ∀ i, s.prices i = F) :
    ¬ ∀ i, t.prices i < F := by
  have hstart :
      0 ≤ potential (fun i => coordinate F g.impact (s.prices i)) := by
    simp [potential, hinit, coordinate_at_benchmark]
  have hterm :
      0 ≤ potential (fun i => coordinate F g.impact (t.prices i)) :=
    trace.potential_nonnegative F rho g edges hF hrho hdiff hstart
  have hp : ∀ i, 0 < t.prices i :=
    trace.positive_terminal F rho g edges (fun i => by rw [hinit i]; exact hF)
  exact not_all_below_benchmark F g hF t.prices hp hterm

/-- A finite BV weak-normal-form path with e>=1 radial on EVERY
continuous price state and e>=2 radial between F and each terminal
price satisfies the systemic-crisis exclusion at the terminal state,
for ANY k. This covers arbitrary singular CONTINUOUS BV controls and
any finite number of physically flow-completed pulses.

The remaining hypothesis linking original M1--M5 to the weak integrated
normal form is model-semantic, NOT a missing potential inequality. -/
theorem RadiallyElasticWeakBVPriceReachable.no_systemic_crisis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    {s t : WeakBVPriceState ι}
    (trace : RadiallyElasticWeakBVPriceReachable F rho g edges s t)
    (hinit : ∀ i, s.prices i = F)
    (q : ι → ℝ) (hq : ∀ i, t.prices i = F * Real.exp (q i))
    (hel2 : ∀ i x, x ∈ Set.Icc (min 0 (q i)) (max 0 (q i)) →
       2 ≤ responseElasticity g.impact (F * Real.exp x))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hstart :
      0 ≤ potential (fun i => coordinate F g.impact (s.prices i)) := by
    simp [potential, hinit, coordinate_at_benchmark]
  have hterminal :
      0 ≤ potential (fun i => coordinate F g.impact (t.prices i)) :=
    trace.potential_nonnegative F rho g edges hF hrho hdiff hstart
  have hlog :
      (∑ i, logCoordinate F g.impact (q i)) =
        potential (fun i => coordinate F g.impact (t.prices i)) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) =
      coordinate F g.impact (t.prices i)
    rw [hq i]
  apply no_positive_crisis_of_radial_elasticity_ge_two_and_potential
    F g hF q k
  · intro i x hx
    exact hdiff _ (mul_pos hF (Real.exp_pos x))
  · exact hel2
  · rw [hlog]
    exact hterminal

end MarketCrash
