import MarketCrash.OrderedAtomicCompletion
import MarketCrash.AdmissiblePathBarrier

/-!
# Closed potential barriers under countable limits of physical prefixes

A BV control can have countably infinitely many atomic timestamps even in
a finite-horizon, finite-edge-dollar execution. Previously we proved
potential nonnegativity for finite, state-matched PHYSICAL execution
traces. Here we prove the genuine topological closure step for convergent
sequences of those finite-trace terminal prices.

This does not assert that EVERY M1--M5 BV execution has such approximants,
nor does it establish existence of their physical solutions, share
inventory feasibility, terminal dollar closure or the singular-continuous
nonatomic component. Those are distinct model-fidelity obligations.
-/

noncomputable section
namespace MarketCrash

open Filter

/-- Aggregate transformed price potential converges when every asset's
terminal price converges to a strictly POSITIVE limit. This uses the
genuine local derivative/continuity of the nonlinear response-adapted
price coordinate, not an assumed continuity postulate. -/
theorem physical_potential_tendsto_of_positive_price_limits
    {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (states : ℕ → ι → ℝ) (S : ι → ℝ)
    (hS : ∀ i, 0 < S i)
    (hlim : ∀ i, Tendsto (fun n => states n i) atTop (𝓝 (S i))) :
    Tendsto
      (fun n => potential (fun i => coordinate F g.impact (states n i)))
      atTop
      (𝓝 (potential (fun i => coordinate F g.impact (S i)))) := by
  change Tendsto (fun n => ∑ i, coordinate F g.impact (states n i))
      atTop (𝓝 (∑ i, coordinate F g.impact (S i)))
  apply tendsto_finset_sum
  intro i _
  exact ((coordinate_hasDerivAt F g hF (hS i)).continuousAt.tendsto).comp (hlim i)

/-- A NONNEGATIVE potential is preserved when passing from a sequence
of physically feasible finite-prefix terminal prices to a strictly
positive pointwise limit. This is the closed-cone step for arbitrary
countable concatenation, CONDITIONAL on convergence/positive limits. -/
theorem physical_potential_nonnegative_of_positive_prefix_limits
    {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F)
    (states : ℕ → ι → ℝ) (S : ι → ℝ)
    (hS : ∀ i, 0 < S i)
    (hlim : ∀ i, Tendsto (fun n => states n i) atTop (𝓝 (S i)))
    (hprefix : ∀ n, 0 ≤ potential
      (fun i => coordinate F g.impact (states n i))) :
    0 ≤ potential (fun i => coordinate F g.impact (S i)) := by
  have ht := physical_potential_tendsto_of_positive_price_limits
    F g hF states S hS hlim
  have hevent :
      ∀ᶠ n in atTop,
        (potential (fun i => coordinate F g.impact (states n i))) ∈
          Set.Ici (0 : ℝ) :=
    Filter.Eventually.of_forall (fun n => hprefix n)
  exact isClosed_Ici.mem_of_tendsto ht hevent

/-- Extension of the previously kernel-checked genuine PHYSICAL
finite-reachability potential barrier to the positive pointwise limit
of an arbitrary countable family of finite-prefix endpoints.

The statement quantifies over ACTUAL physical reachable traces at
every finite prefix: their trade and recovery equations and all
intermediate matching conditions were proved in Phase 1--4. -/
theorem physical_reachable_prefix_limit_potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (initial : PhysicalMarketState ι)
    (prefix : ℕ → PhysicalMarketState ι)
    (hpath : ∀ n, PhysicalMarketReachable F rho g edges
      initial (prefix n))
    (hstart : 0 ≤ potential
      (fun i => coordinate F g.impact (initial.prices i)))
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hlim : ∀ i, Tendsto (fun n => (prefix n).prices i) atTop (𝓝 (S i))) :
    0 ≤ potential (fun i => coordinate F g.impact (S i)) := by
  apply physical_potential_nonnegative_of_positive_prefix_limits
    F g hF (fun n i => (prefix n).prices i) S hS hlim
  intro n
  exact physical_reachable_preserves_potential
    F rho g edges hF hrho hdiff hel (hpath n) hstart

/-- A positive countable prefix limit of genuine finite physical market
executions cannot have EVERY asset strictly below the benchmark
under the global elasticity-1 barrier hypothesis. -/
theorem physical_reachable_prefix_limit_no_all_decline
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (initial : PhysicalMarketState ι)
    (prefix : ℕ → PhysicalMarketState ι)
    (hpath : ∀ n, PhysicalMarketReachable F rho g edges
      initial (prefix n))
    (hstart : 0 ≤ potential
      (fun i => coordinate F g.impact (initial.prices i)))
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hlim : ∀ i, Tendsto (fun n => (prefix n).prices i) atTop (𝓝 (S i))) :
    ¬ ∀ i, S i < F := by
  exact not_all_below_benchmark F g hF S hS
    (physical_reachable_prefix_limit_potential_nonnegative
      F rho g edges hF hrho hdiff hel initial prefix hpath
      hstart S hS hlim)

end MarketCrash
