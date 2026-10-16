import MarketCrash.ContinuousInvariant
import MarketCrash.RestoringTangent

/-!
Continuous smooth-market subcase of the structural barriers.

This file connects the genuinely derived elasticity/concavity bound with
a continuously differentiable, paired-dollar market normal form.
It covers trajectories smooth on the *whole real line*, and it does NOT yet
incorporate the paper's flow-completed instantaneous pulses, bounded
variation controls or weaker elasticity restrictions only on attainable
prices. It is not the complete original Theorem 3.1/3.2.
-/
noncomputable section
namespace MarketCrash

/-- An explicitly coupled smooth realization of the paper's
price / response-adapted coordinate normal form. -/
structure SmoothPairedTrajectory
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  prices : ℝ → ι → ℝ
  coordinates : ℝ → ι → ℝ
  rates : ℝ → κ → ℝ
  restoring : ℝ → ℝ
  positive : ∀ t i, 0 < prices t i
  coordinate_eq : ∀ t i,
    coordinates t i = coordinate F g.impact (prices t i)
  restoring_eq : ∀ t i,
    restoring (coordinates t i) =
      prices t i * (prices t i - F) / g.impact (prices t i)
  nonnegative_rates : ∀ t e, 0 ≤ rates t e
  benchmark_initial : ∀ i, prices 0 i = F
  normal_form : ∀ t i, HasDerivAt (fun u => coordinates u i)
    (tradingInput (pairedMatrix edges) (rates t) i -
      rho * restoring (coordinates t i)) t

/-- For smooth dollar-paired paths, the actual elasticity condition
implies nonnegative aggregate price potential at any t ≥ 0. Unlike
earlier conditional bridge lemmas, the restoring inequality is proved
from elasticity rather than assumed. -/
theorem smooth_potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : SmoothPairedTrajectory F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ potential (m.coordinates t) := by
  have hrestore (u : ℝ) :
      (∑ i, m.restoring (m.coordinates u i)) ≤
        potential (m.coordinates u) := by
    have hb := restoring_drain_sum_le_potential_of_elasticity_ge_one
      F g hF hdiff hel (m.prices u) (m.positive u)
    have hr : (∑ i, m.restoring (m.coordinates u i)) =
        (∑ i, m.prices u i * (m.prices u i - F) /
          g.impact (m.prices u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact m.restoring_eq u i
    have hcoord : potential (m.coordinates u) =
        potential (fun i => coordinate F g.impact (m.prices u i)) := by
      unfold potential
      apply Finset.sum_congr rfl
      intro i _
      exact m.coordinate_eq u i
    rw [hr, hcoord]
    exact hb
  have hzero : 0 ≤ potential (m.coordinates 0) := by
    have hz (i : ι) : m.coordinates 0 i = 0 := by
      rw [m.coordinate_eq 0 i, m.benchmark_initial i, coordinate_at_benchmark]
    simp [potential, hz]
  exact nonnegative_potential_of_normal_form edges m.coordinates m.rates
    m.restoring rho hrho m.normal_form hrestore hzero t ht

/-- A smooth, coupled resilient paired-dollar path cannot have every
asset strictly below F under elasticity at least one. -/
theorem smooth_not_all_prices_below
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : SmoothPairedTrajectory F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (t : ℝ) (ht : 0 ≤ t) :
    ¬ ∀ i, m.prices t i < F := by
  have hpot : 0 ≤ potential (m.coordinates t) :=
    smooth_potential_nonnegative F rho g edges m hF hrho hdiff hel t ht
  have heq : potential (fun i => coordinate F g.impact (m.prices t i)) =
      potential (m.coordinates t) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    exact (m.coordinate_eq t i).symm
  apply not_all_below_benchmark F g hF (m.prices t) (m.positive t)
  rw [heq]
  exact hpot

/-- A smooth coupled path has no positive systemic crisis at any breadth
when elasticity is globally at least two. Still not an impulsive-path theorem. -/
theorem smooth_systemic_crisis_nonpositive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : SmoothPairedTrajectory F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S)
    (t : ℝ) (ht : 0 ≤ t)
    (q : ι → ℝ) (hq : ∀ i, m.prices t i = F * Real.exp (q i))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hel1 : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S := by
    intro S hs
    linarith [hel S hs]
  have hpot : 0 ≤ potential (m.coordinates t) :=
    smooth_potential_nonnegative F rho g edges m hF hrho hdiff hel1 t ht
  have hrep : (∑ i, logCoordinate F g.impact (q i)) =
      potential (m.coordinates t) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) = m.coordinates t i
    rw [← hq i]
    exact (m.coordinate_eq t i).symm
  have hpotQ : 0 ≤ (∑ i, logCoordinate F g.impact (q i)) := by
    rw [hrep]
    exact hpot
  exact no_positive_crisis_of_elasticity_ge_two_and_potential
    F g hF hdiff hel q k hpotQ

end MarketCrash
