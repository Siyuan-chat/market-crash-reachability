import MarketCrash.PotentialFromTime
import MarketCrash.RestoringTangent

/-!
Finite concatenations of smooth market segments and exact paired-dollar
pulse endpoints, preserving the global H ≥ 0 barrier.

Each smooth segment is differentiable on the whole real line, and a pulse
is presently represented by its positive endpoints and proved coordinate
transfer identity. The model does *not* yet establish within-pulse
flow-completed positivity, general BV-path approximation, or terminal
individual signed-dollar ledgers. It is a rigorous intermediate hybrid
subclass, not the original paper's complete admissibility definition.
-/
noncomputable section
namespace MarketCrash

/-- A smooth paired-dollar/resilient segment, without requiring a fresh
benchmark initial state for each segment. -/
structure SmoothExecutionSegment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  prices : ℝ → ι → ℝ
  coordinates : ℝ → ι → ℝ
  rates : ℝ → κ → ℝ
  restoring : ℝ → ℝ
  positive : ∀ t i, 0 < prices t i
  coordinate_eq : ∀ t i,
    coordinates t i = coordinate F g.impact (prices t i)
  restoring_eq : ∀ t i, restoring (coordinates t i) =
    prices t i * (prices t i - F) / g.impact (prices t i)
  nonnegative_rates : ∀ t e, 0 ≤ rates t e
  normal_form : ∀ t i, HasDerivAt (fun u => coordinates u i)
    (tradingInput (pairedMatrix edges) (rates t) i -
      rho * restoring (coordinates t i)) t

/-- A smooth segment propagates the potential invariant between arbitrary
times a ≤ b, rather than requiring benchmark prices at a. -/
theorem smooth_segment_preserves_nonnegative_potential
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (seg : SmoothExecutionSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (a b : ℝ) (hab : a ≤ b)
    (hstart : 0 ≤ potential (seg.coordinates a)) :
    0 ≤ potential (seg.coordinates b) := by
  have hrestore (u : ℝ) :
      (∑ i, seg.restoring (seg.coordinates u i)) ≤
        potential (seg.coordinates u) := by
    have hb := restoring_drain_sum_le_potential_of_elasticity_ge_one
      F g hF hdiff hel (seg.prices u) (seg.positive u)
    have hr : (∑ i, seg.restoring (seg.coordinates u i)) =
        (∑ i, seg.prices u i * (seg.prices u i - F) /
          g.impact (seg.prices u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact seg.restoring_eq u i
    have hc : potential (seg.coordinates u) =
        potential (fun i => coordinate F g.impact (seg.prices u i)) := by
      unfold potential
      apply Finset.sum_congr rfl
      intro i _
      exact seg.coordinate_eq u i
    rw [hr, hc]
    exact hb
  exact nonnegative_potential_of_normal_form_from edges seg.coordinates
    seg.rates seg.restoring rho hrho seg.normal_form hrestore a b hab hstart

/-- Elementary hybrid market steps: exact pure recovery, a paired-dollar
pulse endpoint, or a smooth segment with actual coordinate dynamics. -/
inductive HybridStep
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) :
    (ι → ℝ) → (ι → ℝ) → Prop where
  | recovery (S T : ι → ℝ) (lam : ℝ)
      (hS : ∀ i, 0 < S i) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
      (hT : ∀ i, T i = (1 - lam) * F + lam * S i) :
      HybridStep F rho g edges S T
  | pairedPulse (S T : ι → ℝ) (dollars : κ → ℝ)
      (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
      (hdollars : ∀ e, 0 ≤ dollars e)
      (hCoord : ∀ i, coordinate F g.impact (T i) =
        coordinate F g.impact (S i) +
          tradingInput (pairedMatrix edges) dollars i) :
      HybridStep F rho g edges S T
  | smooth (S T : ι → ℝ)
      (seg : SmoothExecutionSegment F rho g edges)
      (a b : ℝ) (hab : a ≤ b)
      (hStart : ∀ i, seg.prices a i = S i)
      (hEnd : ∀ i, seg.prices b i = T i) :
      HybridStep F rho g edges S T

/-- Every elementary hybrid step preserves nonnegative market potential
under the global elasticity-1 assumption. -/
theorem hybrid_step_preserves_nonnegative_potential
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    {S T : ι → ℝ} (step : HybridStep F rho g edges S T)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (S i))) :
    0 ≤ potential (fun i => coordinate F g.impact (T i)) := by
  cases step with
  | recovery lam hS hlam0 hlam1 hT =>
      have h := recovery_step_preserves_potential_of_elasticity_ge_one
        F g hF hdiff hel S hS lam hlam0 hlam1 hstart
      have heq : potential (fun i => coordinate F g.impact (T i)) =
          potential (fun i => coordinate F g.impact ((1 - lam) * F + lam * S i)) := by
        unfold potential
        apply Finset.sum_congr rfl
        intro i _
        rw [hT i]
      rw [heq]
      exact h
  | pairedPulse dollars _ _ _ hCoord =>
      have heq : potential (fun i => coordinate F g.impact (T i)) =
          potential (fun i => coordinate F g.impact (S i) +
            tradingInput (pairedMatrix edges) dollars i) := by
        unfold potential
        apply Finset.sum_congr rfl
        intro i _
        exact hCoord i
      rw [heq, pulse_preserves_potential]
      exact hstart
  | smooth seg a b hab hStart hEnd =>
      have ha : 0 ≤ potential (seg.coordinates a) := by
        have heq : potential (seg.coordinates a) =
            potential (fun i => coordinate F g.impact (S i)) := by
          unfold potential
          apply Finset.sum_congr rfl
          intro i _
          rw [seg.coordinate_eq a i, hStart i]
        rw [heq]
        exact hstart
      have hb := smooth_segment_preserves_nonnegative_potential
        F rho g edges seg hF hrho hdiff hel a b hab ha
      have heq : potential (fun i => coordinate F g.impact (T i)) =
          potential (seg.coordinates b) := by
        unfold potential
        apply Finset.sum_congr rfl
        intro i _
        rw [seg.coordinate_eq b i, hEnd i]
      rw [heq]
      exact hb

end MarketCrash
