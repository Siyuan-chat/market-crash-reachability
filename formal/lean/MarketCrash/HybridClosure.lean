import MarketCrash.HybridPath

/-!
Finite path closure for the explicitly restricted hybrid market model.

The stage-by-stage positivity invariant extends by induction to any finite
chain of smooth segments, exact recovery steps and paired-dollar pulse
endpoints. The paths here are a rigorously specified subclass, not a
formalization of arbitrary bounded-variation execution with within-pulse
flow completion and exact individual terminal ledgers.
-/
noncomputable section
namespace MarketCrash

/-- Reflexive/transitive closure of the finite hybrid execution steps. -/
inductive HybridReachable
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) :
    (ι → ℝ) → (ι → ℝ) → Prop where
  | refl (S : ι → ℝ) : HybridReachable F rho g edges S S
  | append {S U T : ι → ℝ}
      (previous : HybridReachable F rho g edges S U)
      (nextStep : HybridStep F rho g edges U T) :
      HybridReachable F rho g edges S T

/-- Nonnegative potential is preserved by every finite hybrid path. -/
theorem hybrid_reachable_preserves_nonnegative_potential
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    {S T : ι → ℝ} (path : HybridReachable F rho g edges S T)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (S i))) :
    0 ≤ potential (fun i => coordinate F g.impact (T i)) := by
  induction path with
  | refl => exact hstart
  | append previous nextStep ih =>
      exact hybrid_step_preserves_nonnegative_potential
        F rho g edges hF hrho hdiff hel nextStep ih

/-- On the explicitly finite hybrid class, no admissible endpoint
can put every asset below F when elasticity is at least one. -/
theorem hybrid_not_all_below_benchmark
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i)
    (path : HybridReachable F rho g edges (fun _ => F) T) :
    ¬ ∀ i, T i < F := by
  have hstart : 0 ≤ potential (fun _ : ι => coordinate F g.impact F) := by
    simp [potential, coordinate_at_benchmark]
  have hfinal : 0 ≤ potential (fun i => coordinate F g.impact (T i)) :=
    hybrid_reachable_preserves_nonnegative_potential
      F rho g edges hF hrho hdiff hel path hstart
  exact not_all_below_benchmark F g hF T hT hfinal

/-- The matching all-breadth crisis barrier for the explicitly finite
hybrid market subclass, not a claim about all original BV controls. -/
theorem hybrid_systemic_crisis_nonpositive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S)
    (T : ι → ℝ) (path : HybridReachable F rho g edges (fun _ => F) T)
    (q : ι → ℝ) (hq : ∀ i, T i = F * Real.exp (q i))
    (k : ℕ) :
    systemicCrisis q k ≤ 0 := by
  have hel1 : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S := by
    intro S hS
    linarith [hel S hS]
  have hstart : 0 ≤ potential (fun _ : ι => coordinate F g.impact F) := by
    simp [potential, coordinate_at_benchmark]
  have hfinal : 0 ≤ potential (fun i => coordinate F g.impact (T i)) :=
    hybrid_reachable_preserves_nonnegative_potential
      F rho g edges hF hrho hdiff hel1 path hstart
  have hlog : (∑ i, logCoordinate F g.impact (q i)) =
      potential (fun i => coordinate F g.impact (T i)) := by
    unfold potential
    apply Finset.sum_congr rfl
    intro i _
    change coordinate F g.impact (F * Real.exp (q i)) =
      coordinate F g.impact (T i)
    rw [hq i]
  have hpotQ : 0 ≤ (∑ i, logCoordinate F g.impact (q i)) := by
    rw [hlog]
    exact hfinal
  exact no_positive_crisis_of_elasticity_ge_two_and_potential
    F g hF hdiff hel q k hpotQ

end MarketCrash
