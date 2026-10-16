import MarketCrash.ElasticityConcavity

/-!
A genuine exact-recovery invariant for finite recovery steps.

For the pure resilient-price relaxation S' = (1-λ)F + λ S,
0 ≤ λ ≤ 1, concavity yields H(S') ≥ λ H(S). Therefore H ≥ 0 is
preserved by exact recovery steps. This does NOT yet cover simultaneous
time-varying matched trading and recovery over an interval.
-/
noncomputable section
namespace MarketCrash

variable {ι : Type*} [Fintype ι]

/-- Pure recovery cannot reduce the aggregate generalized price coordinate
    below λ times its previous value when Φ is concave. -/
theorem recovery_step_potential_lower_bound
    (F : ℝ) (g : Response) (hF : 0 < F)
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (λ : ℝ) (hλ0 : 0 ≤ λ) (hλ1 : λ ≤ 1)
    (hConcave : ConcaveOn ℝ positivePrices (coordinate F g.impact)) :
    λ * potential (fun i => coordinate F g.impact (S i)) ≤
      potential (fun i => coordinate F g.impact ((1 - λ) * F + λ * S i)) := by
  have hsingle (i : ι) :
      λ * coordinate F g.impact (S i) ≤
        coordinate F g.impact ((1 - λ) * F + λ * S i) := by
    have hJ := hConcave.2 (x := F) hF (y := S i) (hS i)
      (a := 1 - λ) (b := λ) (sub_nonneg.mpr hλ1) hλ0 (by ring)
    simpa only [smul_eq_mul, coordinate_at_benchmark, mul_zero, zero_add] using hJ
  calc
    λ * potential (fun i => coordinate F g.impact (S i)) =
        ∑ i, λ * coordinate F g.impact (S i) := by simp [potential, Finset.mul_sum]
    _ ≤ ∑ i, coordinate F g.impact ((1 - λ) * F + λ * S i) := by
        apply Finset.sum_le_sum
        intro i _
        exact hsingle i
    _ = potential (fun i => coordinate F g.impact ((1 - λ) * F + λ * S i)) := rfl

/-- Nonnegative generalized-price potential is invariant under a
    finite exact recovery step if Φ is concave. -/
theorem recovery_step_preserves_nonnegative_potential
    (F : ℝ) (g : Response) (hF : 0 < F)
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (λ : ℝ) (hλ0 : 0 ≤ λ) (hλ1 : λ ≤ 1)
    (hConcave : ConcaveOn ℝ positivePrices (coordinate F g.impact))
    (hPotential : 0 ≤ potential (fun i => coordinate F g.impact (S i))) :
    0 ≤ potential (fun i => coordinate F g.impact ((1 - λ) * F + λ * S i)) := by
  exact (mul_nonneg hλ0 hPotential).trans
    (recovery_step_potential_lower_bound F g hF S hS λ hλ0 hλ1 hConcave)

/-- Elasticity ≥ 1 is enough for preservation under each exact recovery
    step, with no assumed concavity left in this result. -/
theorem recovery_step_preserves_potential_of_elasticity_ge_one
    (F : ℝ) (g : Response) (hF : 0 < F)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hElasticity : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (λ : ℝ) (hλ0 : 0 ≤ λ) (hλ1 : λ ≤ 1)
    (hPotential : 0 ≤ potential (fun i => coordinate F g.impact (S i))) :
    0 ≤ potential (fun i => coordinate F g.impact ((1 - λ) * F + λ * S i)) := by
  exact recovery_step_preserves_nonnegative_potential F g hF S hS
    λ hλ0 hλ1
    (coordinate_concaveOn_of_elasticity_ge_one F g hF hdiff hElasticity)
    hPotential

end MarketCrash
