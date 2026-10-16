import MarketCrash.HybridClosure

/-!
Endpoint price positivity for the finite hybrid execution subclass.

This does not establish positivity at every intermediate point of a
flow-completed pulse. That stronger statement still requires a pulse
parameterization and a domain-preservation proof.
-/
noncomputable section
namespace MarketCrash

/-- An elementary hybrid step ends at strictly positive prices. -/
theorem hybrid_step_target_positive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F)
    {S T : ι → ℝ} (step : HybridStep F rho g edges S T) :
    ∀ i, 0 < T i := by
  cases step with
  | recovery lam hS hlam0 hlam1 hT =>
      intro i
      rw [hT i]
      rcases eq_or_lt_of_le hlam0 with hzero | hpositive
      · subst lam
        simpa using hF
      · exact add_pos_of_nonneg_of_pos
          (mul_nonneg (sub_nonneg.mpr hlam1) hF.le)
          (mul_pos hpositive (hS i))
  | pairedPulse dollars hS hT hdollars hCoord =>
      exact hT
  | smooth seg a b hab hStart hEnd =>
      intro i
      rw [← hEnd i]
      exact seg.positive b i

/-- Every endpoint of a finite hybrid execution path remains positive
    when its initial price vector is positive. -/
theorem hybrid_reachable_target_positive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F)
    {S T : ι → ℝ} (path : HybridReachable F rho g edges S T)
    (hS : ∀ i, 0 < S i) :
    ∀ i, 0 < T i := by
  induction path with
  | refl => exact hS
  | append previous nextStep ih =>
      exact hybrid_step_target_positive F rho g edges hF nextStep

end MarketCrash
