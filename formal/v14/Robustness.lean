import MarketCrash.Conservation

/-!
V14-R1 `prop:heterogeneous-quadratic`: algebraic sublemmas only.
These do not prove the recovery-weighted comparison or the terminally
dollar-closed, two-pulse physical-price counterexample.
-/

noncomputable section
namespace MarketCrashV14

/-- The paper's weighted executed-dollar imbalance decomposes into the
unweighted dollar flow plus a response-heterogeneity term. -/
theorem weighted_flow_decomposition
    {ι : Type*} [Fintype ι] (κ x : ι → ℝ) (κbar : ℝ) :
    (∑ i, κ i * x i) =
      κbar * (∑ i, x i) + (∑ i, (κ i - κbar) * x i) := by
  classical
  calc
    _ = ∑ i, (κbar * x i + (κ i - κbar) * x i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = κbar * (∑ i, x i) + (∑ i, (κ i - κbar) * x i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Paired dollar rates alone need not have zero weighted sum when
impact strengths differ. This is only an *instantaneous* algebraic fact. -/
theorem paired_flow_can_have_positive_weighted_imbalance :
    ∃ κ₁ κ₂ x₁ x₂ : ℝ,
      0 < κ₂ ∧ κ₂ < κ₁ ∧ x₁ + x₂ = 0 ∧ 0 < κ₁ * x₁ + κ₂ * x₂ := by
  refine ⟨2, 1, 1, -1, ?_, ?_, ?_, ?_⟩ <;> norm_num

#print axioms MarketCrashV14.weighted_flow_decomposition
#print axioms MarketCrashV14.paired_flow_can_have_positive_weighted_imbalance

end MarketCrashV14
