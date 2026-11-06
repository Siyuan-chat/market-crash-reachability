import MarketCrash.OriginalABC

/-!
V14-R1, `thm:sublinear-severe`: preliminary algebraic dependencies ONLY.
This file does not prove uniform turnover/inventory budgets or the full
universally quantified severe-reachability theorem. Those proof obligations
remain OPEN in formal/V14_RESULT_MANIFEST.md.
-/

noncomputable section
namespace MarketCrashV14

open MarketCrash

/-- For any fixed exponent p < 1, the generalized radial power
    nu = 2-p is strictly above one. -/
theorem sublinear_radial_exponent_gt_one (p : ℝ) (hp : p < 1) :
    1 < 2 - p := by
  linarith

/-- Algebraic dollar pairing on a normalized generalized radial direction.
Taking w_i = u_i^(1-p) and sum_i u_i^(2-p) = 1 recovers the
continuous-control pairing identity used by the manuscript. This
algebraic lemma alone does not establish admissible path existence. -/
theorem normalized_radial_flow_pairing
    {ι : Type*} [Fintype ι] (u w : ι → ℝ)
    (hunit : ∑ i, u i * w i = 1) :
    (∑ i, w i * ((∑ j, w j) * u i - 1)) = 0 := by
  classical
  calc
    _ = ∑ i, ((∑ j, w j) * (u i * w i) - w i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ j, w j) * (∑ i, u i * w i) - (∑ i, w i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 0 := by rw [hunit]; ring

#print axioms MarketCrashV14.sublinear_radial_exponent_gt_one
#print axioms MarketCrashV14.normalized_radial_flow_pairing

end MarketCrashV14
