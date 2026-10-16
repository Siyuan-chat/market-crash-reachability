import MarketCrash.Curvature

/-!
Fixed-benchmark systemic-crisis functional, in log-price coordinates.

q_i = log(S_i/F), so individual log loss is -q_i.
The coverage parameter k must lie in 1..card ι in the intended usage.
No claim about admissible paths is made here.
-/
noncomputable section
namespace MarketCrash
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Cross-sectional mean log loss from a common benchmark. -/
def meanLogLoss (q : ι → ℝ) : ℝ :=
  -(∑ i, q i) / (Fintype.card ι : ℝ)

/-- Greatest loss level attained by at least k assets (for 1 ≤ k ≤ N). -/
noncomputable def coverageQuantile (q : ι → ℝ) (k : ℕ) : ℝ := by
  classical
  exact sSup {x : ℝ | k ≤ (Finset.univ.filter (fun i : ι => x ≤ -q i)).card}

/-- Systemic crash functional: min of mean log loss and coverage quantile. -/
def systemicCrisis (q : ι → ℝ) (k : ℕ) : ℝ :=
  min (meanLogLoss q) (coverageQuantile q k)

theorem systemicCrisis_le_meanLogLoss (q : ι → ℝ) (k : ℕ) :
    systemicCrisis q k ≤ meanLogLoss q := by
  exact min_le_left _ _

theorem no_positive_crisis_of_nonnegative_log_sum (q : ι → ℝ) (k : ℕ)
    (hsum : 0 ≤ ∑ i, q i) : systemicCrisis q k ≤ 0 := by
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hmean : meanLogLoss q ≤ 0 := by
    unfold meanLogLoss
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsum) hn
  exact (systemicCrisis_le_meanLogLoss q k).trans hmean

end MarketCrash
