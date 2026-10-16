import MarketCrash.AdmissiblePathBarrier
import Mathlib.Algebra.Order.Floor.Ring

/-!
Exact parameter/log-price bridge for the paper's systemic drawdown
definition: k = ceil(alpha*N), 0 < alpha <= 1, and
log(F/S_i) = -log(S_i/F).

No claim of equivalence between *all* BV paths and the regular physical
path subclass is made by these endpoint identities.
-/
noncomputable section
namespace MarketCrash

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Paper's coverage count k = ceil(alpha*N). -/
def requiredAssetCount (alpha : ℝ) : ℕ :=
  ⌈alpha * (Fintype.card ι : ℝ)⌉₊

theorem requiredAssetCount_pos (alpha : ℝ) (hpos : 0 < alpha) :
    0 < requiredAssetCount (ι := ι) alpha := by
  unfold requiredAssetCount
  have hn : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  exact Nat.ceil_pos.mpr (mul_pos hpos hn)

theorem requiredAssetCount_le_card (alpha : ℝ) (hle : alpha ≤ 1) :
    requiredAssetCount (ι := ι) alpha ≤ Fintype.card ι := by
  unfold requiredAssetCount
  apply Nat.ceil_le.mpr
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hn]

theorem requiredAssetCount_valid (alpha : ℝ)
    (hpos : 0 < alpha) (hle : alpha ≤ 1) :
    1 ≤ requiredAssetCount (ι := ι) alpha ∧
      requiredAssetCount (ι := ι) alpha ≤ Fintype.card ι := by
  constructor
  · have hp := requiredAssetCount_pos (ι := ι) alpha hpos
    omega
  · exact requiredAssetCount_le_card (ι := ι) alpha hle

/-- The log-price vector from positive actual prices and common F. -/
def logPriceFromBenchmark (F : ℝ) (prices : ι → ℝ) : ι → ℝ :=
  fun i => Real.log (prices i / F)

/-- The individual log-loss vector used in Definition 2.1. -/
def actualLogLoss (F : ℝ) (prices : ι → ℝ) : ι → ℝ :=
  fun i => Real.log (F / prices i)

theorem actualLogLoss_eq_neg_logPrice (F : ℝ) (prices : ι → ℝ)
    (hF : 0 < F) (hS : ∀ i, 0 < prices i) (i : ι) :
    actualLogLoss F prices i = -logPriceFromBenchmark F prices i := by
  unfold actualLogLoss logPriceFromBenchmark
  rw [Real.log_div hF.ne' (hS i).ne', Real.log_div (hS i).ne' hF.ne']
  ring

theorem exp_logPrice_eq_price (F : ℝ) (prices : ι → ℝ)
    (hF : 0 < F) (hS : ∀ i, 0 < prices i) (i : ι) :
    F * Real.exp (logPriceFromBenchmark F prices i) = prices i := by
  unfold logPriceFromBenchmark
  rw [Real.exp_log (div_pos (hS i) hF)]
  field_simp [hF.ne']

theorem meanLogLoss_eq_actual (F : ℝ) (prices : ι → ℝ)
    (hF : 0 < F) (hS : ∀ i, 0 < prices i) :
    meanLogLoss (logPriceFromBenchmark F prices) =
      (∑ i, actualLogLoss F prices i) / (Fintype.card ι : ℝ) := by
  have hsum : (∑ i, actualLogLoss F prices i) =
      -(∑ i, logPriceFromBenchmark F prices i) := by
    calc
      (∑ i, actualLogLoss F prices i) =
          ∑ i, -logPriceFromBenchmark F prices i := by
            apply Finset.sum_congr rfl
            intro i _
            exact actualLogLoss_eq_neg_logPrice F prices hF hS i
      _ = -(∑ i, logPriceFromBenchmark F prices i) := by
            rw [Finset.sum_neg_distrib]
  unfold meanLogLoss
  rw [hsum]

/-- The regular-subclass 3.2 result instantiated with the ACTUAL
price-defined log coordinates and a valid alpha-based coverage count.
The remaining gap is equivalence to all manuscript BV admissible paths. -/
theorem admissible_regular_crisis_with_breadth
    {κ : Type*} [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AdmissibleMarketPath F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 2 ≤ responseElasticity g.impact S)
    (alpha : ℝ) (hpos : 0 < alpha) (hle : alpha ≤ 1) :
    (1 ≤ requiredAssetCount (ι := ι) alpha ∧
      requiredAssetCount (ι := ι) alpha ≤ Fintype.card ι) ∧
      systemicCrisis (logPriceFromBenchmark F m.terminal.prices)
        (requiredAssetCount (ι := ι) alpha) ≤ 0 := by
  refine ⟨requiredAssetCount_valid (ι := ι) alpha hpos hle, ?_⟩
  have hp : ∀ i, 0 < m.terminal.prices i :=
    physical_reachable_terminal_positive F rho g edges m.trace
      (fun i => by rw [m.initial_prices i]; exact hF)
  exact admissible_regular_no_systemic_crisis
    F rho g edges m hF hrho hdiff hel
    (logPriceFromBenchmark F m.terminal.prices)
    (fun i => (exp_logPrice_eq_price F m.terminal.prices hF hp i).symm)
    (requiredAssetCount (ι := ι) alpha)

end MarketCrash
