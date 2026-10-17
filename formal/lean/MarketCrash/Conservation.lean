import MarketCrash.Definitions

noncomputable section
open Finset
namespace MarketCrash
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem paired_column_sum (edges : κ → PairedEdge ι) (e : κ) :
    (∑ i, pairedMatrix edges i e) = 0 := by
  simp [pairedMatrix, Finset.sum_sub_distrib]

theorem ones_transpose_paired (edges : κ → PairedEdge ι) (e : κ) :
    (∑ i, (1 : ℝ) * pairedMatrix edges i e) = 0 := by
  simpa using paired_column_sum edges e

theorem trading_sum_zero (B : ι → κ → ℝ) (hB : ∀ e, (∑ i, B i e) = 0)
    (rates : κ → ℝ) : (∑ i, tradingInput B rates i) = 0 := by
  simp only [tradingInput]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  simp [hB]

theorem paired_trading_sum_zero (edges : κ → PairedEdge ι) (rates : κ → ℝ) :
    (∑ i, tradingInput (pairedMatrix edges) rates i) = 0 :=
  trading_sum_zero _ (paired_column_sum edges) rates

theorem pulse_preserves_potential (edges : κ → PairedEdge ι)
    (y : ι → ℝ) (dollars : κ → ℝ) :
    potential (fun i => y i + tradingInput (pairedMatrix edges) dollars i) =
      potential y := by
  simp [potential, Finset.sum_add_distrib, paired_trading_sum_zero]

theorem normal_form_sum_derivative (edges : κ → PairedEdge ι)
    (y : ℝ → ι → ℝ) (rates : κ → ℝ) (R : ℝ → ℝ) (ρ t : ℝ)
    (hy : ∀ i, HasDerivAt (fun u => y u i)
      (tradingInput (pairedMatrix edges) rates i - ρ * R (y t i)) t) :
    HasDerivAt (fun u => potential (y u)) (-ρ * ∑ i, R (y t i)) t := by
  have h := HasDerivAt.sum (u := Finset.univ) (fun i _ => hy i)
  have heq : (∑ i, (tradingInput (pairedMatrix edges) rates i - ρ * R (y t i))) =
      -ρ * ∑ i, R (y t i) := by
    rw [Finset.sum_sub_distrib, paired_trading_sum_zero]
    simp [Finset.mul_sum]
  simpa [potential, heq] using h


/-- Proposition 7.5, instantaneous market cut: for any subset of assets,
dollar conservation and individual gross-dollar capacity bound the
absolute net flow across the cut by capacity on EITHER side.
This does not postulate any market-wide flow inequality. -/
theorem market_cut_instantaneous_bound
    (B : ι → κ → ℝ) (hB : ∀ e, (∑ i, B i e) = 0)
    (rates : κ → ℝ) (J : Finset ι)
    (S gross : ι → ℝ) (v : ℝ)
    (hv : 0 ≤ v) (hS : ∀ i, 0 ≤ S i)
    (hgross : ∀ i, 0 ≤ gross i ∧ gross i ≤ v)
    (hlocal : ∀ i,
      |tradingInput B rates i| ≤ S i * gross i) :
    |∑ i ∈ J, tradingInput B rates i| ≤
      v * min (∑ i ∈ J, S i)
        (∑ i ∈ Finset.univ \ J, S i) := by
  classical
  have hbound (K : Finset ι) :
      |∑ i ∈ K, tradingInput B rates i| ≤ v * ∑ i ∈ K, S i := by
    calc
      |∑ i ∈ K, tradingInput B rates i| ≤
          ∑ i ∈ K, |tradingInput B rates i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ K, S i * gross i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlocal i
      _ ≤ ∑ i ∈ K, S i * v := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hgross i).2 (hS i)
      _ = v * ∑ i ∈ K, S i := by
        rw [← Finset.sum_mul]
        simp only [mul_comm]
  have hzero : (∑ i, tradingInput B rates i) = 0 :=
    trading_sum_zero B hB rates
  have hcut : (∑ i ∈ J, tradingInput B rates i) =
      -(∑ i ∈ Finset.univ \ J, tradingInput B rates i) := by
    have hs := Finset.sum_sdiff
      (f := fun i => tradingInput B rates i) (Finset.subset_univ J)
    rw [← hs] at hzero
    linarith
  have hleft := hbound J
  have hright := hbound (Finset.univ \ J)
  have hmin : |∑ i ∈ J, tradingInput B rates i| ≤
      min (v * ∑ i ∈ J, S i)
        (v * ∑ i ∈ Finset.univ \ J, S i) := by
    apply le_min
    · exact hleft
    · rw [hcut, abs_neg]
      exact hright
  simpa only [mul_min_of_nonneg hv] using hmin

end MarketCrash
