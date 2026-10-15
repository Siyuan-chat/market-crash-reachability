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

end MarketCrash
