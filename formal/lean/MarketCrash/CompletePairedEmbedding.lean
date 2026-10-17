import MarketCrash.Conservation

noncomputable section
namespace MarketCrash
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

abbrev CompleteEdgeIndex (ι : Type*) := {p : ι × ι // p.1 ≠ p.2}

def completePairedEdges (e : CompleteEdgeIndex ι) : PairedEdge ι :=
  ⟨e.1.1, e.1.2, e.2⟩

def pairedEdgeIndex (e : PairedEdge ι) : CompleteEdgeIndex ι :=
  ⟨(e.seller,e.buyer), e.distinct⟩

def embedPairedDollars (edges : κ → PairedEdge ι) (z : κ → ℝ)
    (e : CompleteEdgeIndex ι) : ℝ := ∑ k, if pairedEdgeIndex (edges k) = e then z k else 0

theorem embedPairedDollars_nonnegative (edges : κ → PairedEdge ι) (z : κ → ℝ)
    (hz : ∀ k, 0 ≤ z k) (e : CompleteEdgeIndex ι) : 0 ≤ embedPairedDollars edges z e := by
  apply Finset.sum_nonneg
  intro k _
  split <;> simp_all

theorem embedPairedDollars_input (edges : κ → PairedEdge ι) (z : κ → ℝ) (i : ι) :
    tradingInput (pairedMatrix completePairedEdges) (embedPairedDollars edges z) i =
      tradingInput (pairedMatrix edges) z i := by
  simp only [tradingInput, embedPairedDollars, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_eq_single (pairedEdgeIndex (edges k))]
  · simp [pairedMatrix, pairedEdgeIndex, completePairedEdges]
  · intro e _ he
    simp [Ne.symm he]
  · simp

theorem embedPairedDollars_turnover (edges : κ → PairedEdge ι) (z : κ → ℝ) :
    (∑ e, embedPairedDollars edges z e) = ∑ k, z k := by
  simp only [embedPairedDollars]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp

end MarketCrash
