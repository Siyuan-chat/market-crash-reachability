import MarketCrash.Conservation

noncomputable section
namespace MarketCrash
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def starEdges (hub : ι) (e : {i : ι // i ≠ hub} × Bool) : PairedEdge ι :=
  if e.2 then ⟨hub, e.1, e.1.property.symm⟩ else ⟨e.1, hub, e.1.property⟩

def starDollars (u : ι → ℝ) (hub : ι) (e : {i : ι // i ≠ hub} × Bool) : ℝ :=
  if e.2 then max (u e.1) 0 else max (-u e.1) 0

omit [Fintype ι] [DecidableEq ι] in
theorem starDollars_nonnegative (u : ι → ℝ) (hub : ι)
    (e : {i : ι // i ≠ hub} × Bool) : 0 ≤ starDollars u hub e := by
  dsimp [starDollars]
  split <;> exact le_max_right _ _

theorem star_input_nonhub (u : ι → ℝ) (hub i : ι) (hi : i ≠ hub) :
    tradingInput (pairedMatrix (starEdges hub)) (starDollars u hub) i = u i := by
  classical
  have he : ∀ x : {j : ι // j ≠ hub},
      pairedMatrix (starEdges hub) i (x, true) * starDollars u hub (x, true) +
      pairedMatrix (starEdges hub) i (x, false) * starDollars u hub (x, false) =
        if x = ⟨i, hi⟩ then u i else 0 := by
    intro x
    by_cases hx : x = ⟨i, hi⟩
    · subst x
      simp [starEdges, starDollars, pairedMatrix, hi]
      rcases le_total 0 (u i) with hu | hu
      · rw [max_eq_left hu, max_eq_right (neg_nonpos.mpr hu)]
        ring
      · rw [max_eq_right hu, max_eq_left (neg_nonneg.mpr hu)]
        ring
    · have hxi : i ≠ (x : ι) := fun h => hx (Subtype.ext h.symm)
      simp [starEdges, starDollars, pairedMatrix, hi, hxi, hx]
  simp only [tradingInput, Fintype.sum_prod_type, Fintype.sum_bool]
  simp_rw [he]
  simp

theorem star_input (u : ι → ℝ) (hub : ι) (hu : ∑ i, u i = 0) (i : ι) :
    tradingInput (pairedMatrix (starEdges hub)) (starDollars u hub) i = u i := by
  by_cases hi : i ≠ hub
  · exact star_input_nonhub u hub i hi
  · have hie : i = hub := not_ne_iff.mp hi
    subst i
    let out := tradingInput (pairedMatrix (starEdges hub)) (starDollars u hub)
    have htail : (∑ i ∈ Finset.univ.erase hub, out i) = ∑ i ∈ Finset.univ.erase hub, u i := by
      apply Finset.sum_congr rfl
      intro j hj
      exact star_input_nonhub u hub j (Finset.mem_erase.mp hj).1
    have hz := paired_trading_sum_zero (starEdges hub) (starDollars u hub)
    change (∑ j, out j) = 0 at hz
    have ho := Finset.sum_erase_add Finset.univ out (Finset.mem_univ hub)
    have hh := Finset.sum_erase_add Finset.univ u (Finset.mem_univ hub)
    rw [htail, hz] at ho
    rw [hu] at hh
    dsimp [out] at ho
    linarith

end MarketCrash
