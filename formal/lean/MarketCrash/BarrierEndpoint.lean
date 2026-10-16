import MarketCrash.CrisisFunctional
import Mathlib.Analysis.Convex.Jensen

/-!
Conditional endpoint lemmas toward Theorems 3.1 and 3.2 (V12 Final).

Nonnegative potential and concavity are still ASSUMED here, rather than
derived from admissible market trajectories and elasticity. Compiling this
module must not be presented as a complete proof of Theorem 3.1 or 3.2.
-/
noncomputable section
namespace MarketCrash
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A nonnegative aggregate potential forbids all prices below F. -/
theorem not_all_below_benchmark (F : ℝ) (g : Response) (hF : 0 < F)
    (S : ι → ℝ) (hS : ∀ i, 0 < S i)
    (hPotential : 0 ≤ potential (fun i => coordinate F g.impact (S i))) :
    ¬ ∀ i, S i < F := by
  intro hall
  have hi (i : ι) : coordinate F g.impact (S i) < 0 := by
    have hs : S i ∈ positivePrices := hS i
    have hf : F ∈ positivePrices := hF
    have h := (coordinate_strictMonoOn F g hF) hs hf (hall i)
    simpa only [coordinate_at_benchmark] using h
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hsum : (∑ i, coordinate F g.impact (S i)) < (0 : ℝ) := by
    have hlt : (∑ i, coordinate F g.impact (S i)) < (∑ i : ι, (0 : ℝ)) := by
      apply Finset.sum_lt_sum
      · intro i _
        exact (hi i).le
      · exact ⟨i₀, Finset.mem_univ _, hi i₀⟩
    simpa using hlt
  have hnonneg : 0 ≤ (∑ i, coordinate F g.impact (S i)) := by
    simpa only [potential] using hPotential
  exact (not_lt_of_ge hnonneg) hsum

/-- Monotonicity of the price coordinate when composed with log prices. -/
theorem logCoordinate_strictMono (F : ℝ) (g : Response) (hF : 0 < F) :
    StrictMono (logCoordinate F g.impact) := by
  intro x y hxy
  have hx : F * Real.exp x ∈ positivePrices :=
    mul_pos hF (Real.exp_pos x)
  have hy : F * Real.exp y ∈ positivePrices :=
    mul_pos hF (Real.exp_pos y)
  have hlt := mul_lt_mul_of_pos_left (Real.exp_strictMono hxy) hF
  change coordinate F g.impact (F * Real.exp x) <
    coordinate F g.impact (F * Real.exp y)
  exact (coordinate_strictMonoOn F g hF) hx hy hlt

/-- Finite Jensen implication for a concave, increasing normalized potential. -/
theorem nonnegative_log_sum_of_concave_potential
    (G : ℝ → ℝ) (q : ι → ℝ)
    (hConcave : ConcaveOn ℝ Set.univ G)
    (hMono : StrictMono G) (hZero : G 0 = 0)
    (hPotential : 0 ≤ ∑ i, G (q i)) :
    0 ≤ ∑ i, q i := by
  let n : ℝ := Fintype.card ι
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
  let w : ι → ℝ := fun _ => n⁻¹
  have hwNonneg : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := by
    intro _ _
    exact inv_nonneg.mpr hn.le
  have hwSum : (∑ i, w i) = 1 := by
    have hne : n ≠ 0 := ne_of_gt hn
    simp [w, n, Finset.sum_const, nsmul_eq_mul, hne]
  have hJensen : (∑ i, w i * G (q i)) ≤ G (∑ i, w i * q i) := by
    simpa only [smul_eq_mul] using
      (hConcave.le_map_sum (t := Finset.univ) (w := w) (p := q)
        hwNonneg hwSum (by intro i _; exact Set.mem_univ _))
  have hwG : (∑ i, w i * G (q i)) = n⁻¹ * (∑ i, G (q i)) := by
    simp [w, Finset.mul_sum]
  have hwQ : (∑ i, w i * q i) = n⁻¹ * (∑ i, q i) := by
    simp [w, Finset.mul_sum]
  have hweighted : 0 ≤ (∑ i, w i * G (q i)) := by
    rw [hwG]
    exact mul_nonneg (inv_nonneg.mpr hn.le) hPotential
  have hmean : 0 ≤ (∑ i, w i * q i) := by
    by_contra hbad
    have hlt : (∑ i, w i * q i) < 0 := lt_of_not_ge hbad
    have hstrict : G (∑ i, w i * q i) < 0 := by
      simpa only [hZero] using hMono hlt
    exact (not_lt_of_ge (hweighted.trans hJensen)) hstrict
  rw [hwQ] at hmean
  by_contra hbad
  have hlt : (∑ i, q i) < 0 := lt_of_not_ge hbad
  have hstrict := mul_neg_of_pos_of_neg (inv_pos.mpr hn) hlt
  exact (not_lt_of_ge hmean) hstrict

/-- Endpoint part of the systemic-crisis barrier, not its full dynamics. -/
theorem no_positive_crisis_of_concave_potential (G : ℝ → ℝ) (q : ι → ℝ)
    (k : ℕ) (hConcave : ConcaveOn ℝ Set.univ G)
    (hMono : StrictMono G) (hZero : G 0 = 0)
    (hPotential : 0 ≤ ∑ i, G (q i)) :
    systemicCrisis q k ≤ 0 := by
  exact no_positive_crisis_of_nonnegative_log_sum q k
    (nonnegative_log_sum_of_concave_potential G q hConcave hMono hZero hPotential)

end MarketCrash
