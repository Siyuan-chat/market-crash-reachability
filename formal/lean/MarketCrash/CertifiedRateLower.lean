import MarketCrash.QuadraticRate

noncomputable section
namespace MarketCrash

/-- A rational uniform majorant; no numerical enclosure of exp(-16) is used. -/
theorem certifiedRateLower_coefficient (A d z : ℝ)
    (hA0 : 0 ≤ A) (hA : A ≤ 441/4000) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hz : 0 ≤ z) :
    A^2*(d-z+d^2/(2*(1-A*d)^2)) < 1/50 := by
  have hb : A*d ≤ 441/4000 := (mul_le_mul_of_nonneg_left hd1 hA0).trans (by simpa using hA)
  have hbase : 0 < 1-A*d := by linarith
  have hden : 2*(1-(441/4000:ℝ))^2 ≤ 2*(1-A*d)^2 := by nlinarith [sq_nonneg (1-A*d-(1-(441/4000:ℝ)))]
  have hden0 : 0 < 2*(1-(441/4000:ℝ))^2 := by norm_num
  have hfrac : d^2/(2*(1-A*d)^2) ≤ 1/(2*(1-(441/4000:ℝ))^2) := by
    calc
      _ ≤ 1/(2*(1-A*d)^2) := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le hden0 hden
  have hsum : d-z+d^2/(2*(1-A*d)^2) ≤ 1+1/(2*(1-(441/4000:ℝ))^2) := by linarith
  have hAsq : A^2 ≤ (441/4000:ℝ)^2 := by nlinarith
  calc
    _ ≤ A^2*(1+1/(2*(1-(441/4000:ℝ))^2)) := mul_le_mul_of_nonneg_left hsum (sq_nonneg A)
    _ ≤ (441/4000:ℝ)^2*(1+1/(2*(1-(441/4000:ℝ))^2)) :=
      mul_le_mul_of_nonneg_right hAsq (by positivity)
    _ < 1/50 := by norm_num

/-- Every actual paired AC session below .0441 misses the .020 crisis threshold,
for every coverage order and every finite directed network. -/
theorem certifiedRateLower_actual_session {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (v : ℝ)
    (hv : m.RateBounded v) (hcap : v ≤ 441/10000)
    (ha : m.a = 0) (hb : m.b = 40)
    (hF : ∀ i,m.F i = 1) (hρ : ∀ i,m.rho i = 2/5)
    (hg : ∀ i x,0 < x → (m.response i).impact x = 1)
    (h0 : ∀ i,m.prices 0 i = 1) (k : ℕ) :
    systemicCrisis (logPriceFromBenchmark 1 (m.prices 40)) k < 1/50 := by
  let A : ℝ := (5/2)*v
  let d : ℝ := 1-Real.exp (-16)
  have hA0 : 0 ≤ A := mul_nonneg (by norm_num) hv.1
  have hA : A ≤ 441/4000 := by dsimp [A];linarith
  have hd0 : 0 ≤ d := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have hd1 : d ≤ 1 := by dsimp [d];linarith [Real.exp_pos (-16)]
  have hz : 0 ≤ (16:ℝ)*Real.exp (-16) := by positivity
  have hsmall : 1*v/(1*(2/5))*(1-Real.exp (-(2/5)*m.b)) < 1 := by
    rw [hb]
    norm_num
    have he : v/(2/5:ℝ) = A := by dsimp [A];ring
    rw [he]
    exact (mul_le_mul_of_nonneg_left hd1 hA0).trans_lt (by simpa using (show A < 1 by linarith))
  have hu := theorem_6_2_original_upper m 1 (2/5) 1 v (by norm_num) (by norm_num) (by norm_num)
    hv ha hF hρ hg h0 hsmall k
  rw [hb] at hu
  have hu' : systemicCrisis (logPriceFromBenchmark 1 (m.prices 40)) k ≤
      A^2*(d-16*Real.exp (-16)+d^2/(2*(1-A*d)^2)) := by
    convert hu using 1 <;> dsimp [A,d] <;> norm_num <;> ring
  exact hu'.trans_lt (certifiedRateLower_coefficient A d _ hA0 hA hd0 hd1 hz)

theorem certifiedRateLower_actual_necessary {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (v : ℝ)
    (hv : m.RateBounded v) (ha : m.a = 0) (hb : m.b = 40)
    (hF : ∀ i,m.F i = 1) (hρ : ∀ i,m.rho i = 2/5)
    (hg : ∀ i x,0 < x → (m.response i).impact x = 1)
    (h0 : ∀ i,m.prices 0 i = 1) (k : ℕ)
    (hcrisis : 1/50 ≤ systemicCrisis (logPriceFromBenchmark 1 (m.prices 40)) k) :
    441/10000 < v := by
  by_contra h
  have hh := certifiedRateLower_actual_session m v hv (le_of_not_gt h) ha hb hF hρ hg h0 k
  linarith

/-- Applies to any nonempty actual feasible-cap set after proving its necessary
cap inequality; the explicit margin controls the infimum as well as each member. -/
theorem certifiedRateLower_infimum_margin (S : Set ℝ) (hne : S.Nonempty)
    (hnecessary : ∀ v ∈ S, (441/10000 : ℝ) < v) :
    (441/10000 : ℝ) ≤ sInf S ∧ (44/1000 : ℝ) < sInf S := by
  have hl : (441/10000 : ℝ) ≤ sInf S := le_csInf hne (fun v hv => (hnecessary v hv).le)
  exact ⟨hl,lt_of_lt_of_le (by norm_num) hl⟩

end MarketCrash
