import MarketCrash.QuadraticRate
import MarketCrash.FiniteRateConstruction
import MarketCrash.ResponseFamilies

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Original AC economics with the actual same execution carrying the gross
cap, holdings, terminal per-asset dollar closure and fixed benchmark bands. -/
def OriginalRateFeasible (F rho T alpha betaMinus betaPlus : ℝ) (g : Response)
    (H : ι → ℝ) (v delta : ℝ) : Prop :=
  ∃ (m : ACPhysicalSession (completePairedEdges (ι := ι)))
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) completePairedEdges),
    m.a = 0 ∧ m.b = T ∧ m.F = (fun _ => F) ∧ m.rho = (fun _ => rho) ∧ m.response = (fun _ => g) ∧
    (∀ i, m.prices 0 i = F) ∧ RealizesACSession m P ∧ m.RateBounded v ∧
    P.initial.shares = H ∧ P.terminal.time = T ∧ P.terminal.prices = m.prices T ∧
    (∀ i x, P.trace.Visited i x → F*(1-betaMinus) ≤ x ∧ x ≤ F*(1+betaPlus)) ∧
    delta ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) alpha)

def minimumOriginalRate (F rho T alpha betaMinus betaPlus : ℝ) (g : Response)
    (H : ι → ℝ) (delta : ℝ) : ℝ :=
  sInf {v | OriginalRateFeasible F rho T alpha betaMinus betaPlus g H v delta}

theorem OriginalRateFeasible.rate_nonnegative (F rho T alpha betaMinus betaPlus : ℝ)
    (g : Response) (H : ι → ℝ) (v delta : ℝ)
    (h : OriginalRateFeasible F rho T alpha betaMinus betaPlus g H v delta) : 0 ≤ v := by
  obtain ⟨m,P,_,_,_,_,_,_,_,hv,_⟩ := h
  exact hv.1

theorem OriginalRateFeasible.raise_cap (F rho T alpha betaMinus betaPlus : ℝ)
    (g : Response) (H : ι → ℝ) (v w delta : ℝ)
    (h : OriginalRateFeasible F rho T alpha betaMinus betaPlus g H v delta) (hvw : v ≤ w) :
    OriginalRateFeasible F rho T alpha betaMinus betaPlus g H w delta := by
  obtain ⟨m,P,ha,hb,hF,hr,hg,h0,hreal,hv,hrest⟩ := h
  refine ⟨m,P,ha,hb,hF,hr,hg,h0,hreal,⟨hv.1.trans hvw,?_⟩,hrest⟩
  filter_upwards [hv.2] with t ht hmem i
  exact (ht hmem i).trans hvw

theorem constant_rate_attainment_family (hN : 2 ≤ Fintype.card ι)
    (F rho eta T alpha betaMinus betaPlus : ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hT : 0 < T)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hbM : 0 < betaMinus) (hbP : 0 < betaPlus)
    (H : ι → ℝ) (hH : ∀ i, 0 < H i) :
    ∃ eps c C : ℝ, 0 < eps ∧ 0 < c ∧ 0 < C ∧ ∀ a : ℝ, 0 < a → a < eps →
      OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H (C*a) (c*a^2) := by
  have hg : ContDiffAt ℝ 3 (constantResponse eta he).impact F := contDiffAt_const
  have hel : F*deriv (constantResponse eta he).impact F/(constantResponse eta he).impact F < 1 := by
    simp [constantResponse]
  obtain ⟨eps,c,C,D,heps,hc,hC,hD,hfamily⟩ := theorem_6_3_original_family hN F rho T 1 betaMinus betaPlus
    (constantResponse eta he) hF hr hT (by norm_num) hbM hbP hg hel H hH
  refine ⟨eps,c,C,heps,hc,hC,?_⟩
  intro a ha0 haeps
  obtain ⟨m,P,hma,hmb,hmF,hmr,hmg,hm0,hreal,hmCa,hmv,hPH,hPT,hPS,hband,hloss,hupp,hcrisis⟩ := hfamily a ha0 haeps
  refine ⟨m,P,hma,hmb,hmF,hmr,hmg,hm0,hreal,hmCa,hPH,hPT,hPS,?_,?_⟩
  · intro i x hx
    exact ⟨(hband i x hx).1.le,(hband i x hx).2.le⟩
  · apply systemicCrisis_lower_of_each_loss _ _ (requiredAssetCount_pos alpha ha) (requiredAssetCount_le_card alpha ha1)
    intro i
    have hp : 0 < P.terminal.prices i := P.trace.endpoint_positive
      (fun j => by rw [P.initial_prices j];exact hF) i
    dsimp [logPriceFromBenchmark]
    rw [Real.log_div hp.ne' hF.ne']
    linarith [hloss i]

theorem theorem_6_2_attained_order (hN : 2 ≤ Fintype.card ι)
    (F rho eta T alpha betaMinus betaPlus : ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hT : 0 < T)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hbM : 0 < betaMinus) (hbP : 0 < betaPlus)
    (H : ι → ℝ) (hH : ∀ i, 0 < H i) :
    ∃ c v0 : ℝ, 0 < c ∧ 0 < v0 ∧ ∀ v : ℝ, 0 < v → v < v0 →
      OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v (c*v^2) := by
  obtain ⟨eps,c,C,heps,hc,hC,hfamily⟩ := constant_rate_attainment_family hN F rho eta T alpha betaMinus betaPlus
    hF hr he hT ha ha1 hbM hbP H hH
  refine ⟨c/C^2,C*eps,div_pos hc (sq_pos_of_pos hC),mul_pos hC heps,?_⟩
  intro v hv hv0
  have ha0 : 0 < v/C := div_pos hv hC
  have haeps : v/C < eps := (div_lt_iff₀ hC).mpr (by nlinarith)
  have hh := hfamily (v/C) ha0 haeps
  have hcap : C*(v/C) = v := by field_simp
  have hsev : c*(v/C)^2 = (c/C^2)*v^2 := by ring
  rw [hcap,hsev] at hh
  exact hh

theorem original_rate_necessary_quadratic
    (F rho eta T alpha betaMinus betaPlus v delta : ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hT : 0 < T)
    (H : ι → ℝ) (hdelta : delta ≤ (3:ℝ)/4)
    (h : OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta) :
    delta ≤ 3*(eta/(F*rho))^2*v^2 := by
  obtain ⟨m,P,hma,hmb,hmF,hmr,hmg,hm0,hreal,hmcap,hPH,hPT,hPS,hband,hcrisis⟩ := h
  let A := eta/(F*rho)
  let d := 1-Real.exp (-rho*T)
  have hA : 0 < A := div_pos he (mul_pos hF hr)
  have hd0 : 0 ≤ d := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  have hd1 : d ≤ 1 := by dsimp [d];linarith [Real.exp_pos (-rho*T)]
  have hv : 0 ≤ v := hmcap.1
  have hAv : 0 ≤ A*v := mul_nonneg hA.le hv
  by_cases hsmall : A*v ≤ 1/2
  · have hb : A*v*d ≤ 1/2 := (mul_le_mul_of_nonneg_left hd1 hAv).trans (by simpa using hsmall)
    have hb' : eta*v/(F*rho)*(1-Real.exp (-rho*m.b)) < 1 := by
      rw [hmb]
      have heq : eta*v/(F*rho) = A*v := by dsimp [A];ring
      rw [heq]
      linarith
    have hh := theorem_6_2_original_upper m F rho eta v hF hr he.le hmcap hma
      (fun i => congrFun hmF i) (fun i => congrFun hmr i)
      (fun i x hx => by rw [hmg];rfl) hm0 hb' (requiredAssetCount (ι := ι) alpha)
    rw [hmb] at hh
    have heq : eta*v/(F*rho) = A*v := by dsimp [A];ring
    rw [heq] at hh
    have hz : 0 ≤ rho*T*Real.exp (-rho*T) := mul_nonneg (mul_pos hr hT).le (Real.exp_pos _).le
    have hu := quadratic_coefficient_uniform A v d (rho*T*Real.exp (-rho*T)) hd0 hd1 hz hb
    rw [hPS] at hcrisis
    exact hcrisis.trans (hh.trans hu)
  · have hh : (1:ℝ)/2 < A*v := lt_of_not_ge hsmall
    have hs : (1:ℝ)/4 ≤ (A*v)^2 := by nlinarith
    change delta ≤ 3*A^2*v^2
    nlinarith

/-- Quantified Theta(sqrt(delta)) for the infimum over actual admissible
rate-bounded executions; the feasible set is proved nonempty in this range. -/
theorem theorem_6_2_minimum_rate (hN : 2 ≤ Fintype.card ι)
    (F rho eta T alpha betaMinus betaPlus : ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hT : 0 < T)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hbM : 0 < betaMinus) (hbP : 0 < betaPlus)
    (H : ι → ℝ) (hH : ∀ i, 0 < H i) :
    ∃ A B delta0 : ℝ, 0 < A ∧ 0 < B ∧ 0 < delta0 ∧ ∀ delta : ℝ, 0 < delta → delta < delta0 →
      {v | OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta}.Nonempty ∧
      A*Real.sqrt delta ≤ minimumOriginalRate F rho T alpha betaMinus betaPlus (constantResponse eta he) H delta ∧
      minimumOriginalRate F rho T alpha betaMinus betaPlus (constantResponse eta he) H delta ≤ B*Real.sqrt delta := by
  obtain ⟨eps,c,C,heps,hc,hC,hfamily⟩ := constant_rate_attainment_family hN F rho eta T alpha betaMinus betaPlus
    hF hr he hT ha ha1 hbM hbP H hH
  let K := 3*(eta/(F*rho))^2
  have hK : 0 < K := mul_pos (by norm_num) (sq_pos_of_pos (div_pos he (mul_pos hF hr)))
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  let A := 1/Real.sqrt K
  let B := C/Real.sqrt c
  let delta0 := min (c*eps^2) ((3:ℝ)/4)
  refine ⟨A,B,delta0,one_div_pos.mpr hsK,div_pos hC hsc,lt_min (mul_pos hc (sq_pos_of_pos heps)) (by norm_num),?_⟩
  intro delta hdelta hdelta0
  have hd0 : delta < c*eps^2 := lt_of_lt_of_le hdelta0 (min_le_left _ _)
  have hd1 : delta ≤ (3:ℝ)/4 := (lt_of_lt_of_le hdelta0 (min_le_right _ _)).le
  let a := Real.sqrt (delta/c)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (div_pos hdelta hc)
  have ha2 : a^2 = delta/c := Real.sq_sqrt (div_pos hdelta hc).le
  have haeps : a < eps := by
    have hh : a^2 < eps^2 := by rw [ha2];exact (div_lt_iff₀ hc).mpr (by nlinarith)
    nlinarith
  have hsev : c*a^2 = delta := by rw [ha2];field_simp
  have hfeas := hfamily a ha0 haeps
  rw [hsev] at hfeas
  have hcap : C*a = B*Real.sqrt delta := by
    dsimp [a,B]
    rw [Real.sqrt_div hdelta.le c]
    ring
  have hnonempty : {v | OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta}.Nonempty :=
    ⟨C*a,hfeas⟩
  have hlower : ∀ v, OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta → A*Real.sqrt delta ≤ v := by
    intro v hv
    have hv0 := OriginalRateFeasible.rate_nonnegative F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta hv
    have hh := original_rate_necessary_quadratic F rho eta T alpha betaMinus betaPlus v delta hF hr he hT H hd1 hv
    have hprod : (Real.sqrt K*v)^2 = K*v^2 := by rw [mul_pow,Real.sq_sqrt hK.le]
    have hsq : (Real.sqrt delta)^2 ≤ (Real.sqrt K*v)^2 := by
      rw [Real.sq_sqrt hdelta.le,hprod]
      exact hh
    have hroot : Real.sqrt delta ≤ Real.sqrt K*v :=
      (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hsK.le hv0)).mp hsq
    have hdiv : Real.sqrt delta/Real.sqrt K ≤ v := (div_le_iff₀ hsK).mpr (by nlinarith)
    convert hdiv using 1 <;> dsimp [A] <;> ring
  have hbelow : BddBelow {v | OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta} :=
    ⟨A*Real.sqrt delta,fun v hv => hlower v hv⟩
  refine ⟨hnonempty,le_csInf hnonempty (fun v hv => hlower v hv),?_⟩
  change sInf {v | OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta} ≤ _
  exact (csInf_le hbelow hfeas).trans_eq hcap

def OriginalQuadraticUpper (F rho eta T alpha : ℝ) (he : 0 < eta) : Prop :=
  ∀ (κ : Type) [Fintype κ] (edges : κ → PairedEdge ι) (m : ACPhysicalSession edges),
    m.a = 0 → m.b = T → m.F = (fun _ => F) → m.rho = (fun _ => rho) →
    m.response = (fun _ => constantResponse eta he) → (∀ i, m.prices 0 i = F) →
    ∀ v : ℝ, m.RateBounded v → eta*v/(F*rho)*(1-Real.exp (-rho*T)) < 1 →
    systemicCrisis (logPriceFromBenchmark F (m.prices T)) (requiredAssetCount (ι := ι) alpha) ≤
      (eta*v/(F*rho))^2*((1-Real.exp (-rho*T))-rho*T*Real.exp (-rho*T)+
        (1-Real.exp (-rho*T))^2/(2*(1-eta*v/(F*rho)*(1-Real.exp (-rho*T)))^2))

/-- Entire original Theorem 6.2: exact universal coefficient, attained
quadratic order, and two-sided sqrt(delta) bounds for the true rate infimum. -/
theorem theorem_6_2_original (hN : 2 ≤ Fintype.card ι)
    (F rho eta T alpha betaMinus betaPlus : ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hT : 0 < T)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1) (hbM : 0 < betaMinus) (hbP : 0 < betaPlus)
    (H : ι → ℝ) (hH : ∀ i, 0 < H i) :
    OriginalQuadraticUpper (ι := ι) F rho eta T alpha he ∧
    (∃ c v0 : ℝ, 0 < c ∧ 0 < v0 ∧ ∀ v : ℝ, 0 < v → v < v0 →
      OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v (c*v^2)) ∧
    (∃ A B delta0 : ℝ, 0 < A ∧ 0 < B ∧ 0 < delta0 ∧ ∀ delta : ℝ, 0 < delta → delta < delta0 →
      {v | OriginalRateFeasible F rho T alpha betaMinus betaPlus (constantResponse eta he) H v delta}.Nonempty ∧
      A*Real.sqrt delta ≤ minimumOriginalRate F rho T alpha betaMinus betaPlus (constantResponse eta he) H delta ∧
      minimumOriginalRate F rho T alpha betaMinus betaPlus (constantResponse eta he) H delta ≤ B*Real.sqrt delta) := by
  refine ⟨?_,theorem_6_2_attained_order hN F rho eta T alpha betaMinus betaPlus hF hr he hT ha ha1 hbM hbP H hH,
    theorem_6_2_minimum_rate hN F rho eta T alpha betaMinus betaPlus hF hr he hT ha ha1 hbM hbP H hH⟩
  intro κ inst edges m hma hmb hmF hmr hmg hm0 v hv hb
  have hb' : eta*v/(F*rho)*(1-Real.exp (-rho*m.b)) < 1 := by simpa only [hmb] using hb
  have hh := theorem_6_2_original_upper m F rho eta v hF hr he.le hv hma
    (fun i => congrFun hmF i) (fun i => congrFun hmr i)
    (fun i x hx => by rw [hmg];rfl) hm0 hb' (requiredAssetCount (ι := ι) alpha)
  simpa only [hmb] using hh

end MarketCrash
