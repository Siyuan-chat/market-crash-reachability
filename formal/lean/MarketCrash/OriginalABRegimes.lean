import MarketCrash.OriginalSystemicBarrier
import MarketCrash.OriginalResources
import MarketCrash.OriginalTwoPulse
import MarketCrash.ResponseFamilies

/-! Theorem 4.1, A/B branches only. Market A excludes every positive
crisis on every original physical observation. Market B admits positive
arbitrarily small crises, while every fixed initial inventory cap gives
a trade-sequence-independent finite terminal upper bound. The severe
reachability C branch is not asserted by this module. -/

noncomputable section
namespace MarketCrash
open Set MeasureTheory Filter
open scoped Topology

theorem quadraticResponse_hasDerivAt (F η x : ℝ) (hF : 0 < F) (hη : 0 < η) :
    HasDerivAt (quadraticResponse F η hF hη).impact (2*η*x/F^2) x := by
  have hd := (((hasDerivAt_id x).div_const F).pow 2).const_mul η
  convert hd using 1 <;> dsimp [quadraticResponse] <;> field_simp <;> ring

theorem quadraticResponse_elasticity (F η x : ℝ) (hF : 0 < F) (hη : 0 < η) (hx : 0 < x) :
    responseElasticity (quadraticResponse F η hF hη).impact x = 2 := by
  rw [responseElasticity,(quadraticResponse_hasDerivAt F η x hF hη).deriv]
  dsimp [quadraticResponse]
  field_simp
  ring

theorem linearResponse_hasDerivAt (F η x : ℝ) (hF : 0 < F) (hη : 0 < η) :
    HasDerivAt (linearResponse F η hF hη).impact (η/F) x := by
  convert ((hasDerivAt_id x).div_const F).const_mul η using 1 <;> dsimp [linearResponse] <;> ring

theorem linearResponse_elasticity (F η x : ℝ) (hF : 0 < F) (hη : 0 < η) (hx : 0 < x) :
    responseElasticity (linearResponse F η hF hη).impact x = 1 := by
  rw [responseElasticity,(linearResponse_hasDerivAt F η x hF hη).deriv]
  dsimp [linearResponse]
  field_simp
  ring

theorem theorem_4_1_A_original
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (F ρ η : ℝ) (hF : 0 < F) (hρ : 0 ≤ ρ) (hη : 0 < η)
    (_hN : 2 ≤ Fintype.card ι)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => quadraticResponse F η hF hη) edges) :
    ∀ o, P.trace.Observes o → ∀ α : ℝ, 0 < α → α ≤ 1 →
      systemicCrisis (logPriceFromBenchmark F o.prices) (requiredAssetCount (ι := ι) α) ≤ 0 := by
  intro o ho α hα hα1
  apply P.trace.actual_crisis_nonpositive_observed F ρ (quadraticResponse F η hF hη) hF hρ
    (fun x _ => (quadraticResponse_hasDerivAt F η x hF hη).differentiableAt) P.initial_prices _ o ho
  intro i x hx
  have hp := P.trace.visited_positive (fun j => by rw [P.initial_prices j];exact hF) i x hx
  rw [quadraticResponse_elasticity F η x hF hη hp]

def linearInventoryCost (F η S : ℝ) : ℝ :=
  F/η*(S-F)-F^2/η*Real.log (S/F)

theorem linearInventoryCost_hasDerivAt (F η S : ℝ) (hF : 0 < F) (hη : 0 < η) (hS : 0 < S) :
    HasDerivAt (linearInventoryCost F η) ((S-F)/(linearResponse F η hF hη).impact S) S := by
  have hd := (((hasDerivAt_id S).sub_const F).const_mul (F/η)).sub
    ((((hasDerivAt_id S).div_const F).log (div_ne_zero hS.ne' hF.ne')).const_mul (F^2/η))
  convert hd using 1 <;> dsimp [linearInventoryCost,linearResponse] <;> field_simp <;> ring

theorem linear_inventory_cost_formula (F η S : ℝ) (hF : 0 < F) (hη : 0 < η) (hS : 0 < S) :
    inventoryCostCoordinate F (linearResponse F η hF hη).impact S =
      F^2/η*(Real.log (F/S)+S/F-1) := by
  have hsub : uIcc F S ⊆ Ioi (0:ℝ) := fun x hx => (lt_min hF hS).trans_le hx.1
  have hi : IntervalIntegrable (fun x => (x-F)/(linearResponse F η hF hη).impact x) volume F S :=
    (continuousOn_id.sub continuousOn_const |>.div
      ((linearResponse F η hF hη).continuousOn_positive.mono hsub)
      (fun x hx => ((linearResponse F η hF hη).positive x (hsub hx)).ne')).intervalIntegrable
  rw [inventoryCostCoordinate_integral F S (linearResponse F η hF hη) hF hS,
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => linearInventoryCost_hasDerivAt F η x hF hη (hsub hx)) hi]
  dsimp [linearInventoryCost]
  rw [Real.log_div hF.ne' hS.ne',Real.log_div hS.ne' hF.ne']
  simp only [div_self hF.ne',Real.log_one,mul_zero,sub_zero]
  field_simp
  ring

theorem linear_inventory_cost_logloss (F η L : ℝ) (hF : 0 < F) (hη : 0 < η) :
    inventoryCostCoordinate F (linearResponse F η hF hη).impact (F*Real.exp (-L)) =
      F^2/η*(L+Real.exp (-L)-1) := by
  rw [linear_inventory_cost_formula F η _ hF hη (mul_pos hF (Real.exp_pos _))]
  have hdiv : F/(F*Real.exp (-L)) = Real.exp L := by
    rw [Real.exp_neg]
    field_simp
  rw [hdiv,Real.log_exp]
  congr 1
  field_simp

theorem linear_original_asset_inventory_bound
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (F ρ η : ℝ) (hF : 0 < F) (hη : 0 < η)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => linearResponse F η hF hη) edges)
    (H0 : ℝ) (hH : ∀ i, P.initial.shares i ≤ H0) (i : ι) :
    Real.log (F/P.terminal.prices i) ≤ 1+η*H0/F := by
  have hp : 0 < P.terminal.prices i := P.trace.endpoint_positive
    (fun j => by rw [P.initial_prices j];exact hF) i
  have hc := P.trace.inventory_cost_nonincreasing i
  unfold physicalInventoryCost at hc
  rw [P.initial_prices i,P.initial_dollars i,P.terminal_dollars i] at hc
  have hzero : inventoryCostCoordinate F (linearResponse F η hF hη).impact F = 0 := by
    simp [inventoryCostCoordinate,coordinate_at_benchmark,shareResponseCoordinate_at_benchmark]
  change F*P.terminal.shares i+inventoryCostCoordinate F (linearResponse F η hF hη).impact (P.terminal.prices i)-0 ≤
    F*P.initial.shares i+inventoryCostCoordinate F (linearResponse F η hF hη).impact F-0 at hc
  rw [hzero] at hc
  have hs := mul_nonneg hF.le (P.trace.endpoint_no_short P.initial_holdings i)
  have hH' := mul_le_mul_of_nonneg_left (hH i) hF.le
  have hE : inventoryCostCoordinate F (linearResponse F η hF hη).impact (P.terminal.prices i) ≤ F*H0 := by linarith
  rw [linear_inventory_cost_formula F η _ hF hη hp] at hE
  have hK : 0 < F^2/η := div_pos (sq_pos_of_pos hF) hη
  have hS : 0 < P.terminal.prices i/F := div_pos hp hF
  have hh : (F^2/η)*(Real.log (F/P.terminal.prices i)-1) ≤ F*H0 :=
    (mul_le_mul_of_nonneg_left (by linarith : Real.log (F/P.terminal.prices i)-1 ≤
      Real.log (F/P.terminal.prices i)+P.terminal.prices i/F-1) hK.le).trans hE
  have hh' : Real.log (F/P.terminal.prices i)-1 ≤ F*H0/(F^2/η) :=
    (le_div_iff₀ hK).mpr (by simpa only [mul_comm] using hh)
  have he : F*H0/(F^2/η) = η*H0/F := by field_simp;ring
  rw [he] at hh'
  linarith

theorem theorem_4_1_B_inventory_bound
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (F ρ η : ℝ) (hF : 0 < F) (hη : 0 < η)
    (H0 : ℝ)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => linearResponse F η hF hη) edges)
    (hH : ∀ i, P.initial.shares i ≤ H0) (α : ℝ) :
    systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) α) ≤ 1+η*H0/F := by
  have hp (i : ι) : 0 < P.terminal.prices i := P.trace.endpoint_positive
    (fun j => by rw [P.initial_prices j];exact hF) i
  have hb (i : ι) : -logPriceFromBenchmark F P.terminal.prices i ≤ 1+η*H0/F := by
    have hh := linear_original_asset_inventory_bound F ρ η hF hη P H0 hH i
    dsimp [logPriceFromBenchmark]
    rw [Real.log_div hF.ne' (hp i).ne'] at hh
    rw [Real.log_div (hp i).ne' hF.ne']
    linarith
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (systemicCrisis_le_meanLogLoss _ _).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hb i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_neg_distrib] at hh
  exact (div_le_iff₀ hn).mpr (by nlinarith)

theorem theorem_4_1_B_small_positive
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ)
    (hη : 0 < η) (hT : 0 < T) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : requiredAssetCount (ι := ι) α < Fintype.card ι) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => linearResponse F η hF hη) completePairedEdges,
      P.terminal.time = T ∧
      0 < systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) α) ∧
      systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) α) < ζ := by
  classical
  let hub : ι := Classical.arbitrary ι
  let u := partialCoveragePulseVector hub
  have hn : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have huiff (i : ι) : 0 < u i ↔ i ≠ hub := by
    by_cases hi : i = hub
    · subst i
      have hh := partialCoveragePulseVector_hub_negative hub hN
      exact iff_of_false (not_lt.mpr hh.le) (not_ne_iff.mpr rfl)
    · simp [u,partialCoveragePulseVector,hi]
  have hfilter : Finset.univ.filter (fun i => 0 < u i) = Finset.univ.erase hub := by
    ext i
    simp [huiff]
  have hcount : requiredAssetCount (ι := ι) α ≤ (Finset.univ.filter (fun i => 0 < u i)).card := by
    rw [hfilter,Finset.card_erase_of_mem (Finset.mem_univ hub),Finset.card_univ]
    omega
  let g := linearResponse F η hF hη
  have hg : ContDiffAt ℝ 3 g.impact F := by
    exact contDiffAt_const.mul (contDiffAt_id.div_const F)
  have he : F*deriv g.impact F/g.impact F = 1 := linearResponse_elasticity F η F hF hη hF
  have hr : Real.exp (-ρ*T) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hρ hT])
  obtain ⟨ε,C,hε,hpaths⟩ := proposition_4_3_original F ρ T g hF hρ hT hN hg α hα hα1 hk
    (by rw [he];norm_num) (by rw [he];simpa only [show (2:ℝ)-1=1 by norm_num] using hr) u (partialCoveragePulseVector_zero_sum hub) hcount
  let Q := (g.impact F/F^2)^2/(2*(Fintype.card ι : ℝ))*(1-Real.exp (-ρ*T))*
    (2-F*deriv g.impact F/g.impact F-Real.exp (-ρ*T))*(∑ i,(u i)^2)
  let D := |Q|+|C|+1
  have hD : 0 < D := by dsimp [D];positivity
  let h := min ε (min 1 (ζ/D))/2
  have hh : 0 < h := half_pos (lt_min hε (lt_min one_pos (div_pos hζ hD)))
  have hhε : h < ε := (half_lt_self (lt_min hε (lt_min one_pos (div_pos hζ hD)))).trans_le (min_le_left _ _)
  have hhrest : h < min 1 (ζ/D) := (half_lt_self (lt_min hε (lt_min one_pos (div_pos hζ hD)))).trans_le (min_le_right _ _)
  have hh1 : h ≤ 1 := (hhrest.trans_le (min_le_left _ _)).le
  have hhζ : D*h < ζ := by nlinarith [(lt_div_iff₀ hD).mp (hhrest.trans_le (min_le_right _ _))]
  obtain ⟨P,hPT,hpos,herr⟩ := hpaths h hh hhε
  change |meanLogLoss (logPriceFromBenchmark F P.terminal.prices)-Q*h^2| ≤ C*h^3 at herr
  have hh2 : h^2 ≤ h := by nlinarith
  have hh3 : h^3 ≤ h := by
    calc
      h^3 = h^2*h := by ring
      _ ≤ h*h := mul_le_mul_of_nonneg_right hh2 hh.le
      _ = h^2 := by ring
      _ ≤ h := hh2
  have hQ : Q*h^2 ≤ |Q| *h := (mul_le_mul_of_nonneg_right (le_abs_self Q) (sq_nonneg h)).trans
    (mul_le_mul_of_nonneg_left hh2 (abs_nonneg Q))
  have hC : C*h^3 ≤ |C| *h := (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hh.le 3)).trans
    (mul_le_mul_of_nonneg_left hh3 (abs_nonneg C))
  have hm : meanLogLoss (logPriceFromBenchmark F P.terminal.prices) < ζ := by
    have hlo := (le_abs_self (meanLogLoss (logPriceFromBenchmark F P.terminal.prices)-Q*h^2)).trans herr
    dsimp [D] at hhζ
    nlinarith
  exact ⟨P,hPT,hpos,(systemicCrisis_le_meanLogLoss _ _).trans_lt hm⟩

/-- Theorem 4.1(B): small positive crises are reachable; independently,
each fixed initial inventory cap bounds the terminal crisis of every
original admissible path, regardless of its trade sequence. -/
theorem theorem_4_1_B_original
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hk : requiredAssetCount (ι := ι) α < Fintype.card ι) :
    (∀ ζ : ℝ, 0 < ζ →
      ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
        (fun _ => linearResponse F η hF hη) completePairedEdges,
        P.terminal.time = T ∧
        0 < systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) α) ∧
        systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) α) < ζ) ∧
    ∀ (H0 : ℝ) (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => linearResponse F η hF hη) edges),
      (∀ i, P.initial.shares i ≤ H0) →
      systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) α) ≤ 1+η*H0/F := by
  constructor
  · intro ζ hζ
    exact theorem_4_1_B_small_positive hN F ρ η T hF hρ hη hT α hα hα1 hk ζ hζ
  · intro H0 P hH
    exact theorem_4_1_B_inventory_bound F ρ η hF hη H0 P hH α

end MarketCrash
