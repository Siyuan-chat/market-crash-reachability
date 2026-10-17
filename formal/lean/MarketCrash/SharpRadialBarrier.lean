import MarketCrash.PhysicalBVNormalForm
import MarketCrash.OriginalVisitedPrices
import MarketCrash.ResponseFamilies
import MarketCrash.CrisisQuantile
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Theorem 4.4, universal clause: under constant impact and k=N,
delta_crit = log[sqrt N / (1+(sqrt N-1) exp(-rho*T))].
"If delta >= delta_crit, no such positive-price path exists."
This file proves the strict universal upper bound from genuine continuous
BV primitives and finite original flow-completed pulses. The sharp
approaching construction is a separate part of Theorem 4.4.

The aggregate square price has a continuous physical-time primitive even
when the individual prices are only BV: paired dollars cancel in every
physical prefix of the already proved original BV normal form.
-/

noncomputable section
namespace MarketCrash
open Set MeasureTheory Filter
open scoped Topology

def originalRadius {ι : Type*} [Fintype ι] (S : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (S i)^2)

theorem positive_prices_radius_strict_l1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (S : ι → ℝ) (hp : ∀ i, 0 < S i) :
    0 < originalRadius S ∧ originalRadius S < ∑ i, S i := by
  classical
  letI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let i : ι := Classical.arbitrary ι
  have hQ : 0 < ∑ j, (S j)^2 := (sq_pos_of_pos (hp i)).trans_le
    (Finset.single_le_sum (fun j _ => sq_nonneg (S j)) (Finset.mem_univ i))
  have hL : 0 < ∑ j, S j := (hp i).trans_le
    (Finset.single_le_sum (fun j _ => (hp j).le) (Finset.mem_univ i))
  have hlt (j : ι) : S j < ∑ k, S k := by
    obtain ⟨k,hkj⟩ := exists_ne j
    have hk : k ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ k⟩
    have hh := (hp k).trans_le (Finset.single_le_sum (fun k _ => (hp k).le) hk)
    have he := Finset.sum_erase_add Finset.univ S (Finset.mem_univ j)
    linarith
  have hsq : (∑ j, (S j)^2) < (∑ j, S j)^2 := by
    have hh := Finset.sum_lt_sum
      (fun j (_ : j ∈ Finset.univ) => (mul_lt_mul_of_pos_left (hlt j) (hp j)).le)
      ⟨i,Finset.mem_univ i,mul_lt_mul_of_pos_left (hlt i) (hp i)⟩
    simpa only [←sq,←Finset.sum_mul] using hh
  refine ⟨Real.sqrt_pos.mpr hQ,?_⟩
  have hr := Real.sq_sqrt hQ.le
  have hr0 := Real.sqrt_nonneg (∑ j,(S j)^2)
  dsimp [originalRadius]
  nlinarith

theorem continuous_piece_constant_square_primitive
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : PhysicalContinuousBVPiece edges)
    (F ρ η : ℝ) (hF : 0 < F) (hη : 0 < η)
    (hmF : ∀ i, m.F i = F) (hmρ : ∀ i, m.rho i = ρ)
    (hmg : ∀ i, m.response i = constantResponse η hη)
    (t : ℝ) (ht : t ∈ Icc m.a m.b) :
    (∑ i, (m.prices t i)^2)-(∑ i, (m.prices m.a i)^2) =
      -2*ρ*∫ u in m.a..t, ((∑ i, (m.prices u i)^2)-F*(∑ i,m.prices u i)) := by
  classical
  have hi (i : ι) : IntervalIntegrable (fun u => m.prices u i*(m.prices u i-F)) volume m.a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact ((m.continuous_prices i).mul ((m.continuous_prices i).sub continuousOn_const)).mono
      (fun u hu => ⟨hu.1,hu.2.trans ht.2⟩)
  have hasset (i : ι) : (m.prices t i)^2-(m.prices m.a i)^2 =
      2*η*tradingInput (pairedMatrix edges)
        (fun e => (m.execution.cumulative e) t-(m.execution.cumulative e) m.a) i -
        2*ρ*∫ u in m.a..t, m.prices u i*(m.prices u i-F) := by
    have hh := m.normal_form t ht i
    simp only [hmF,hmρ,hmg] at hh
    dsimp [constantResponse] at hh
    rw [←constantCoordinate_eq_integral F η hF hη (m.positive_prices t ht i),
      ←constantCoordinate_eq_integral F η hF hη (m.positive_prices m.a (left_mem_Icc.mpr m.time_order) i)] at hh
    change constantCoordinate F η (m.prices t i) = constantCoordinate F η (m.prices m.a i)+
      tradingInput (pairedMatrix edges) (fun e => (m.execution.cumulative e) t-(m.execution.cumulative e) m.a) i-
      ρ*(∫ u in m.a..t, m.prices u i*(m.prices u i-F)/η) at hh
    rw [intervalIntegral.integral_div] at hh
    dsimp [constantCoordinate] at hh
    field_simp [hη.ne'] at hh
    have he : (2*η^2)*((m.prices t i)^2-(m.prices m.a i)^2-
        (2*η*tradingInput (pairedMatrix edges) (fun e => (m.execution.cumulative e) t-(m.execution.cumulative e) m.a) i-
          2*ρ*(∫ u in m.a..t,m.prices u i*(m.prices u i-F)))) = 0 := by linear_combination hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (by positivity))
  calc
    _ = ∑ i, ((m.prices t i)^2-(m.prices m.a i)^2) := by rw [Finset.sum_sub_distrib]
    _ = ∑ i, (2*η*tradingInput (pairedMatrix edges)
        (fun e => (m.execution.cumulative e) t-(m.execution.cumulative e) m.a) i-
        2*ρ*∫ u in m.a..t, m.prices u i*(m.prices u i-F)) := Finset.sum_congr rfl (fun i _ => hasset i)
    _ = -2*ρ*(∫ u in m.a..t, ∑ i, m.prices u i*(m.prices u i-F)) := by
      rw [Finset.sum_sub_distrib,←Finset.mul_sum,paired_trading_sum_zero,mul_zero,←Finset.mul_sum,
        ←intervalIntegral.integral_finset_sum (fun i _ => hi i)]
      ring
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u _
      simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,←sq]
      ring

theorem continuous_piece_radius_hasDerivAt
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : PhysicalContinuousBVPiece edges)
    (hN : 2 ≤ Fintype.card ι) (F ρ η : ℝ) (hF : 0 < F) (hη : 0 < η)
    (hmF : ∀ i, m.F i = F) (hmρ : ∀ i, m.rho i = ρ)
    (hmg : ∀ i, m.response i = constantResponse η hη)
    (t : ℝ) (ht : t ∈ Ioo m.a m.b) :
    HasDerivAt (fun u => originalRadius (m.prices u))
      (-ρ*(originalRadius (m.prices t)-F*(∑ i,m.prices t i)/originalRadius (m.prices t))) t := by
  let Q := fun u => ∑ i, (m.prices u i)^2
  let L := fun u => ∑ i, m.prices u i
  let H := fun u => Q u-F*L u
  have hQc : ContinuousOn Q (Icc m.a m.b) := continuousOn_finset_sum _ (fun i _ => (m.continuous_prices i).pow 2)
  have hLc : ContinuousOn L (Icc m.a m.b) := continuousOn_finset_sum _ (fun i _ => m.continuous_prices i)
  have hHc : ContinuousOn H (Icc m.a m.b) := hQc.sub (continuousOn_const.mul hLc)
  have hi : IntervalIntegrable H volume m.a t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1.le]
    exact hHc.mono (fun u hu => ⟨hu.1,hu.2.trans ht.2.le⟩)
  have hmeas : StronglyMeasurableAtFilter H (nhds t) :=
    ⟨Icc m.a m.b,Icc_mem_nhds ht.1 ht.2,hHc.aestronglyMeasurable measurableSet_Icc⟩
  have hd := ((intervalIntegral.integral_hasDerivAt_right hi hmeas
    (hHc.continuousAt (Icc_mem_nhds ht.1 ht.2))).const_mul (-2*ρ)).const_add (Q m.a)
  have he : Q =ᶠ[nhds t] (fun u => Q m.a+(-2*ρ)*(∫ v in m.a..u,H v)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    have hh := continuous_piece_constant_square_primitive m F ρ η hF hη hmF hmρ hmg u (Ioo_subset_Icc_self hu)
    change Q u-Q m.a = -2*ρ*(∫ v in m.a..u,H v) at hh
    linarith
  have hQd := hd.congr_of_eventuallyEq he
  have hp := (positive_prices_radius_strict_l1 hN (m.prices t) (m.positive_prices t (Ioo_subset_Icc_self ht))).1
  have hQp : 0 < Q t := by
    exact Real.sqrt_pos.mp hp
  have hR := (Real.hasDerivAt_sqrt hQp.ne').comp t hQd
  convert hR using 1
  dsimp [originalRadius,Q,H,L]
  have heq := Real.sq_sqrt hQp.le
  dsimp [Q] at heq
  field_simp [hp.ne']
  nlinarith

theorem continuous_piece_weighted_radius_strictMono
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : PhysicalContinuousBVPiece edges)
    (hN : 2 ≤ Fintype.card ι) (F ρ η : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η)
    (hmF : ∀ i, m.F i = F) (hmρ : ∀ i, m.rho i = ρ)
    (hmg : ∀ i, m.response i = constantResponse η hη) :
    StrictMonoOn (fun t => (originalRadius (m.prices t)-F)*Real.exp (ρ*t)) (Icc m.a m.b) := by
  have hQc : ContinuousOn (fun t => ∑ i,(m.prices t i)^2) (Icc m.a m.b) :=
    continuousOn_finset_sum _ (fun i _ => (m.continuous_prices i).pow 2)
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    ((hQc.sqrt.sub continuousOn_const).mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  intro t ht
  rw [interior_Icc] at ht
  have hR := continuous_piece_radius_hasDerivAt m hN F ρ η hF hη hmF hmρ hmg t ht
  have hE := ((hasDerivAt_id t).const_mul ρ).exp
  have hd := (hR.sub_const F).mul hE
  change 0 < deriv (fun x => (originalRadius (m.prices x)-F)*Real.exp (ρ*x)) t
  simp only [id_eq] at hd
  rw [hd.deriv]
  obtain ⟨hpos,hgap⟩ := positive_prices_radius_strict_l1 hN (m.prices t)
    (m.positive_prices t (Ioo_subset_Icc_self ht))
  have hratio : 0 < (∑ i,m.prices t i)/originalRadius (m.prices t)-1 :=
    sub_pos.mpr ((one_lt_div hpos).mpr hgap)
  have hh := mul_pos (mul_pos (mul_pos hρ hF) hratio) (Real.exp_pos (ρ*t))
  convert hh using 1 <;> ring

theorem original_constant_pulse_radius_preserved
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (p : OriginalFlowCompletedPulse edges)
    (F η : ℝ) (hF : 0 < F) (hη : 0 < η)
    (hmF : ∀ i, p.F i = F) (hmg : ∀ i, p.response i = constantResponse η hη) :
    originalRadius (p.prices 1) = originalRadius (p.prices 0) := by
  have hcoord (a : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (i : ι) :
      coordinate (p.F i) (p.response i).impact (p.prices a i) =
        ((p.prices a i)^2-F^2)/(2*η) := by
    rw [hmF,hmg]
    exact (constantCoordinate_eq_integral F η hF hη (p.positive_prices a ha i)).symm
  have hh := p.potential_preserved
  unfold potential at hh
  simp_rw [hcoord 1 ⟨by norm_num,le_rfl⟩,hcoord 0 ⟨le_rfl,by norm_num⟩] at hh
  rw [←Finset.sum_div,←Finset.sum_div] at hh
  have he : (∑ i,(p.prices 1 i)^2) = ∑ i,(p.prices 0 i)^2 := by
    have hmul := congrArg (fun x : ℝ => x*(2*η)) hh
    simp only [div_mul_cancel₀ _ (show 2*η ≠ 0 by positivity),Finset.sum_sub_distrib] at hmul
    linarith
  exact congrArg Real.sqrt he

def weightedOriginalRadius {ι : Type*} [Fintype ι] (F ρ : ℝ) (s : PhysicalMarketState ι) : ℝ :=
  (originalRadius s.prices-F)*Real.exp (ρ*s.time)

theorem original_step_weighted_radius_comparison
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η)
    {s t : PhysicalMarketState ι}
    (step : OriginalPhysicalStep (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges s t) :
    weightedOriginalRadius F ρ s ≤ weightedOriginalRadius F ρ t ∧
      (s.time < t.time → weightedOriginalRadius F ρ s < weightedOriginalRadius F ρ t) := by
  cases step with
  | continuous m hmF hmρ hmg hBV =>
    have hh := continuous_piece_weighted_radius_strictMono m hN F ρ η hF hρ hη
      (fun i => congrFun hmF i) (fun i => congrFun hmρ i) (fun i => congrFun hmg i)
    exact ⟨hh.monotoneOn (left_mem_Icc.mpr m.time_order) (right_mem_Icc.mpr m.time_order) m.time_order,
      fun ht => hh (left_mem_Icc.mpr m.time_order) (right_mem_Icc.mpr m.time_order) ht⟩
  | pulse p hmF hmg hBV =>
    have hh := original_constant_pulse_radius_preserved p F η hF hη
      (fun i => congrFun hmF i) (fun i => congrFun hmg i)
    constructor
    · dsimp [weightedOriginalRadius]
      rw [hh]
    · intro ht
      exact False.elim ((lt_irrefl p.physicalTime) ht)

theorem original_trace_weighted_radius_comparison
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges s t) :
    weightedOriginalRadius F ρ s ≤ weightedOriginalRadius F ρ t ∧
      (s.time < t.time → weightedOriginalRadius F ρ s < weightedOriginalRadius F ρ t) := by
  induction trace with
  | refl => exact ⟨le_rfl,fun h => False.elim ((lt_irrefl s.time) h)⟩
  | @append mid t previous step ih =>
    obtain ⟨hs,hslt⟩ := original_step_weighted_radius_comparison hN F ρ η hF hρ hη step
    refine ⟨ih.1.trans hs,?_⟩
    intro hst
    by_cases hsm : s.time < mid.time
    · exact (ih.2 hsm).trans_le hs
    · have hmt : mid.time < t.time := by linarith [previous.chronological]
      exact ih.1.trans_lt (hslt hmt)

theorem originalRadius_constant {ι : Type*} [Fintype ι] (F : ℝ) (hF : 0 ≤ F) :
    originalRadius (fun _ : ι => F) = F*Real.sqrt (Fintype.card ι) := by
  unfold originalRadius
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [Real.sqrt_mul (Nat.cast_nonneg _),Real.sqrt_sq hF,mul_comm]

theorem original_trace_strict_radial_lower
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges s t)
    (hs0 : s.time = 0) (hstart : ∀ i, s.prices i = F) (hPT : t.time = T) :
    F*(1+(Real.sqrt (Fintype.card ι)-1)*Real.exp (-ρ*T)) < originalRadius t.prices := by
  have h := (original_trace_weighted_radius_comparison hN F ρ η hF hρ hη trace).2
    (by rw [hs0,hPT];exact hT)
  have hR0 : originalRadius s.prices = F*Real.sqrt (Fintype.card ι) := by
    have he : s.prices = fun _ => F := funext hstart
    rw [he,originalRadius_constant F hF.le]
  dsimp [weightedOriginalRadius] at h
  rw [hs0,hPT,hR0,mul_zero,Real.exp_zero,mul_one] at h
  have hh := mul_lt_mul_of_pos_right h (Real.exp_pos (-ρ*T))
  have he : Real.exp (ρ*T)*Real.exp (-ρ*T) = 1 := by rw [←Real.exp_add];simp
  rw [mul_assoc,he,mul_one] at hh
  have hh' := add_lt_add_left hh F
  convert hh' using 1 <;> ring

theorem original_path_strict_radial_lower
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges)
    (hPT : P.terminal.time = T) :
    F*(1+(Real.sqrt (Fintype.card ι)-1)*Real.exp (-ρ*T)) < originalRadius P.terminal.prices :=
  original_trace_strict_radial_lower hN F ρ η T hF hρ hη hT P.trace P.at_zero P.initial_prices hPT

theorem originalRadius_le_uniform {ι : Type*} [Fintype ι] (S : ι → ℝ) (L : ℝ)
    (hp : ∀ i, 0 ≤ S i) (hL : 0 ≤ L) (hb : ∀ i, S i ≤ L) :
    originalRadius S ≤ L*Real.sqrt (Fintype.card ι) := by
  calc
    originalRadius S ≤ originalRadius (fun _ : ι => L) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun i _ => (sq_le_sq₀ (hp i) hL).mpr (hb i))
    _ = _ := originalRadius_constant L hL

def originalSharpCriticalLoss (n ρ T : ℝ) : ℝ :=
  Real.log (Real.sqrt n/(1+(Real.sqrt n-1)*Real.exp (-ρ*T)))

theorem original_trace_strict_crisis_upper
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges s t)
    (hs0 : s.time = 0) (hstart : ∀ i, s.prices i = F) (hPT : t.time = T) :
    systemicCrisis (logPriceFromBenchmark F t.prices) (Fintype.card ι) <
      originalSharpCriticalLoss (Fintype.card ι) ρ T := by
  classical
  let n : ℝ := Fintype.card ι
  let D := 1+(Real.sqrt n-1)*Real.exp (-ρ*T)
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hroot1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by linarith)
  have hD : 0 < D := by
    dsimp [D]
    have hh := mul_nonneg (sub_nonneg.mpr hroot1) (Real.exp_pos (-ρ*T)).le
    linarith
  have hp (i : ι) : 0 < t.prices i := trace.endpoint_positive
    (fun i => by rw [hstart i];exact hF) i
  apply lt_of_not_ge
  intro hcrit
  change originalSharpCriticalLoss n ρ T ≤ systemicCrisis (logPriceFromBenchmark F t.prices) (Fintype.card ι) at hcrit
  have hquant : originalSharpCriticalLoss n ρ T ≤
      coverageQuantile (logPriceFromBenchmark F t.prices) (Fintype.card ι) :=
    hcrit.trans (min_le_right _ _)
  have hcount := (coverageQuantile_threshold_iff (logPriceFromBenchmark F t.prices)
    (Fintype.card ι) Fintype.card_pos le_rfl (originalSharpCriticalLoss n ρ T)).mp hquant
  have hset : Finset.univ.filter (fun i => originalSharpCriticalLoss n ρ T ≤
      -logPriceFromBenchmark F t.prices i) = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by simpa only [Finset.card_univ] using hcount)
  have hprice (i : ι) : t.prices i ≤ F*D/Real.sqrt n := by
    have hi : originalSharpCriticalLoss n ρ T ≤ -logPriceFromBenchmark F t.prices i := by
      have hiMem : i ∈ Finset.univ.filter (fun j : ι => originalSharpCriticalLoss n ρ T ≤ -logPriceFromBenchmark F t.prices j) := by
        rw [hset]
        exact Finset.mem_univ i
      exact (Finset.mem_filter.mp hiMem).2
    have he := Real.exp_le_exp.mpr (show logPriceFromBenchmark F t.prices i ≤
      -originalSharpCriticalLoss n ρ T by linarith)
    have hex : Real.exp (-originalSharpCriticalLoss n ρ T) = D/Real.sqrt n := by
      dsimp [originalSharpCriticalLoss]
      rw [Real.exp_neg,Real.exp_log (div_pos hroot hD),inv_div]
    rw [hex] at he
    have hh := mul_le_mul_of_nonneg_left he hF.le
    rw [exp_logPrice_eq_price F t.prices hF hp] at hh
    simpa only [mul_div_assoc] using hh
  have hupper := originalRadius_le_uniform t.prices (F*D/Real.sqrt n) (fun i => (hp i).le)
    (div_nonneg (mul_nonneg hF.le hD.le) hroot.le) hprice
  have hupper' : originalRadius t.prices ≤ F*D := by
    simpa only [show (Fintype.card ι : ℝ) = n from rfl,div_mul_cancel₀ _ hroot.ne'] using hupper
  have hlower := original_trace_strict_radial_lower hN F ρ η T hF hρ hη hT trace hs0 hstart hPT
  exact (not_lt_of_ge hupper') hlower

theorem original_path_strict_crisis_upper
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges)
    (hPT : P.terminal.time = T) :
    systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) <
      originalSharpCriticalLoss (Fintype.card ι) ρ T :=
  original_trace_strict_crisis_upper hN F ρ η T hF hρ hη hT P.trace P.at_zero P.initial_prices hPT

theorem original_path_critical_threshold_excluded
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η T δ : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges)
    (hPT : P.terminal.time = T) (hδ : originalSharpCriticalLoss (Fintype.card ι) ρ T ≤ δ) :
    ¬δ ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) := by
  intro h
  exact (not_lt_of_ge (hδ.trans h)) (original_path_strict_crisis_upper hN F ρ η T hF hρ hη hT P hPT)

theorem original_trace_critical_threshold_excluded
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (hN : 2 ≤ Fintype.card ι)
    (F ρ η T δ : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη) edges s t)
    (hs0 : s.time = 0) (hstart : ∀ i, s.prices i = F) (hPT : t.time = T)
    (hδ : originalSharpCriticalLoss (Fintype.card ι) ρ T ≤ δ) :
    ¬δ ≤ systemicCrisis (logPriceFromBenchmark F t.prices) (Fintype.card ι) := by
  intro h
  exact (not_lt_of_ge (hδ.trans h))
    (original_trace_strict_crisis_upper hN F ρ η T hF hρ hη hT trace hs0 hstart hPT)

theorem originalSharpCriticalLoss_positive (n ρ T : ℝ) (hn : 2 ≤ n) (hρ : 0 < ρ) (hT : 0 < T) :
    0 < originalSharpCriticalLoss n ρ T := by
  have hs : 1 < Real.sqrt n := by
    have hsq := Real.sq_sqrt (show 0 ≤ n by linarith)
    have hp := Real.sqrt_nonneg n
    nlinarith
  have he : Real.exp (-ρ*T) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hD : 0 < 1+(Real.sqrt n-1)*Real.exp (-ρ*T) := by
    have hh := mul_pos (sub_pos.mpr hs) (Real.exp_pos (-ρ*T))
    linarith
  have hDlt : 1+(Real.sqrt n-1)*Real.exp (-ρ*T) < Real.sqrt n := by
    have hh := mul_lt_mul_of_pos_left he (sub_pos.mpr hs)
    linarith
  exact Real.log_pos ((lt_div_iff₀ hD).mpr (by simpa only [one_mul] using hDlt))

end MarketCrash
