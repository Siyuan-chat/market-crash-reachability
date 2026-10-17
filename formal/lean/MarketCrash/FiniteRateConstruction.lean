import MarketCrash.ParameterizedODEExpansion
import MarketCrash.ACPhysicalSession
import Mathlib.Analysis.SpecialFunctions.Integrals
import MarketCrash.PhysicalBVNormalForm
import MarketCrash.PairedControlConstruction
import MarketCrash.CompletePairedEmbedding
import MarketCrash.OriginalPhysicalTrace
import MarketCrash.CrisisQuantile
import MarketCrash.OriginalVisitedPrices
import MarketCrash.TwoPulseScalar

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace MarketCrash

def threeBinSignal (Δ r t : ℝ) : ℝ :=
  if t < Δ then 1 else if t < 2*Δ then -(1+r) else r

theorem threeBinSignal_first (Δ r t : ℝ) (ht : t ∈ Ioo 0 Δ) :
    threeBinSignal Δ r t = 1 := by simp [threeBinSignal, ht.2]

theorem threeBinSignal_second (Δ r t : ℝ) (ht : t ∈ Ioo Δ (2*Δ)) :
    threeBinSignal Δ r t = -(1+r) := by simp [threeBinSignal, not_lt.mpr ht.1.le, ht.2]

theorem threeBinSignal_third (Δ r t : ℝ) (hΔ : 0 ≤ Δ) (ht : t ∈ Ioo (2*Δ) (3*Δ)) :
    threeBinSignal Δ r t = r := by
  have h1 : ¬t < Δ := by linarith [ht.1]
  have h2 : ¬t < 2*Δ := by linarith [ht.1]
  simp [threeBinSignal,h1,h2]

theorem threeBinSignal_abs_le (Δ r t : ℝ) (hr : 0 ≤ r) :
    |threeBinSignal Δ r t| ≤ 1+r := by
  unfold threeBinSignal
  split
  · simp; linarith
  · split
    · rw [abs_neg, abs_of_nonneg (by linarith)]
    · rw [abs_of_nonneg hr]; linarith

theorem ae_eq_on_interval_of_eqOn_open (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hfg : ∀ t ∈ Ioo a b, f t = g t) :
    f =ᵐ[volume.restrict (uIoc a b)] g := by
  rw [uIoc_of_le hab]
  filter_upwards [(Set.countable_singleton b).ae_not_mem (volume.restrict (Ioc a b)),
    ae_restrict_mem measurableSet_Ioc] with t hn ht
  simp only [mem_singleton_iff] at hn
  exact hfg t ⟨ht.1, lt_of_le_of_ne ht.2 hn⟩

theorem threeBinSignal_integral (Δ r : ℝ) (hΔ : 0 < Δ) :
    IntervalIntegrable (threeBinSignal Δ r) volume 0 (3*Δ) ∧
      (∫ t in (0 : ℝ)..(3*Δ), threeBinSignal Δ r t) = 0 := by
  have h1 := ae_eq_on_interval_of_eqOn_open (threeBinSignal Δ r) (fun _ => 1) 0 Δ hΔ.le
    (fun t ht => threeBinSignal_first Δ r t ht)
  have h2 := ae_eq_on_interval_of_eqOn_open (threeBinSignal Δ r) (fun _ => -(1+r)) Δ (2*Δ)
    (by linarith) (fun t ht => threeBinSignal_second Δ r t ht)
  have h3 := ae_eq_on_interval_of_eqOn_open (threeBinSignal Δ r) (fun _ => r) (2*Δ) (3*Δ)
    (by linarith) (fun t ht => threeBinSignal_third Δ r t hΔ.le ht)
  have hi1 := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 Δ).congr h1.symm
  have hi2 := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => -(1+r)) volume Δ (2*Δ)).congr h2.symm
  have hi3 := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => r) volume (2*Δ) (3*Δ)).congr h3.symm
  refine ⟨(hi1.trans hi2).trans hi3, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr_ae_restrict h1,
    intervalIntegral.integral_congr_ae_restrict h2,
    intervalIntegral.integral_congr_ae_restrict h3]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem integral_const_exp_mul (c ρ a b : ℝ) (hρ : ρ ≠ 0) :
    (∫ t in a..b, c * Real.exp (ρ*t)) = c/ρ*(Real.exp (ρ*b)-Real.exp (ρ*a)) := by
  have hd (t : ℝ) : HasDerivAt (fun s => c/ρ*Real.exp (ρ*s)) (c*Real.exp (ρ*t)) t := by
    convert (((hasDerivAt_id t).const_mul ρ).exp).const_mul (c/ρ) using 1 <;> dsimp
    field_simp [hρ]
    ring
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((show Continuous (fun t => c*Real.exp (ρ*t)) by fun_prop).intervalIntegrable a b)
  rw [hh]
  ring

theorem threeBinSignal_weighted_cancellation (Δ ρ : ℝ) (hΔ : 0 < Δ) (hρ : ρ ≠ 0) :
    IntervalIntegrable (fun t => threeBinSignal Δ (Real.exp (-ρ*Δ)) t * Real.exp (ρ*t)) volume 0 (3*Δ) ∧
    (∫ t in (0 : ℝ)..(3*Δ), threeBinSignal Δ (Real.exp (-ρ*Δ)) t * Real.exp (ρ*t)) = 0 := by
  let r := Real.exp (-ρ*Δ)
  let w := fun t => threeBinSignal Δ r t * Real.exp (ρ*t)
  have h1 := ae_eq_on_interval_of_eqOn_open w (fun t => 1*Real.exp (ρ*t)) 0 Δ hΔ.le
    (fun t ht => by dsimp [w]; rw [threeBinSignal_first Δ r t ht])
  have h2 := ae_eq_on_interval_of_eqOn_open w (fun t => -(1+r)*Real.exp (ρ*t)) Δ (2*Δ)
    (by linarith) (fun t ht => by dsimp [w]; rw [threeBinSignal_second Δ r t ht])
  have h3 := ae_eq_on_interval_of_eqOn_open w (fun t => r*Real.exp (ρ*t)) (2*Δ) (3*Δ)
    (by linarith) (fun t ht => by dsimp [w]; rw [threeBinSignal_third Δ r t hΔ.le ht])
  have hi (c a b : ℝ) : IntervalIntegrable (fun t => c*Real.exp (ρ*t)) volume a b :=
    (show Continuous (fun t => c*Real.exp (ρ*t)) by fun_prop).intervalIntegrable a b
  have hi1 := (hi 1 0 Δ).congr h1.symm
  have hi2 := (hi (-(1+r)) Δ (2*Δ)).congr h2.symm
  have hi3 := (hi r (2*Δ) (3*Δ)).congr h3.symm
  refine ⟨(hi1.trans hi2).trans hi3, ?_⟩
  change (∫ t in (0 : ℝ)..(3*Δ), w t) = 0
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3,
    ← intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr_ae_restrict h1,
    intervalIntegral.integral_congr_ae_restrict h2,
    intervalIntegral.integral_congr_ae_restrict h3,
    integral_const_exp_mul _ _ _ _ hρ, integral_const_exp_mul _ _ _ _ hρ,
    integral_const_exp_mul _ _ _ _ hρ]
  let E := Real.exp (ρ*Δ)
  have he2 : Real.exp (ρ*(2*Δ)) = E^2 := by
    rw [show ρ*(2*Δ) = ρ*Δ+ρ*Δ by ring,Real.exp_add]
    dsimp [E]
    ring
  have he3 : Real.exp (ρ*(3*Δ)) = E^3 := by
    rw [show ρ*(3*Δ) = ρ*(2*Δ)+ρ*Δ by ring,Real.exp_add,he2]
    dsimp [E]
    ring
  have hrE : r*E = 1 := by
    rw [←Real.exp_add]
    simp
  simp only [mul_zero,Real.exp_zero,he2,he3]
  have he : 1/ρ*(E-1) + (-(1+r))/ρ*(E^2-E) + r/ρ*(E^3-E^2) =
      ((E-1)^2*(r*E-1))/ρ := by ring
  rw [he,hrE]
  simp

def threeBinLinearResponse (Δ ρ h₀ t : ℝ) : ℝ :=
  h₀ * Real.exp (-ρ*t) * ∫ s in (0 : ℝ)..t,
    threeBinSignal Δ (Real.exp (-ρ*Δ)) s * Real.exp (ρ*s)

theorem threeBinLinearResponse_continuous (Δ ρ h₀ : ℝ) (hΔ : 0 < Δ) (hρ : ρ ≠ 0) :
    ContinuousOn (threeBinLinearResponse Δ ρ h₀) (Icc 0 (3*Δ)) := by
  have hi := (threeBinSignal_weighted_cancellation Δ ρ hΔ hρ).1
  have hprim := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  rw [uIcc_of_le (show (0:ℝ) ≤ 3*Δ by linarith)] at hprim
  exact (continuous_const.mul (by fun_prop : Continuous (fun t => Real.exp (-ρ*t)))).continuousOn.mul hprim

theorem threeBinLinearResponse_endpoints (Δ ρ h₀ : ℝ) (hΔ : 0 < Δ) (hρ : ρ ≠ 0) :
    threeBinLinearResponse Δ ρ h₀ 0 = 0 ∧ threeBinLinearResponse Δ ρ h₀ (3*Δ) = 0 := by
  constructor
  · simp [threeBinLinearResponse]
  · unfold threeBinLinearResponse
    rw [(threeBinSignal_weighted_cancellation Δ ρ hΔ hρ).2,mul_zero]

theorem threeBinLinearResponse_first_positive (Δ ρ h₀ t : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (ht : t ∈ Ioo 0 Δ) : 0 < threeBinLinearResponse Δ ρ h₀ t := by
  have heq := ae_eq_on_interval_of_eqOn_open
    (fun s => threeBinSignal Δ (Real.exp (-ρ*Δ)) s * Real.exp (ρ*s))
    (fun s => 1*Real.exp (ρ*s)) 0 t ht.1.le
    (fun s hs => by dsimp only; rw [threeBinSignal_first Δ _ s ⟨hs.1,hs.2.trans ht.2⟩])
  unfold threeBinLinearResponse
  rw [intervalIntegral.integral_congr_ae_restrict heq,integral_const_exp_mul _ _ _ _ hρ.ne']
  simp only [mul_zero,Real.exp_zero,one_div]
  exact mul_pos (mul_pos hh₀ (Real.exp_pos _))
    (mul_pos (inv_pos.mpr hρ) (sub_pos.mpr ((Real.one_lt_exp_iff).mpr (mul_pos hρ ht.1))))

theorem threeBinLinearResponse_energy_positive (Δ ρ h₀ : ℝ) (hΔ : 0 < Δ)
    (hρ : 0 < ρ) (hh₀ : 0 < h₀) :
    0 < ∫ t in (0 : ℝ)..(3*Δ), Real.exp (-ρ*(3*Δ-t)) * (threeBinLinearResponse Δ ρ h₀ t)^2 := by
  apply intervalIntegral.integral_pos (by linarith)
  · exact (show Continuous (fun t => Real.exp (-ρ*(3*Δ-t))) by fun_prop).continuousOn.mul
      ((threeBinLinearResponse_continuous Δ ρ h₀ hΔ hρ.ne').pow 2)
  · intro t _
    exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  · refine ⟨Δ/2, ⟨by linarith,by linarith⟩, ?_⟩
    exact mul_pos (Real.exp_pos _) (sq_pos_of_pos
      (threeBinLinearResponse_first_positive Δ ρ h₀ (Δ/2) hρ hh₀ ⟨by linarith,by linarith⟩))

theorem threeBinSignal_continuousAt (Δ r t : ℝ) (h1 : t ≠ Δ) (h2 : t ≠ 2*Δ) :
    ContinuousAt (threeBinSignal Δ r) t := by
  by_cases ht1 : t < Δ
  · have he : threeBinSignal Δ r =ᶠ[nhds t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht1] with s hs
      have hs' : s < Δ := hs
      simp [threeBinSignal,hs']
    exact he.continuousAt
  · have hgt1 : Δ < t := lt_of_le_of_ne (not_lt.mp ht1) h1.symm
    by_cases ht2 : t < 2*Δ
    · have he : threeBinSignal Δ r =ᶠ[nhds t] fun _ => -(1+r) := by
        filter_upwards [Ioo_mem_nhds hgt1 ht2] with s hs
        simp [threeBinSignal,not_lt.mpr hs.1.le,hs.2]
      exact he.continuousAt
    · have hgt2 : 2*Δ < t := lt_of_le_of_ne (not_lt.mp ht2) h2.symm
      have he : threeBinSignal Δ r =ᶠ[nhds t] fun _ => r := by
        filter_upwards [Ioi_mem_nhds hgt1,Ioi_mem_nhds hgt2] with s hs1 hs2
        have hs1' : Δ < s := hs1
        have hs2' : 2*Δ < s := hs2
        simp [threeBinSignal,not_lt.mpr hs1'.le,not_lt.mpr hs2'.le]
      exact he.continuousAt

theorem threeBinLinearResponse_hasDerivAt (Δ ρ h₀ t : ℝ) (hΔ : 0 < Δ) (hρ : ρ ≠ 0)
    (ht : t ∈ Icc 0 (3*Δ)) (h1 : t ≠ Δ) (h2 : t ≠ 2*Δ) :
    HasDerivAt (threeBinLinearResponse Δ ρ h₀)
      (-ρ*threeBinLinearResponse Δ ρ h₀ t+h₀*threeBinSignal Δ (Real.exp (-ρ*Δ)) t) t := by
  let w := fun s => threeBinSignal Δ (Real.exp (-ρ*Δ)) s * Real.exp (ρ*s)
  have hw : ContinuousAt w t := (threeBinSignal_continuousAt Δ _ t h1 h2).mul (by fun_prop)
  have hm : Measurable w := by
    have hsig : Measurable (threeBinSignal Δ (Real.exp (-ρ*Δ))) :=
      Measurable.ite measurableSet_Iio measurable_const
        (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    exact hsig.mul (by fun_prop)
  have hi := (threeBinSignal_weighted_cancellation Δ ρ hΔ hρ).1.mono_set
    (show uIcc 0 t ⊆ uIcc 0 (3*Δ) by rw [uIcc_of_le (by linarith : (0:ℝ) ≤ 3*Δ)]; exact uIcc_subset_Icc ⟨le_rfl,by linarith⟩ ht)
  have hG := intervalIntegral.integral_hasDerivAt_right hi hm.aestronglyMeasurable.stronglyMeasurableAtFilter hw
  have hE := (((hasDerivAt_id t).const_mul (-ρ)).exp).const_mul h₀
  have hd := hE.mul hG
  convert hd using 1
  have he : Real.exp (-ρ*t)*Real.exp (ρ*t) = 1 := by rw [←Real.exp_add]; simp
  dsimp [threeBinLinearResponse,w]
  linear_combination -h₀ * threeBinSignal Δ (Real.exp (-ρ*Δ)) t * he

theorem threeBinLinearResponse_lipschitz (Δ ρ h₀ : ℝ) (hΔ : 0 < Δ) (hρ : 0 < ρ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (threeBinLinearResponse Δ ρ h₀) (Icc 0 (3*Δ)) := by
  let r := Real.exp (-ρ*Δ)
  let w := fun t => threeBinSignal Δ r t * Real.exp (ρ*t)
  let G := fun t => ∫ s in (0:ℝ)..t, w s
  let E := fun t => h₀*Real.exp (-ρ*t)
  let C := (1+r)*Real.exp (ρ*(3*Δ))
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hC : 0 ≤ C := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hw : ∀ t ∈ Icc 0 (3*Δ), ‖w t‖ ≤ C := by
    intro t ht
    simp only [w,Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (threeBinSignal_abs_le Δ r t hr)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hρ.le)) (Real.exp_pos _).le (by linarith)
  have hi := (threeBinSignal_weighted_cancellation Δ ρ hΔ hρ.ne').1
  have hG := bounded_primitive_lipschitz w 0 (3*Δ) C (by linarith) hC hi hw
  have hGb : ∀ t ∈ Icc 0 (3*Δ), |G t| ≤ C*(3*Δ) := by
    intro t ht
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (fun s hs => hw s ((uIcc_subset_Icc ⟨le_rfl,by linarith⟩ ht) (uIoc_subset_uIcc hs)))
    rw [sub_zero,abs_of_nonneg ht.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left ht.2 hC)
  have hEbd : ∀ t ∈ Icc 0 (3*Δ), |E t| ≤ |h₀| := by
    intro t ht
    have he : Real.exp (-ρ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    simpa only [E,abs_mul,abs_of_pos (Real.exp_pos _),mul_one] using
      mul_le_mul_of_nonneg_left he (abs_nonneg h₀)
  have hEd (t : ℝ) : HasDerivAt E (h₀*(-ρ*Real.exp (-ρ*t))) t := by
    convert ((((hasDerivAt_id t).const_mul (-ρ)).exp).const_mul h₀) using 1 <;> dsimp [E] <;> ring
  have hEL : LipschitzOnWith ⟨|h₀| *ρ,by positivity⟩ E (Icc 0 (3*Δ)) := by
    apply (convex_Icc 0 (3*Δ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t _ => (hEd t).hasDerivWithinAt)
    intro t ht
    change |h₀*(-ρ*Real.exp (-ρ*t))| ≤ |h₀| *ρ
    rw [abs_mul,abs_mul,abs_neg,abs_of_pos hρ,abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-ρ*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.1])
    nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg h₀) hρ.le)]
  refine ⟨_,bounded_lipschitz_product E G (Icc 0 (3*Δ)) _ _ |h₀| (C*(3*Δ))
    (abs_nonneg _) (by positivity) hEL hG hEbd hGb⟩

theorem exponential_weight_hasDerivAt (ρ T t : ℝ) :
    HasDerivAt (fun s => Real.exp (-ρ*(T-s))) (ρ*Real.exp (-ρ*(T-t))) t := by
  convert ((((hasDerivAt_const t T).sub (hasDerivAt_id t)).const_mul (-ρ)).exp) using 1 <;> simp <;> ring

theorem exponential_weight_lipschitz (ρ T : ℝ) (hρ : 0 ≤ ρ) :
    LipschitzOnWith ⟨ρ,hρ⟩ (fun t => Real.exp (-ρ*(T-t))) (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (exponential_weight_hasDerivAt ρ T t).hasDerivWithinAt)
  intro t ht
  change |ρ*Real.exp (-ρ*(T-t))| ≤ ρ
  rw [abs_mul,abs_of_nonneg hρ,abs_of_pos (Real.exp_pos _)]
  have he : Real.exp (-ρ*(T-t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [ht.2])
  nlinarith [mul_le_mul_of_nonneg_left he hρ]

theorem weighted_linear_energy_identity (ρ T h₀ : ℝ) (hρ : 0 ≤ ρ) (hT : 0 ≤ T)
    (f y : ℝ → ℝ) (K : ℝ≥0) (hy : LipschitzOnWith K y (Icc 0 T))
    (hy0 : y 0 = 0) (hyT : y T = 0) (hf : IntervalIntegrable f volume 0 T)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → HasDerivAt y (-ρ*y t+h₀*f t) t) :
    2*h₀*(∫ t in (0:ℝ)..T, Real.exp (-ρ*(T-t))*f t*y t) =
      ρ*(∫ t in (0:ℝ)..T, Real.exp (-ρ*(T-t))*(y t)^2) := by
  let W := fun t => Real.exp (-ρ*(T-t))
  let B : ℝ := K*T
  have hB : 0 ≤ B := mul_nonneg K.coe_nonneg hT
  have hyb : ∀ t ∈ Icc 0 T, |y t| ≤ B := by
    intro t ht
    have hh := hy.dist_le_mul t ht 0 (left_mem_Icc.mpr hT)
    have hh' : |y t| ≤ K*t := by simpa only [hy0,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] using hh
    exact hh'.trans (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)
  have hWb : ∀ t ∈ Icc 0 T, |W t| ≤ 1 := by
    intro t ht
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by nlinarith [ht.2])
  have hyy := bounded_lipschitz_product y y (Icc 0 T) K K B B hB hB hy hy hyb hyb
  have hyyb : ∀ t ∈ Icc 0 T, |y t*y t| ≤ B*B := by
    intro t ht
    rw [abs_mul]
    exact mul_le_mul (hyb t ht) (hyb t ht) (abs_nonneg _) hB
  have hE := bounded_lipschitz_product W (fun t => y t*y t) (Icc 0 T) ⟨ρ,hρ⟩ _
    1 (B*B) (by norm_num) (mul_nonneg hB hB) (exponential_weight_lipschitz ρ T hρ) hyy hWb hyyb
  have hE' : ∃ C : ℝ≥0, LipschitzOnWith C (fun t => W t*(y t)^2) (Icc 0 T) := by
    exact ⟨_,by simpa only [pow_two] using hE⟩
  obtain ⟨C,hE'⟩ := hE'
  have hEd : ∀ᵐ t ∂volume, t ∈ Ioo 0 T →
      HasDerivAt (fun t => W t*(y t)^2) (W t*(2*h₀*f t*y t-ρ*(y t)^2)) t := by
    filter_upwards [hd] with t ht hit
    have hh := (exponential_weight_hasDerivAt ρ T t).mul ((ht hit).pow 2)
    convert hh using 1 <;> dsimp [W] <;> ring
  obtain ⟨_,hFTC⟩ := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hE' hT hEd
  have hWc : ContinuousOn W (Icc 0 T) := (show Continuous W by dsimp [W];fun_prop).continuousOn
  have heI : IntervalIntegrable (fun t => W t*(y t)^2) volume 0 T :=
    (hWc.mul (hy.continuousOn.pow 2)).intervalIntegrable_of_Icc hT
  have hfI : IntervalIntegrable (fun t => W t*f t*y t) volume 0 T := by
    convert hf.mul_continuousOn (by rw [uIcc_of_le hT];exact hWc.mul hy.continuousOn) using 1
    funext t
    ring
  have heq : (fun t => W t*(2*h₀*f t*y t-ρ*(y t)^2)) =
      (fun t => (2*h₀)*(W t*f t*y t)-ρ*(W t*(y t)^2)) := by funext t;ring
  rw [heq,intervalIntegral.integral_sub (hfI.const_mul _) (heI.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hFTC
  simp only [hy0,hyT,pow_two,mul_zero,sub_self] at hFTC
  simpa only [W,pow_two] using sub_eq_zero.mp hFTC

theorem threeBinLinearResponse_energy_identity (Δ ρ h₀ : ℝ) (hΔ : 0 < Δ) (hρ : 0 < ρ) :
    2*h₀*(∫ t in (0:ℝ)..(3*Δ), Real.exp (-ρ*(3*Δ-t))*
      threeBinSignal Δ (Real.exp (-ρ*Δ)) t*threeBinLinearResponse Δ ρ h₀ t) =
      ρ*(∫ t in (0:ℝ)..(3*Δ), Real.exp (-ρ*(3*Δ-t))*(threeBinLinearResponse Δ ρ h₀ t)^2) := by
  obtain ⟨K,hK⟩ := threeBinLinearResponse_lipschitz Δ ρ h₀ hΔ hρ
  have he := threeBinLinearResponse_endpoints Δ ρ h₀ hΔ hρ.ne'
  apply weighted_linear_energy_identity ρ (3*Δ) h₀ hρ.le (by linarith)
    (threeBinSignal Δ (Real.exp (-ρ*Δ))) (threeBinLinearResponse Δ ρ h₀) K hK he.1 he.2
    (threeBinSignal_integral Δ (Real.exp (-ρ*Δ)) hΔ).1
  filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ Δ by simp [ae_iff],
    show ∀ᵐ t : ℝ ∂volume, t ≠ 2*Δ by simp [ae_iff]] with t h1 h2 ht
  exact threeBinLinearResponse_hasDerivAt Δ ρ h₀ t hΔ hρ.ne' ⟨ht.1.le,ht.2.le⟩ h1 h2

def threeBinSecondResponse (Δ ρ h₀ h₁ t : ℝ) : ℝ :=
  h₁*Real.exp (-ρ*t) * ∫ s in (0:ℝ)..t,
    threeBinSignal Δ (Real.exp (-ρ*Δ)) s*Real.exp (ρ*s)*threeBinLinearResponse Δ ρ h₀ s

theorem threeBinSecondResponse_terminal (Δ ρ h₀ h₁ : ℝ) (hΔ : 0 < Δ) (hρ : 0 < ρ) (hh₀ : h₀ ≠ 0) :
    threeBinSecondResponse Δ ρ h₀ h₁ (3*Δ) = ρ*h₁/(2*h₀)*
      ∫ t in (0:ℝ)..(3*Δ), Real.exp (-ρ*(3*Δ-t))*(threeBinLinearResponse Δ ρ h₀ t)^2 := by
  have hi := threeBinLinearResponse_energy_identity Δ ρ h₀ hΔ hρ
  have heq : threeBinSecondResponse Δ ρ h₀ h₁ (3*Δ) = h₁*
      ∫ t in (0:ℝ)..(3*Δ), Real.exp (-ρ*(3*Δ-t))*
        threeBinSignal Δ (Real.exp (-ρ*Δ)) t*threeBinLinearResponse Δ ρ h₀ t := by
    unfold threeBinSecondResponse
    rw [mul_assoc,← intervalIntegral.integral_const_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    have he : Real.exp (-ρ*(3*Δ-t)) = Real.exp (-ρ*(3*Δ))*Real.exp (ρ*t) := by
      rw [←Real.exp_add]
      congr 1
      ring
    dsimp only
    rw [he]
    ring
  rw [heq]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (mul_ne_zero (by norm_num) hh₀)).mpr
  linear_combination h₁*hi

theorem threeBinSecondResponse_terminal_negative (Δ ρ h₀ h₁ : ℝ) (hΔ : 0 < Δ)
    (hρ : 0 < ρ) (hh₀ : 0 < h₀) (hh₁ : h₁ < 0) :
    threeBinSecondResponse Δ ρ h₀ h₁ (3*Δ) < 0 := by
  rw [threeBinSecondResponse_terminal Δ ρ h₀ h₁ hΔ hρ hh₀.ne']
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hρ hh₁) (by positivity))
    (threeBinLinearResponse_energy_positive Δ ρ h₀ hΔ hρ hh₀)

theorem threeBinSignal_continuousWithinAt_right (Δ r t : ℝ) :
    ContinuousWithinAt (threeBinSignal Δ r) (Ici t) t := by
  have he : threeBinSignal Δ r =ᶠ[nhdsWithin t (Ici t)] fun _ => threeBinSignal Δ r t := by
    by_cases ht1 : t < Δ
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht1)] with s hs
      have hs' : s < Δ := hs
      simp [threeBinSignal,ht1,hs']
    · by_cases ht2 : t < 2*Δ
      · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds ht2)] with s hs hsu
        have hs' : ¬s < Δ := not_lt.mpr ((not_lt.mp ht1).trans hs)
        have hsu' : s < 2*Δ := hsu
        simp [threeBinSignal,ht1,ht2,hs',hsu']
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs1 : ¬s < Δ := not_lt.mpr ((not_lt.mp ht1).trans hs)
        have hs2 : ¬s < 2*Δ := not_lt.mpr ((not_lt.mp ht2).trans hs)
        simp [threeBinSignal,ht1,ht2,hs1,hs2]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem threeBinLinearResponse_hasDerivWithinAt_right (Δ ρ h₀ t : ℝ)
    (hΔ : 0 < Δ) (hρ : ρ ≠ 0) (ht : t ∈ Icc 0 (3*Δ)) :
    HasDerivWithinAt (threeBinLinearResponse Δ ρ h₀)
      (-ρ*threeBinLinearResponse Δ ρ h₀ t+h₀*threeBinSignal Δ (Real.exp (-ρ*Δ)) t) (Ici t) t := by
  let w := fun s => threeBinSignal Δ (Real.exp (-ρ*Δ)) s * Real.exp (ρ*s)
  have hw : ContinuousWithinAt w (Ici t) t :=
    (threeBinSignal_continuousWithinAt_right Δ _ t).mul ((by fun_prop : ContinuousAt (fun s => Real.exp (ρ*s)) t).continuousWithinAt)
  have hm : Measurable w := by
    have hsig : Measurable (threeBinSignal Δ (Real.exp (-ρ*Δ))) :=
      Measurable.ite measurableSet_Iio measurable_const (Measurable.ite measurableSet_Iio measurable_const measurable_const)
    exact hsig.mul (by fun_prop)
  have hi := (threeBinSignal_weighted_cancellation Δ ρ hΔ hρ).1.mono_set
    (show uIcc 0 t ⊆ uIcc 0 (3*Δ) by rw [uIcc_of_le (by linarith : (0:ℝ) ≤ 3*Δ)]; exact uIcc_subset_Icc ⟨le_rfl,by linarith⟩ ht)
  have hG := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t) hi
    hm.aestronglyMeasurable.stronglyMeasurableAtFilter (hw.mono Ioi_subset_Ici_self)
  have hE := ((((hasDerivAt_id t).const_mul (-ρ)).exp).const_mul h₀).hasDerivWithinAt (s := Ici t)
  have hd := hE.mul hG
  convert hd using 1
  have he : Real.exp (-ρ*t)*Real.exp (ρ*t) = 1 := by rw [←Real.exp_add]; simp
  dsimp [threeBinLinearResponse,w]
  linear_combination -h₀ * threeBinSignal Δ (Real.exp (-ρ*Δ)) t * he

theorem threeBinSecondResponse_continuous (Δ ρ h₀ h₁ : ℝ) (hΔ : 0 < Δ) (hρ : ρ ≠ 0) :
    ContinuousOn (threeBinSecondResponse Δ ρ h₀ h₁) (Icc 0 (3*Δ)) := by
  have hy := threeBinLinearResponse_continuous Δ ρ h₀ hΔ hρ
  have hi := (threeBinSignal_weighted_cancellation Δ ρ hΔ hρ).1.mul_continuousOn
    (by rw [uIcc_of_le (show (0:ℝ) ≤ 3*Δ by linarith)];exact hy)
  have hp := intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  rw [uIcc_of_le (show (0:ℝ) ≤ 3*Δ by linarith)] at hp
  exact (show Continuous (fun t => h₁*Real.exp (-ρ*t)) by fun_prop).continuousOn.mul hp

theorem threeBinSecondResponse_hasDerivWithinAt_right (Δ ρ h₀ h₁ t : ℝ)
    (hΔ : 0 < Δ) (hρ : ρ ≠ 0) (ht : t ∈ Ico 0 (3*Δ)) :
    HasDerivWithinAt (threeBinSecondResponse Δ ρ h₀ h₁)
      (-ρ*threeBinSecondResponse Δ ρ h₀ h₁ t+
        h₁*threeBinSignal Δ (Real.exp (-ρ*Δ)) t*threeBinLinearResponse Δ ρ h₀ t) (Ici t) t := by
  let w := fun s => threeBinSignal Δ (Real.exp (-ρ*Δ)) s*Real.exp (ρ*s)*threeBinLinearResponse Δ ρ h₀ s
  have hy := threeBinLinearResponse_continuous Δ ρ h₀ hΔ hρ
  have hi : IntervalIntegrable w volume 0 (3*Δ) :=
    (threeBinSignal_weighted_cancellation Δ ρ hΔ hρ).1.mul_continuousOn
      (by rw [uIcc_of_le (show (0:ℝ) ≤ 3*Δ by linarith)];exact hy)
  have hmIcc := ((intervalIntegrable_iff_integrableOn_Icc_of_le (show (0:ℝ) ≤ 3*Δ by linarith)).mp hi).aestronglyMeasurable
  have hm : StronglyMeasurableAtFilter w (nhdsWithin t (Ici t)) :=
    ⟨Icc 0 (3*Δ),Icc_mem_nhdsGE_of_mem ht,hmIcc⟩
  have hyw := (hy t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hw : ContinuousWithinAt w (Ici t) t :=
    ((threeBinSignal_continuousWithinAt_right Δ _ t).mul
      ((by fun_prop : ContinuousAt (fun s => Real.exp (ρ*s)) t).continuousWithinAt)).mul hyw
  have hisub := hi.mono_set (show uIcc 0 t ⊆ uIcc 0 (3*Δ) by
    rw [uIcc_of_le (show (0:ℝ) ≤ 3*Δ by linarith)]
    exact uIcc_subset_Icc ⟨le_rfl,by linarith⟩ ⟨ht.1,ht.2.le⟩)
  have hG := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t) hisub
    (hm.filter_mono (nhdsWithin_mono _ Ioi_subset_Ici_self)) (hw.mono Ioi_subset_Ici_self)
  have hE := ((((hasDerivAt_id t).const_mul (-ρ)).exp).const_mul h₁).hasDerivWithinAt (s := Ici t)
  have hd := hE.mul hG
  convert hd using 1
  have he : Real.exp (-ρ*t)*Real.exp (ρ*t) = 1 := by rw [←Real.exp_add];simp
  dsimp [threeBinSecondResponse,w]
  linear_combination -h₁ * threeBinSignal Δ (Real.exp (-ρ*Δ)) t * threeBinLinearResponse Δ ρ h₀ t * he

set_option maxHeartbeats 800000 in
theorem three_bin_nonlinear_approximation (F ρ Δ : ℝ) (g : Response)
    (hρ : 0 < ρ) (hΔ : 0 < Δ) (m : LocalResponseModel F g) :
    ∃ ε A B : ℝ, 0 < ε ∧ 0 < A ∧ 0 < B ∧ ∀ p : ℝ, |p| < ε →
      ∃ (X : ℝ → ℝ) (K : ℝ≥0), X 0 = F ∧ LipschitzOnWith K X (Icc 0 (3*Δ)) ∧
        (∀ t ∈ Ico 0 (3*Δ), HasDerivWithinAt X
          (-ρ*(X t-F)+p*threeBinSignal Δ (Real.exp (-ρ*Δ)) t*(g.impact (X t)/X t)) (Ici t) t) ∧
        (∀ t ∈ Icc 0 (3*Δ), 0 < X t ∧ |X t-F| ≤ B*|p|) ∧
        ∀ t ∈ Icc 0 (3*Δ),
          |X t-(F+p*threeBinLinearResponse Δ ρ (g.impact F/F) t+
            p^2*threeBinSecondResponse Δ ρ (g.impact F/F)
              ((F*deriv g.impact F-g.impact F)/F^2) t)| ≤ A*|p|^3 := by
  let h₀ := g.impact F/F
  let h₁ := (F*deriv g.impact F-g.impact F)/F^2
  let y := threeBinLinearResponse Δ ρ h₀
  let z := threeBinSecondResponse Δ ρ h₀ h₁
  let r := Real.exp (-ρ*Δ)
  let D := 1+r
  have hr : 0 < r := Real.exp_pos _
  have hD : 0 < D := by dsimp [D];linarith
  obtain ⟨Y,hY,hyb⟩ := continuousOn_compact_abs_bound y (Icc 0 (3*Δ)) isCompact_Icc
    (threeBinLinearResponse_continuous Δ ρ h₀ hΔ hρ.ne')
  obtain ⟨Z,hZ,hzb⟩ := continuousOn_compact_abs_bound z (Icc 0 (3*Δ)) isCompact_Icc
    (threeBinSecondResponse_continuous Δ ρ h₀ h₁ hΔ hρ.ne')
  let R₀ := D*(|h₁| *Z+m.Q*(Y+Z)^2)
  have hR₀ : 0 ≤ R₀ := mul_nonneg hD.le (add_nonneg (mul_nonneg (abs_nonneg _) hZ.le)
    (mul_nonneg m.remainder_nonnegative (sq_nonneg _)))
  let L : ℝ≥0 := ⟨|ρ|,abs_nonneg _⟩+m.L
  obtain ⟨G,hG,hGb⟩ := gronwallBound_uniform_linear_error L (3*Δ)
  let A := G*R₀+1
  have hA : 0 < A := by dsimp [A];nlinarith
  let B := Y+Z+A
  have hB : 0 < B := by dsimp [B];linarith
  let ε := min 1 (min (1/D) (m.δ/B))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (div_pos (by norm_num) hD) (div_pos m.radius_positive hB))
  refine ⟨ε,A,B,hε,hA,hB,?_⟩
  intro p hp
  have hp1 : |p| ≤ 1 := (hp.trans_le (min_le_left _ _)).le
  have hpB : B*|p| < m.δ := by
    have hh : |p| < m.δ/B := hp.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    simpa only [mul_comm] using (lt_div_iff₀ hB).mp hh
  have hpf (c : ℝ) (hc : |c| ≤ D) : |p*c| ≤ 1 := by
    rw [abs_mul]
    have hh : |p| ≤ 1/D := (hp.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg _)).trans ((le_div_iff₀ hD).mp hh)
  let Q := fun t => F+p*y t+p^2*z t
  have hQb : ∀ t ∈ Icc 0 (3*Δ), |Q t-F| ≤ |p| *(Y+Z) := by
    intro t ht
    have hp2 : |p|^2 ≤ |p| := by nlinarith [abs_nonneg p]
    have he : Q t-F = p*y t+p^2*z t := by dsimp [Q];ring
    rw [he]
    calc
      _ ≤ |p*y t|+|p^2*z t| := abs_add_le _ _
      _ = |p| * |y t|+|p|^2 * |z t| := by rw [abs_mul,abs_mul,abs_pow]
      _ ≤ |p| *Y+|p|^2*Z := add_le_add (mul_le_mul_of_nonneg_left (hyb t ht) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left (hzb t ht) (sq_nonneg _))
      _ ≤ _ := by nlinarith
  have hQstrip : ∀ t ∈ Icc 0 (3*Δ), Q t ∈ Icc (F-m.δ) (F+m.δ) := by
    intro t ht
    have hh : |Q t-F| < m.δ := (hQb t ht).trans_lt (by dsimp [B] at hpB;nlinarith [abs_nonneg p])
    have hh' := abs_lt.mp hh
    constructor <;> linarith
  let V := fun c => clampedResponseField F ρ m.δ (p*c) m.H
  let C := |ρ| *m.δ+m.M
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (abs_nonneg _) m.radius_positive.le) m.bound_nonnegative
  have hVL (c : ℝ) (hc : |c| ≤ D) : LipschitzWith L (V c) := by
    apply (clampedResponseField_lipschitz F ρ m.δ (p*c) m.H m.L m.lipschitz).weaken
    change |ρ|+|p*c| *m.L ≤ |ρ|+m.L
    nlinarith [mul_le_mul_of_nonneg_right (hpf c hc) m.L.coe_nonneg]
  have hVC (c : ℝ) (hc : |c| ≤ D) : ∀ x, ‖V c x‖ ≤ C := by
    intro x
    exact (clampedResponseField_bound F ρ m.δ (p*c) m.M m.H m.radius_positive.le m.bounded x).trans
      (by dsimp [C];nlinarith [mul_le_mul_of_nonneg_right (hpf c hc) m.bound_nonnegative])
  have hc₁ : |(1:ℝ)| ≤ D := by dsimp [D];simp;linarith
  have hc₂ : |-(1+r)| ≤ D := by rw [abs_neg,abs_of_pos hD]
  have hc₃ : |r| ≤ D := by rw [abs_of_pos hr];dsimp [D];linarith
  let W := fun t => if t < Δ then V 1 else if t < 2*Δ then V (-(1+r)) else V r
  have hW (t x : ℝ) : W t x = clampedResponseField F ρ m.δ
      (p*threeBinSignal Δ r t) m.H x := by
    dsimp [W,V,threeBinSignal]
    split
    · rfl
    · split <;> rfl
  have hQ : ContinuousOn Q (Icc 0 (3*Δ)) :=
    (continuousOn_const.add (continuousOn_const.mul
      (threeBinLinearResponse_continuous Δ ρ h₀ hΔ hρ.ne'))).add
      (continuousOn_const.mul (threeBinSecondResponse_continuous Δ ρ h₀ h₁ hΔ hρ.ne'))
  let Q' := fun t => -ρ*(Q t-F)+p*threeBinSignal Δ r t*(h₀+h₁*p*y t)
  have hQd : ∀ t ∈ Ico 0 (3*Δ), HasDerivWithinAt Q (Q' t) (Ici t) t := by
    intro t ht
    have yd := threeBinLinearResponse_hasDerivWithinAt_right Δ ρ h₀ t hΔ hρ.ne' ⟨ht.1,ht.2.le⟩
    have zd := threeBinSecondResponse_hasDerivWithinAt_right Δ ρ h₀ h₁ t hΔ hρ.ne' ht
    have hd := (((hasDerivAt_const t F).hasDerivWithinAt.add (yd.const_mul p)).add (zd.const_mul (p^2)))
    convert hd using 1 <;> dsimp [Q,Q',y,z,r] <;> ring
  have hres : ∀ t ∈ Ico 0 (3*Δ), dist (Q' t) (W t (Q t)) ≤ R₀*|p|^3 := by
    intro t ht
    have hti : t ∈ Icc 0 (3*Δ) := ⟨ht.1,ht.2.le⟩
    have hTaylor := m.taylor (Q t) (hQstrip t hti)
    have he : Q t-F = p*y t+p^2*z t := by dsimp [Q];ring
    rw [he] at hTaylor
    have hres := nonlinear_response_cubic_residual m.H F h₀ h₁ p (y t) (z t) m.Q Y Z
      (threeBinSignal Δ r t) hp1 m.remainder_nonnegative hY.le hZ.le (hyb t hti) (hzb t hti) hTaylor
    have he' : Q' t-W t (Q t) = p*threeBinSignal Δ r t*(h₀+h₁*p*y t-m.H (Q t)) := by
      rw [hW,clampedResponseField,responseClamp_eq F m.δ (Q t) (hQstrip t hti)]
      dsimp [Q']
      ring
    rw [Real.dist_eq,he']
    exact hres.trans (by
      have hf := threeBinSignal_abs_le Δ r t hr.le
      have hh := mul_le_mul_of_nonneg_left hf (mul_nonneg (pow_nonneg (abs_nonneg p) 3)
        (add_nonneg (mul_nonneg (abs_nonneg h₁) hZ.le) (mul_nonneg m.remainder_nonnegative (sq_nonneg (Y+Z)))))
      dsimp [R₀,D]
      convert hh using 1 <;> ring)
  have hQ0 : Q 0 = F := by simp [Q,y,z,threeBinLinearResponse,threeBinSecondResponse]
  obtain ⟨X,K,hX,hXL,hXd,hErr⟩ := three_stage_solution_approximation Δ C F 0 (R₀*|p|^3) hΔ hC
    (V 1) (V (-(1+r))) (V r) L (hVL 1 hc₁) (hVL _ hc₂) (hVL r hc₃)
    (hVC 1 hc₁) (hVC _ hc₂) (hVC r hc₃) Q Q' hQ hQd hres (by simp [hQ0])
  have hE : ∀ t ∈ Icc 0 (3*Δ), |X t-Q t| ≤ A*|p|^3 := by
    intro t ht
    have hh := (hErr t ht).trans (hGb (R₀*|p|^3) (mul_nonneg hR₀ (pow_nonneg (abs_nonneg _) _)) t ht)
    rw [Real.dist_eq] at hh
    dsimp [A]
    nlinarith [pow_nonneg (abs_nonneg p) 3]
  have hXb : ∀ t ∈ Icc 0 (3*Δ), |X t-F| ≤ B*|p| := by
    intro t ht
    have hp3 : |p|^3 ≤ |p| := by
      have hp2 : |p|^2 ≤ 1 := by
        simpa only [pow_two,one_mul] using mul_le_mul hp1 hp1 (abs_nonneg p) (by norm_num : (0:ℝ) ≤ 1)
      calc
        |p|^3 = |p| * |p|^2 := by ring
        _ ≤ |p| * 1 := mul_le_mul_of_nonneg_left hp2 (abs_nonneg p)
        _ = _ := mul_one _
    calc
      _ ≤ |X t-Q t|+|Q t-F| := abs_sub_le _ _ _
      _ ≤ A*|p|^3+|p| *(Y+Z) := add_le_add (hE t ht) (hQb t ht)
      _ ≤ A*|p|+|p| *(Y+Z) := add_le_add_right (mul_le_mul_of_nonneg_left hp3 hA.le) _
      _ = _ := by dsimp [B];ring
  have hXs : ∀ t ∈ Icc 0 (3*Δ), X t ∈ Icc (F-m.δ) (F+m.δ) := by
    intro t ht
    have hh := abs_lt.mp ((hXb t ht).trans_lt hpB)
    constructor <;> linarith
  refine ⟨X,K,hX,hXL,?_,?_,hE⟩
  · intro t ht
    have hh := hXd t ht
    change HasDerivWithinAt X (W t (X t)) (Ici t) t at hh
    rw [hW,clampedResponseField,responseClamp_eq F m.δ (X t) (hXs t ⟨ht.1,ht.2.le⟩),
      m.actual (X t) (hXs t ⟨ht.1,ht.2.le⟩)] at hh
    exact hh
  · intro t ht
    exact ⟨lt_of_lt_of_le (by linarith [m.radius_lt_benchmark]) (hXs t ht).1,hXb t ht⟩

def threeStageFunction (Δ A B C t : ℝ) : ℝ := if t < Δ then A else if t < 2*Δ then B else C

theorem threeStageFunction_measurable (Δ A B C : ℝ) : Measurable (threeStageFunction Δ A B C) :=
  Measurable.ite measurableSet_Iio measurable_const (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem threeStageFunction_nonnegative (Δ A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∀ t, 0 ≤ threeStageFunction Δ A B C t := by
  intro t
  unfold threeStageFunction
  split
  · exact hA
  · split <;> assumption

theorem threeStageFunction_bound (Δ A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    ∀ t, threeStageFunction Δ A B C t ≤ A+B+C := by
  intro t
  unfold threeStageFunction
  split
  · linarith
  · split <;> linarith

theorem threeStageFunction_integral (Δ A B C : ℝ) (hΔ : 0 < Δ) :
    (∫ t in (0:ℝ)..(3*Δ), threeStageFunction Δ A B C t) = Δ*(A+B+C) := by
  have h1 := ae_eq_on_interval_of_eqOn_open (threeStageFunction Δ A B C) (fun _ => A) 0 Δ hΔ.le
    (fun t ht => by dsimp [threeStageFunction];rw [if_pos ht.2])
  have h2 := ae_eq_on_interval_of_eqOn_open (threeStageFunction Δ A B C) (fun _ => B) Δ (2*Δ)
    (by linarith) (fun t ht => by dsimp [threeStageFunction];rw [if_neg (not_lt.mpr ht.1.le),if_pos ht.2])
  have h3 := ae_eq_on_interval_of_eqOn_open (threeStageFunction Δ A B C) (fun _ => C) (2*Δ) (3*Δ)
    (by linarith) (fun t ht => by
      dsimp [threeStageFunction]
      rw [if_neg (show ¬t < Δ by linarith [ht.1]),if_neg (not_lt.mpr ht.1.le)])
  have hi1 := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => A) volume 0 Δ).congr h1.symm
  have hi2 := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume Δ (2*Δ)).congr h2.symm
  have hi3 := (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume (2*Δ) (3*Δ)).congr h3.symm
  rw [←intervalIntegral.integral_add_adjacent_intervals (hi1.trans hi2) hi3,
    ←intervalIntegral.integral_add_adjacent_intervals hi1 hi2,
    intervalIntegral.integral_congr_ae_restrict h1,intervalIntegral.integral_congr_ae_restrict h2,
    intervalIntegral.integral_congr_ae_restrict h3]
  simp only [intervalIntegral.integral_const,smul_eq_mul]
  ring

theorem threeStageFunction_continuousWithinAt_right (Δ A B C t : ℝ) :
    ContinuousWithinAt (threeStageFunction Δ A B C) (Ici t) t := by
  have he : threeStageFunction Δ A B C =ᶠ[nhdsWithin t (Ici t)] fun _ => threeStageFunction Δ A B C t := by
    by_cases ht1 : t < Δ
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht1)] with s hs
      have hs' : s < Δ := hs
      simp [threeStageFunction,ht1,hs']
    · by_cases ht2 : t < 2*Δ
      · filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds ht2)] with s hs hsu
        have hs' : ¬s < Δ := not_lt.mpr ((not_lt.mp ht1).trans hs)
        have hsu' : s < 2*Δ := hsu
        simp [threeStageFunction,ht1,ht2,hs',hsu']
      · filter_upwards [self_mem_nhdsWithin] with s hs
        have hs1 : ¬s < Δ := not_lt.mpr ((not_lt.mp ht1).trans hs)
        have hs2 : ¬s < 2*Δ := not_lt.mpr ((not_lt.mp ht2).trans hs)
        simp [threeStageFunction,ht1,ht2,hs1,hs2]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem rate_stieltjes_derivative_ae (rate : ℝ → ℝ) (G : StieltjesFunction)
    (B T : ℝ) (hB : 0 ≤ B) (hG : LipschitzWith ⟨B,hB⟩ G)
    (hPrim : ∀ t, G t = ∫ u in (0:ℝ)..t, rate u)
    (hm : Measurable rate) (hb : ∀ t, ‖rate t‖ ≤ B)
    (hc : ∀ t, ContinuousWithinAt rate (Ici t) t) :
    ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt G (rate t) t := by
  apply lipschitz_right_derivative_ae G rate 0 T ⟨B,hB⟩ hG.lipschitzOnWith
  intro t _
  have hi := bounded_measurable_intervalIntegrable rate B hm hb 0 t
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici t) (t := Ioi t) hi
    hm.aestronglyMeasurable.stronglyMeasurableAtFilter ((hc t).mono Ioi_subset_Ici_self)
  exact hd.congr_of_eventuallyEq_of_mem (Filter.Eventually.of_forall hPrim) (by simp)

theorem stieltjes_rate_density (rate : ℝ → ℝ) (G : StieltjesFunction) (B : ℝ≥0)
    (hG : LipschitzWith B G) (T : ℝ)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt G (rate t) t)
    (w : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) :
    (∫ u in s..t, w u ∂G.measure) = ∫ u in s..t, w u*rate u := by
  rw [stieltjes_lipschitz_integral_density G hG w s t hst]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hd] with u hu hum
  rw [uIoc_of_le hst] at hum
  rw [(hu ⟨hs.1.trans hum.1.le,hum.2.trans ht.2⟩).deriv]

theorem stieltjes_rate_density_unordered (rate : ℝ → ℝ) (G : StieltjesFunction) (B : ℝ≥0)
    (hG : LipschitzWith B G) (T : ℝ)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt G (rate t) t)
    (w : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    (∫ u in s..t, w u ∂G.measure) = ∫ u in s..t, w u*rate u := by
  rcases le_total s t with hst | hts
  · exact stieltjes_rate_density rate G B hG T hd w s t hs ht hst
  · rw [intervalIntegral.integral_symm t s, intervalIntegral.integral_symm t s]
    rw [stieltjes_rate_density rate G B hG T hd w t s ht hs hts]

/-- Genuine share holdings, retaining an arbitrary initial inventory offset. -/
def rateShares {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (S : ℝ → ι → ℝ) (rates : ℝ → κ → ℝ)
    (H : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  H i + ∫ u in (0:ℝ)..t, tradingInput (pairedMatrix edges) (rates u) i / S u i

theorem rateShares_initial {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (S : ℝ → ι → ℝ) (rates : ℝ → κ → ℝ) (H : ι → ℝ) :
    rateShares edges S rates H 0 = H := by
  funext i
  simp [rateShares]

theorem rateShares_difference {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (S : ℝ → ι → ℝ) (rates : ℝ → κ → ℝ)
    (H : ι → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hi : ∀ i, IntervalIntegrable (fun u => tradingInput (pairedMatrix edges) (rates u) i / S u i) volume 0 T)
    (i : ι) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
    rateShares edges S rates H t i-rateShares edges S rates H s i =
      ∫ u in s..t, tradingInput (pairedMatrix edges) (rates u) i / S u i := by
  have his : IntervalIntegrable (fun u => tradingInput (pairedMatrix edges) (rates u) i / S u i) volume 0 s :=
    (hi i).mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc (left_mem_Icc.mpr hT) hs)
  have hist : IntervalIntegrable (fun u => tradingInput (pairedMatrix edges) (rates u) i / S u i) volume s t :=
    (hi i).mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc hs ht)
  have hh := intervalIntegral.integral_add_adjacent_intervals his hist
  dsimp [rateShares]
  linarith

theorem rateShares_lipschitz_and_nonnegative {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (S : ℝ → ι → ℝ) (rates : ℝ → κ → ℝ)
    (H : ι → ℝ) (T V : ℝ) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hi : ∀ i, IntervalIntegrable (fun u => tradingInput (pairedMatrix edges) (rates u) i / S u i) volume 0 T)
    (hb : ∀ᵐ t ∂volume, t ∈ Icc 0 T → ∀ i,
      |tradingInput (pairedMatrix edges) (rates t) i / S t i| ≤ V)
    (hH : ∀ i, V*T ≤ H i) :
    (∀ i, LipschitzOnWith ⟨V,hV⟩ (fun t => rateShares edges S rates H t i) (Icc 0 T)) ∧
      ∀ t ∈ Icc 0 T, ∀ i, 0 ≤ rateShares edges S rates H t i := by
  have hL (i : ι) : LipschitzOnWith ⟨V,hV⟩ (fun t => rateShares edges S rates H t i) (Icc 0 T) := by
    apply lipschitzOn_of_bounded_primitive _ _ 0 T ⟨V,hV⟩
      (fun s hs t ht => rateShares_difference edges S rates H T hT hi i s t hs ht)
    filter_upwards [hb] with t ht hmem
    exact ht hmem i
  refine ⟨hL, fun t ht i => ?_⟩
  have hh := (hL i).dist_le_mul t ht 0 (left_mem_Icc.mpr hT)
  rw [Real.dist_eq, Real.dist_eq, rateShares_initial] at hh
  have ht' : |t-0| ≤ T := by rw [sub_zero,abs_of_nonneg ht.1]; exact ht.2
  have hbound : |rateShares edges S rates H t i-H i| ≤ V*T :=
    hh.trans (mul_le_mul_of_nonneg_left ht' hV)
  linarith [(le_abs_self (-(rateShares edges S rates H t i-H i))), abs_neg (rateShares edges S rates H t i-H i), hH i]

theorem paired_rate_stieltjes_sum {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (rates : ℝ → κ → ℝ) (G : κ → StieltjesFunction)
    (B : κ → ℝ≥0) (hG : ∀ e, LipschitzWith (B e) (G e)) (T : ℝ)
    (hd : ∀ e, ∀ᵐ t ∂volume, t ∈ Icc 0 T → HasDerivAt (G e) (rates t e) t)
    (q : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T)
    (hq : ∀ e, IntervalIntegrable (fun u => q u*rates u e) volume s t) (i : ι) :
    (∫ u in s..t, q u*tradingInput (pairedMatrix edges) (rates u) i) =
      ∑ e, pairedMatrix edges i e * ∫ u in s..t, q u ∂(G e).measure := by
  have he : (fun u => q u*tradingInput (pairedMatrix edges) (rates u) i) =
      fun u => ∑ e, pairedMatrix edges i e*(q u*rates u e) := by
    funext u
    simp only [tradingInput, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [he, intervalIntegral.integral_finset_sum (fun e _ => (hq e).const_mul _)]
  apply Finset.sum_congr rfl
  intro e _
  rw [intervalIntegral.integral_const_mul,
    stieltjes_rate_density_unordered (fun u => rates u e) (G e) (B e) (hG e) T (hd e) q s t hs ht]

/-- An actual AC price/edge execution produces a genuine original BV piece.
The inventory is the integral of signed shares, and cash offsets are arbitrary. -/
def acSessionOriginalPiece {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (ha : m.a = 0)
    (G : κ → StieltjesFunction) (B : κ → ℝ≥0)
    (hG : ∀ e, LipschitzWith (B e) (G e))
    (hd : ∀ e, ∀ᵐ t ∂volume, t ∈ Icc 0 m.b → HasDerivAt (G e) (m.rates t e) t)
    (H L : ι → ℝ)
    (hshort : ∀ t ∈ Icc 0 m.b, ∀ i, 0 ≤ rateShares edges m.prices m.rates H t i) :
    PhysicalContinuousBVPiece edges where
  a := 0
  b := m.b
  time_order := by simpa [ha] using m.time_order.le
  F := m.F
  rho := m.rho
  response := m.response
  benchmark_positive := m.benchmark_positive
  resilience_nonnegative := m.resilience_nonnegative
  execution := ⟨G⟩
  continuous_execution := fun e => (hG e).continuous.continuousOn
  prices := m.prices
  shares := rateShares edges m.prices m.rates H
  dollarLedger := fun t i => L i + tradingInput (pairedMatrix edges) (fun e => G e t-G e 0) i
  continuous_prices := fun i => by simpa [ha] using m.continuous_prices i
  positive_prices := by simpa [ha] using m.positive_prices
  no_short_sales := hshort
  physical_price_primitive := by
    intro i s hs t ht
    have hT : 0 ≤ m.b := by simpa [ha] using m.time_order.le
    have hsub : uIcc s t ⊆ Icc m.a m.b := by
      rw [ha]
      exact uIcc_subset_Icc hs ht
    let q := fun u => (m.response i).impact (m.prices u i)/m.prices u i
    have hq : ContinuousOn q (uIcc s t) :=
      (((m.response i).continuousOn_positive.comp (m.continuous_prices i)
        (fun u hu => m.positive_prices u hu i)).div (m.continuous_prices i)
        (fun u hu => (m.positive_prices u hu i).ne')).mono hsub
    have hi (e : κ) : IntervalIntegrable (fun u => q u*m.rates u e) volume s t := by
      simpa only [mul_comm] using ((m.rates_integrable e).mono_set (by rw [uIcc_of_le m.time_order.le]; exact hsub)).mul_continuousOn hq
    have hr : IntervalIntegrable (fun u => -m.rho i*(m.prices u i-m.F i)) volume s t :=
      ((continuousOn_const.mul ((m.continuous_prices i).sub continuousOn_const)).mono hsub).intervalIntegrable
    have htrade : IntervalIntegrable (fun u => q u*tradingInput (pairedMatrix edges) (m.rates u) i) volume s t := by
      have hh := IntervalIntegrable.sum Finset.univ (fun e _ => (hi e).const_mul (pairedMatrix edges i e))
      convert hh using 1
      funext u
      simp only [tradingInput,Finset.mul_sum,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [m.physical_primitive i s (by simpa [ha] using hs) t (by simpa [ha] using ht)]
    have he : (fun u => -m.rho i*(m.prices u i-m.F i)+(m.response i).impact (m.prices u i)*
        (tradingInput (pairedMatrix edges) (m.rates u) i/m.prices u i)) =
        fun u => -m.rho i*(m.prices u i-m.F i)+q u*tradingInput (pairedMatrix edges) (m.rates u) i := by
      funext u
      dsimp [q]
      ring
    rw [he, intervalIntegral.integral_add hr htrade,
      paired_rate_stieltjes_sum edges m.rates G B hG m.b hd q s t hs ht hi i]
  physical_share_primitive := by
    intro i s hs t ht
    have hT : 0 ≤ m.b := by simpa [ha] using m.time_order.le
    have hiq (e : κ) : IntervalIntegrable (fun u => (1/m.prices u i)*m.rates u e) volume 0 m.b := by
      have hc : ContinuousOn (fun u => 1/m.prices u i) (uIcc m.a m.b) := by
        rw [uIcc_of_le m.time_order.le]
        exact continuousOn_const.div (m.continuous_prices i) (fun u hu => (m.positive_prices u hu i).ne')
      simpa only [ha,mul_comm] using (m.rates_integrable e).mul_continuousOn hc
    have hi : ∀ j, IntervalIntegrable (fun u => tradingInput (pairedMatrix edges) (m.rates u) j/m.prices u j) volume 0 m.b := by
      intro j
      have hc : ContinuousOn (fun u => 1/m.prices u j) (uIcc m.a m.b) := by
        rw [uIcc_of_le m.time_order.le]
        exact continuousOn_const.div (m.continuous_prices j) (fun u hu => (m.positive_prices u hu j).ne')
      have hh := IntervalIntegrable.sum Finset.univ (fun e _ =>
        (((m.rates_integrable e).mul_continuousOn hc).const_mul (pairedMatrix edges j e)))
      simp only [ha] at hh
      convert hh using 1
      funext u
      simp only [tradingInput,Finset.sum_div,Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro e _
      ring
    rw [rateShares_difference edges m.prices m.rates H m.b hT hi i s t hs ht]
    convert paired_rate_stieltjes_sum edges m.rates G B hG m.b hd (fun u => 1/m.prices u i) s t hs ht
      (fun e => (hiq e).mono_set (by rw [uIcc_of_le hT]; exact uIcc_subset_Icc hs ht)) i using 1
    congr 1
    funext u
    ring
  marginal_dollar_primitive := by
    intro i s hs t ht
    dsimp [tradingInput]
    rw [add_sub_add_left_eq_sub, ←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring

theorem three_bin_actual_endpoint_quadratic (F ρ Δ : ℝ) (g : Response)
    (hF : 0 < F) (hρ : 0 < ρ) (hΔ : 0 < Δ)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F < g.impact F) :
    ∃ ε B c : ℝ, 0 < ε ∧ 0 < B ∧ 0 < c ∧ ∀ p : ℝ, |p| < ε →
      ∃ (X : ℝ → ℝ) (K : ℝ≥0), X 0 = F ∧ LipschitzOnWith K X (Icc 0 (3*Δ)) ∧
        (∀ t ∈ Ico 0 (3*Δ), HasDerivWithinAt X
          (-ρ*(X t-F)+p*threeBinSignal Δ (Real.exp (-ρ*Δ)) t*(g.impact (X t)/X t)) (Ici t) t) ∧
        (∀ t ∈ Icc 0 (3*Δ), 0 < X t ∧ |X t-F| ≤ B*|p|) ∧
        X (3*Δ) ≤ F-c*p^2 := by
  obtain ⟨m⟩ := exists_local_response_model F g hF hg
  obtain ⟨ε,A,B,hε,hA,hB,hsol⟩ := three_bin_nonlinear_approximation F ρ Δ g hρ hΔ m
  let z := threeBinSecondResponse Δ ρ (g.impact F/F) ((F*deriv g.impact F-g.impact F)/F^2) (3*Δ)
  have hz : z < 0 := threeBinSecondResponse_terminal_negative Δ ρ _ _ hΔ hρ
    (div_pos (g.positive F hF) hF) (div_neg_of_neg_of_pos (sub_neg.mpr he) (sq_pos_of_pos hF))
  refine ⟨min ε (-z/(2*A)),B,-z/2,lt_min hε (div_pos (neg_pos.mpr hz) (by positivity)),hB,by linarith,?_⟩
  intro p hp
  obtain ⟨X,K,hX0,hXL,hXd,hXb,hXE⟩ := hsol p (lt_of_lt_of_le hp (min_le_left _ _))
  refine ⟨X,K,hX0,hXL,hXd,hXb,?_⟩
  have ht : 3*Δ ∈ Icc (0:ℝ) (3*Δ) := ⟨by positivity,le_rfl⟩
  have hE := hXE (3*Δ) ht
  rw [(threeBinLinearResponse_endpoints Δ ρ (g.impact F/F) hΔ hρ.ne').2] at hE
  change |X (3*Δ)-(F+p*0+p^2*z)| ≤ A*|p|^3 at hE
  have hpA : A*|p| < -z/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*A by positivity)).mp
      (lt_of_lt_of_le hp (min_le_right _ _))
    linarith
  have hsquare : |p|^2 = p^2 := sq_abs p
  have hrem : A*|p|^3 ≤ (-z/2)*p^2 := by
    calc
      A*|p|^3 = (A*|p|)*p^2 := by rw [←hsquare];ring
      _ ≤ (-z/2)*p^2 := mul_le_mul_of_nonneg_right hpA.le (sq_nonneg p)
  have hh := le_trans (le_abs_self (X (3*Δ)-(F+p*0+p^2*z))) hE
  nlinarith

/-- Construction of an integral-form physical AC session from actual right
ODEs and bounded nonnegative paired rates. No FTC premise is supplied. -/
def rightODERateSession {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (F ρ : ι → ℝ) (g : ι → Response)
    (hF : ∀ i, 0 < F i) (hρ : ∀ i, 0 ≤ ρ i) (T : ℝ) (hT : 0 < T)
    (S : ℝ → ι → ℝ) (K : ι → ℝ≥0)
    (hSL : ∀ i, LipschitzOnWith (K i) (fun t => S t i) (Icc 0 T))
    (hSP : ∀ t ∈ Icc 0 T, ∀ i, 0 < S t i)
    (rate : ℝ → κ → ℝ) (B : κ → ℝ) (hB : ∀ e, 0 ≤ B e)
    (hm : ∀ e, Measurable (fun t => rate t e))
    (hr : ∀ e t, 0 ≤ rate t e ∧ rate t e ≤ B e)
    (G : κ → StieltjesFunction) (hGL : ∀ e, LipschitzWith ⟨B e,hB e⟩ (G e))
    (hGP : ∀ e t, G e t = ∫ u in (0:ℝ)..t, rate u e)
    (hRC : ∀ e t, ContinuousWithinAt (fun u => rate u e) (Ici t) t)
    (hODE : ∀ i t, t ∈ Ico 0 T → HasDerivWithinAt (fun u => S u i)
      (-ρ i*(S t i-F i)+(g i).impact (S t i)*
        (tradingInput (pairedMatrix edges) (rate t) i/S t i)) (Ici t) t) :
    ACPhysicalSession edges where
  a := 0
  b := T
  time_order := hT
  F := F
  rho := ρ
  response := g
  benchmark_positive := hF
  resilience_nonnegative := hρ
  prices := S
  rates := rate
  edgeDollars := fun t e => G e t
  continuous_prices := fun i => (hSL i).continuousOn
  positive_prices := hSP
  rates_integrable := fun e => bounded_measurable_intervalIntegrable (fun t => rate t e) (B e) (hm e)
    (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (hr e t).1];exact (hr e t).2) 0 T
  nonnegative_rates := Filter.Eventually.of_forall (fun t _ e => (hr e t).1)
  edge_primitive := by
    intro e t ht
    simp [hGP e t,hGP e 0]
  edge_derivative := by
    have hd (e : κ) := rate_stieltjes_derivative_ae (fun t => rate t e) (G e) (B e) T
      (hB e) (hGL e) (hGP e) (hm e)
      (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (hr e t).1];exact (hr e t).2) (hRC e)
    have hh : ∀ᵐ t ∂volume, ∀ e, t ∈ Icc 0 T → HasDerivAt (G e) (rate t e) t :=
      (ae_all_iff.mpr hd)
    filter_upwards [hh] with t ht hmem e
    exact ht e hmem
  physical_primitive := fun i => (lipschitz_right_ode_primitive _ _ 0 T hT.le (K i) (hSL i)
    (fun t ht => hODE i t ht)).2
  physical_derivative := by
    have hd (i : ι) := lipschitz_right_derivative_ae _ _ 0 T (K i) (hSL i)
      (fun t ht => hODE i t ht)
    have hh : ∀ᵐ t ∂volume, ∀ i, t ∈ Icc 0 T → HasDerivAt (fun u => S u i)
        (-ρ i*(S t i-F i)+(g i).impact (S t i)*
          (tradingInput (pairedMatrix edges) (rate t) i/S t i)) t := ae_all_iff.mpr hd
    filter_upwards [hh] with t ht hmem i
    exact ht i hmem

theorem ACPhysicalSession.signed_share_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (i : ι) :
    IntervalIntegrable (fun u => tradingInput (pairedMatrix edges) (m.rates u) i/m.prices u i)
      volume m.a m.b := by
  have hc : ContinuousOn (fun u => 1/m.prices u i) (uIcc m.a m.b) := by
    rw [uIcc_of_le m.time_order.le]
    exact continuousOn_const.div (m.continuous_prices i) (fun u hu => (m.positive_prices u hu i).ne')
  have hh := IntervalIntegrable.sum Finset.univ (fun e _ =>
    (((m.rates_integrable e).mul_continuousOn hc).const_mul (pairedMatrix edges i e)))
  convert hh using 1
  funext u
  simp only [tradingInput,Finset.sum_div,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem ACPhysicalSession.signed_share_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → ∀ i,
      |tradingInput (pairedMatrix edges) (m.rates t) i/m.prices t i| ≤ v := by
  filter_upwards [m.local_capacity,hv.2] with t hcap hb ht i
  have hp := m.positive_prices t ht i
  rw [abs_div,abs_of_pos hp,div_le_iff₀ hp]
  exact (hcap ht i).2.trans (by nlinarith [hb ht i])

theorem acSession_original_piece_of_rateBounded {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (ha : m.a = 0)
    (G : κ → StieltjesFunction) (B : κ → ℝ≥0) (hG : ∀ e, LipschitzWith (B e) (G e))
    (hd : ∀ e, ∀ᵐ t ∂volume, t ∈ Icc 0 m.b → HasDerivAt (G e) (m.rates t e) t)
    (H L : ι → ℝ) (v : ℝ) (hv : m.RateBounded v) (hH : ∀ i, v*m.b ≤ H i) :
    ∃ p : PhysicalContinuousBVPiece edges,
      p.a = 0 ∧ p.b = m.b ∧ p.F = m.F ∧ p.rho = m.rho ∧ p.response = m.response ∧
      p.prices = m.prices ∧ p.shares = rateShares edges m.prices m.rates H ∧
      p.shares 0 = H ∧ p.dollarLedger 0 = L ∧
      (∀ i, LipschitzOnWith ⟨v,hv.1⟩ (fun t => p.shares t i) (Icc 0 m.b)) := by
  have hT : 0 ≤ m.b := by simpa [ha] using m.time_order.le
  have hi (i : ι) := m.signed_share_integrable i
  simp only [ha] at hi
  have hb := m.signed_share_bound v hv
  simp only [ha] at hb
  obtain ⟨hL,hshort⟩ := rateShares_lipschitz_and_nonnegative edges m.prices m.rates H m.b v hT hv.1 hi hb hH
  let p := acSessionOriginalPiece m ha G B hG hd H L hshort
  refine ⟨p,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rateShares_initial _ _ _ _,?_,hL⟩
  funext i
  simp [p,acSessionOriginalPiece,tradingInput]

def fullGraphVectorDollars {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) : CompleteEdgeIndex ι → ℝ :=
  embedPairedDollars (starEdges hub) (starDollars u hub)

theorem fullGraphVectorDollars_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (e : CompleteEdgeIndex ι) : 0 ≤ fullGraphVectorDollars hub u e :=
  embedPairedDollars_nonnegative _ _ (starDollars_nonnegative u hub) e

theorem fullGraphVectorDollars_input {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (hu : ∑ i, u i = 0) (i : ι) :
    tradingInput (pairedMatrix completePairedEdges) (fullGraphVectorDollars hub u) i = u i := by
  rw [fullGraphVectorDollars,embedPairedDollars_input,star_input u hub hu]

def threeBinPairedRates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (Δ r a t : ℝ) (e : CompleteEdgeIndex ι) : ℝ :=
  a*threeStageFunction Δ (fullGraphVectorDollars hub u e)
    (fullGraphVectorDollars hub (fun i => -(1+r)*u i) e)
    (fullGraphVectorDollars hub (fun i => r*u i) e) t

theorem threeBinPairedRates_input {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (hu : ∑ i, u i = 0) (Δ r a t : ℝ) (i : ι) :
    tradingInput (pairedMatrix completePairedEdges) (threeBinPairedRates hub u Δ r a t) i =
      a*u i*threeBinSignal Δ r t := by
  have hz (c : ℝ) : ∑ i, c*u i = 0 := by rw [←Finset.mul_sum,hu,mul_zero]
  have hsc (v : ι → ℝ) (hv : ∑ j, v j = 0) :
      tradingInput (pairedMatrix completePairedEdges) (fun e => a*fullGraphVectorDollars hub v e) i = a*v i := by
    calc
      _ = a*tradingInput (pairedMatrix completePairedEdges) (fullGraphVectorDollars hub v) i := by
        simp only [tradingInput,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = _ := by rw [fullGraphVectorDollars_input hub v hv]
  change tradingInput (pairedMatrix completePairedEdges) (fun e => a*(if t < Δ then fullGraphVectorDollars hub u e else if t < 2*Δ then fullGraphVectorDollars hub (fun j => -(1+r)*u j) e else fullGraphVectorDollars hub (fun j => r*u j) e)) i = a*u i*threeBinSignal Δ r t
  by_cases h1 : t < Δ
  · simpa only [threeBinSignal,if_pos h1,mul_one] using hsc u hu
  · by_cases h2 : t < 2*Δ
    · have hh := hsc (fun j => -(1+r)*u j) (hz (-(1+r)))
      simp only [threeBinSignal,if_neg h1,if_pos h2]
      rw [hh]
      ring
    · have hh := hsc (fun j => r*u j) (hz r)
      simp only [threeBinSignal,if_neg h1,if_neg h2]
      rw [hh]
      ring

def threeBinEdgeBound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (r : ℝ) (e : CompleteEdgeIndex ι) : ℝ :=
  fullGraphVectorDollars hub u e+fullGraphVectorDollars hub (fun i => -(1+r)*u i) e+
    fullGraphVectorDollars hub (fun i => r*u i) e

theorem threeBinEdgeBound_nonnegative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (r : ℝ) (e : CompleteEdgeIndex ι) : 0 ≤ threeBinEdgeBound hub u r e := by
  exact add_nonneg (add_nonneg (fullGraphVectorDollars_nonnegative _ _ _)
    (fullGraphVectorDollars_nonnegative _ _ _)) (fullGraphVectorDollars_nonnegative _ _ _)

theorem threeBinPairedRates_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (Δ r a t : ℝ) (ha : 0 ≤ a) (e : CompleteEdgeIndex ι) :
    0 ≤ threeBinPairedRates hub u Δ r a t e ∧
      threeBinPairedRates hub u Δ r a t e ≤ a*threeBinEdgeBound hub u r e := by
  exact ⟨mul_nonneg ha (threeStageFunction_nonnegative _ _ _ _
    (fullGraphVectorDollars_nonnegative _ _ _) (fullGraphVectorDollars_nonnegative _ _ _)
    (fullGraphVectorDollars_nonnegative _ _ _) t),
    mul_le_mul_of_nonneg_left (threeStageFunction_bound _ _ _ _
      (fullGraphVectorDollars_nonnegative _ _ _) (fullGraphVectorDollars_nonnegative _ _ _)
      (fullGraphVectorDollars_nonnegative _ _ _) t) ha⟩

theorem threeBinPairedRates_measurable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (Δ r a : ℝ) (e : CompleteEdgeIndex ι) :
    Measurable (fun t => threeBinPairedRates hub u Δ r a t e) :=
  measurable_const.mul (threeStageFunction_measurable _ _ _ _)

theorem threeBinPairedRates_right_continuous {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (Δ r a t : ℝ) (e : CompleteEdgeIndex ι) :
    ContinuousWithinAt (fun s => threeBinPairedRates hub u Δ r a s e) (Ici t) t :=
  continuousWithinAt_const.mul (threeStageFunction_continuousWithinAt_right _ _ _ _ _)

theorem threeBinPairedRates_ledger_closure {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (hu : ∑ i, u i = 0) (Δ r a : ℝ) (hΔ : 0 < Δ) (i : ι) :
    (∫ t in (0:ℝ)..(3*Δ), tradingInput (pairedMatrix completePairedEdges)
      (threeBinPairedRates hub u Δ r a t) i) = 0 := by
  simp_rw [threeBinPairedRates_input hub u hu Δ r a]
  rw [intervalIntegral.integral_const_mul,(threeBinSignal_integral Δ r hΔ).2,mul_zero]

def threeBinGrossConstant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (r : ℝ) : ℝ :=
  1+∑ i, ∑ e, |pairedMatrix (completePairedEdges (ι := ι)) i e| *threeBinEdgeBound hub u r e

theorem threeBinGrossConstant_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (r : ℝ) : 0 < threeBinGrossConstant hub u r := by
  have hh : 0 ≤ ∑ i, ∑ e, |pairedMatrix (completePairedEdges (ι := ι)) i e| *threeBinEdgeBound hub u r e :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun e _ =>
      mul_nonneg (abs_nonneg _) (threeBinEdgeBound_nonnegative hub u r e)))
  dsimp [threeBinGrossConstant]
  linarith

theorem threeBinPairedRates_gross_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (Δ r a F : ℝ) (ha : 0 ≤ a) (hF : 0 < F)
    (S : ℝ → ι → ℝ) (t : ℝ) (i : ι) (hS : F/2 ≤ S t i) :
    (∑ e, |pairedMatrix (completePairedEdges (ι := ι)) i e| *
      threeBinPairedRates hub u Δ r a t e)/S t i ≤
      (2*threeBinGrossConstant hub u r/F)*a := by
  have hci : (∑ e, |pairedMatrix (completePairedEdges (ι := ι)) i e| *threeBinEdgeBound hub u r e) ≤
      threeBinGrossConstant hub u r := by
    have hh := Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j => ∑ e, |pairedMatrix (completePairedEdges (ι := ι)) j e| *threeBinEdgeBound hub u r e)
      (fun j _ => Finset.sum_nonneg (fun e _ =>
        mul_nonneg (abs_nonneg _) (threeBinEdgeBound_nonnegative hub u r e))) (Finset.mem_univ i)
    dsimp [threeBinGrossConstant]
    linarith
  have hn : (∑ e, |pairedMatrix (completePairedEdges (ι := ι)) i e| *
      threeBinPairedRates hub u Δ r a t e) ≤ a*threeBinGrossConstant hub u r := by
    calc
      _ ≤ ∑ e, a*(|pairedMatrix (completePairedEdges (ι := ι)) i e| *threeBinEdgeBound hub u r e) := by
        apply Finset.sum_le_sum
        intro e _
        have hh := mul_le_mul_of_nonneg_left (threeBinPairedRates_bounds hub u Δ r a t ha e).2
          (abs_nonneg (pairedMatrix (completePairedEdges (ι := ι)) i e))
        nlinarith
      _ = a*(∑ e, |pairedMatrix (completePairedEdges (ι := ι)) i e| *threeBinEdgeBound hub u r e) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hci ha
  have hSp : 0 < S t i := lt_of_lt_of_le (half_pos hF) hS
  rw [div_le_iff₀ hSp]
  have hC : 0 ≤ 2*threeBinGrossConstant hub u r/F*a :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (threeBinGrossConstant_positive hub u r).le) hF.le) ha
  have hh := mul_le_mul_of_nonneg_left hS hC
  have he : (2*threeBinGrossConstant hub u r/F*a)*(F/2) = a*threeBinGrossConstant hub u r := by
    field_simp
    <;> ring
  rw [he] at hh
  exact hn.trans hh

theorem three_bin_finite_prices {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F ρ Δ : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 < ρ) (hΔ : 0 < Δ)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F < g.impact F)
    (u : ι → ℝ) (U : ℝ) (hU : 0 < U) (hu : ∀ i, |u i| ≤ U) (huq : ∀ i, 1 ≤ (u i)^2) :
    ∃ ε B c : ℝ, 0 < ε ∧ 0 < B ∧ 0 < c ∧ ∀ a : ℝ, 0 < a → a < ε →
      ∃ (S : ℝ → ι → ℝ) (K : ι → ℝ≥0),
        (∀ i, S 0 i = F) ∧
        (∀ i, LipschitzOnWith (K i) (fun t => S t i) (Icc 0 (3*Δ))) ∧
        (∀ i t, t ∈ Ico 0 (3*Δ) → HasDerivWithinAt (fun s => S s i)
          (-ρ*(S t i-F)+(a*u i)*threeBinSignal Δ (Real.exp (-ρ*Δ)) t*
            (g.impact (S t i)/S t i)) (Ici t) t) ∧
        (∀ t ∈ Icc 0 (3*Δ), ∀ i, 0 < S t i ∧ |S t i-F| ≤ B*a) ∧
        ∀ i, S (3*Δ) i ≤ F-c*a^2 := by
  classical
  obtain ⟨ε,B,c,hε,hB,hc,hsol⟩ := three_bin_actual_endpoint_quadratic F ρ Δ g hF hρ hΔ hg he
  refine ⟨ε/U,B*U,c,div_pos hε hU,mul_pos hB hU,hc,?_⟩
  intro a ha haε
  have hp (i : ι) : |a*u i| < ε := by
    rw [abs_mul,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left (hu i) ha.le).trans_lt ((lt_div_iff₀ hU).mp haε)
  choose S K h0 hL hD hb hend using (fun i => hsol (a*u i) (hp i))
  refine ⟨fun t i => S i t,K,h0,hL,hD,?_,?_⟩
  · intro t ht i
    refine ⟨(hb i t ht).1,?_⟩
    calc
      |S i t-F| ≤ B*|a*u i| := (hb i t ht).2
      _ = B*(a*|u i|) := by rw [abs_mul,abs_of_pos ha]
      _ ≤ B*(a*U) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hu i) ha.le) hB.le
      _ = _ := by ring
  · intro i
    have hh := mul_le_mul_of_nonneg_left (huq i) (mul_nonneg hc.le (sq_nonneg a))
    nlinarith [hend i]

theorem positive_price_logloss_lower (F S d : ℝ) (hF : 0 < F) (hS : 0 < S) (h : S ≤ F-d) :
    d/F ≤ Real.log F-Real.log S := by
  have hh := Real.log_le_sub_one_of_pos (div_pos hS hF)
  rw [Real.log_div hS.ne' hF.ne'] at hh
  have hd : d/F ≤ 1-S/F := by rw [le_sub_iff_add_le,←add_div];exact (div_le_one hF).mpr (by linarith)
  linarith

def originalPathOfContinuousPiece {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (p : PhysicalContinuousBVPiece edges) (ha : p.a = 0)
    (hstart : ∀ i, p.prices 0 i = p.F i)
    (hBV : ∀ i, BoundedVariationOn (fun t => p.shares t i) (Icc p.a p.b))
    (hL0 : ∀ i, p.dollarLedger 0 i = 0) (hLT : ∀ i, p.dollarLedger p.b i = 0) :
    OriginalAdmissiblePhysicalPath p.F p.rho p.response edges where
  benchmark_positive := p.benchmark_positive
  resilience_nonnegative := p.resilience_nonnegative
  initial := ⟨p.a,p.prices p.a,p.shares p.a,p.dollarLedger p.a⟩
  terminal := ⟨p.b,p.prices p.b,p.shares p.b,p.dollarLedger p.b⟩
  trace := .append (.refl _) (.continuous p rfl rfl rfl hBV)
  at_zero := ha
  initial_prices := by simpa [ha] using hstart
  initial_holdings := p.no_short_sales p.a (left_mem_Icc.mpr p.time_order)
  initial_dollars := by simpa [ha] using hL0
  terminal_dollars := hLT

theorem paired_cumulative_ledger_integral {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (rate : ℝ → κ → ℝ) (G : κ → StieltjesFunction)
    (T : ℝ) (hi : ∀ e, IntervalIntegrable (fun t => rate t e) volume 0 T)
    (hP : ∀ e t, G e t = ∫ u in (0:ℝ)..t, rate u e) (i : ι) :
    tradingInput (pairedMatrix edges) (fun e => G e T-G e 0) i =
      ∫ t in (0:ℝ)..T, tradingInput (pairedMatrix edges) (rate t) i := by
  simp only [tradingInput,hP,intervalIntegral.integral_same,sub_zero]
  rw [intervalIntegral.integral_finset_sum (fun e _ => (hi e).const_mul _)]
  simp only [intervalIntegral.integral_const_mul]

/-- The complete original economic trace is exactly the single continuous
piece driven by this AC session's actual dollar measures and densities. -/
def RealizesACSession {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} {F ρ : ι → ℝ} {g : ι → Response}
    (m : ACPhysicalSession edges) (P : OriginalAdmissiblePhysicalPath F ρ g edges) : Prop :=
  ∃ (w : PhysicalContinuousBVPiece edges) (hF : w.F = F) (hρ : w.rho = ρ) (hg : w.response = g)
    (hBV : ∀ i, BoundedVariationOn (fun t => w.shares t i) (Icc w.a w.b)),
    P.initial = ⟨w.a,w.prices w.a,w.shares w.a,w.dollarLedger w.a⟩ ∧
    P.terminal = ⟨w.b,w.prices w.b,w.shares w.b,w.dollarLedger w.b⟩ ∧
    HEq P.trace (OriginalPhysicalReachable.append (.refl _)
      (OriginalPhysicalStep.continuous w hF hρ hg hBV)) ∧
    w.a = m.a ∧ w.b = m.b ∧ w.F = m.F ∧ w.rho = m.rho ∧ w.response = m.response ∧
    w.prices = m.prices ∧
    ∀ e, ∃ B : ℝ≥0, LipschitzWith B (w.execution.cumulative e) ∧
      (∀ s t, (w.execution.cumulative e) t-(w.execution.cumulative e) s =
        m.edgeDollars t e-m.edgeDollars s e) ∧
      ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → HasDerivAt (w.execution.cumulative e) (m.rates t e) t

theorem three_bin_economic_realization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (hu : ∑ i, u i = 0)
    (F ρ Δ a : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 < ρ) (hΔ : 0 < Δ) (ha : 0 < a)
    (S : ℝ → ι → ℝ) (K : ι → ℝ≥0)
    (hSL : ∀ i, LipschitzOnWith (K i) (fun t => S t i) (Icc 0 (3*Δ)))
    (hS : ∀ t ∈ Icc 0 (3*Δ), ∀ i, F/2 ≤ S t i)
    (hODE : ∀ i t, t ∈ Ico 0 (3*Δ) → HasDerivWithinAt (fun s => S s i)
      (-ρ*(S t i-F)+(a*u i)*threeBinSignal Δ (Real.exp (-ρ*Δ)) t*
        (g.impact (S t i)/S t i)) (Ici t) t)
    (H : ι → ℝ)
    (hH : ∀ i, ((2*threeBinGrossConstant hub u (Real.exp (-ρ*Δ))/F)*a)*(3*Δ) ≤ H i) :
    ∃ (m : ACPhysicalSession (completePairedEdges (ι := ι)))
      (p : PhysicalContinuousBVPiece (completePairedEdges (ι := ι))),
      m.a = 0 ∧ m.b = 3*Δ ∧ m.F = (fun _ => F) ∧ m.rho = (fun _ => ρ) ∧ m.response = (fun _ => g) ∧ m.prices = S ∧
      m.RateBounded ((2*threeBinGrossConstant hub u (Real.exp (-ρ*Δ))/F)*a) ∧
      p.a = 0 ∧ p.b = 3*Δ ∧ p.F = (fun _ => F) ∧ p.rho = (fun _ => ρ) ∧
      p.response = (fun _ => g) ∧ p.prices = S ∧ p.shares 0 = H ∧
      p.dollarLedger 0 = 0 ∧ p.dollarLedger (3*Δ) = 0 ∧
      (∀ i, ∃ L : ℝ≥0, LipschitzOnWith L (fun t => p.shares t i) (Icc 0 (3*Δ))) ∧
      ∀ e, ∃ B : ℝ≥0, LipschitzWith B (p.execution.cumulative e) ∧
        (∀ s t, (p.execution.cumulative e) t-(p.execution.cumulative e) s =
          m.edgeDollars t e-m.edgeDollars s e) ∧
        ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → HasDerivAt (p.execution.cumulative e) (m.rates t e) t := by
  classical
  let r := Real.exp (-ρ*Δ)
  let rate := threeBinPairedRates hub u Δ r a
  let EB := fun e => a*threeBinEdgeBound hub u r e
  have hEB (e : CompleteEdgeIndex ι) : 0 ≤ EB e := mul_nonneg ha.le (threeBinEdgeBound_nonnegative hub u r e)
  have hr (e : CompleteEdgeIndex ι) (t : ℝ) : 0 ≤ rate t e ∧ rate t e ≤ EB e :=
    threeBinPairedRates_bounds hub u Δ r a t ha.le e
  have hm (e : CompleteEdgeIndex ι) : Measurable (fun t => rate t e) := threeBinPairedRates_measurable hub u Δ r a e
  have hc (e : CompleteEdgeIndex ι) (t : ℝ) : ContinuousWithinAt (fun s => rate s e) (Ici t) t :=
    threeBinPairedRates_right_continuous hub u Δ r a t e
  choose G hG0 hGP hGL using (fun e => exists_bounded_rate_stieltjes (fun t => rate t e) (EB e)
    (hEB e) (hm e) (fun t => (hr e t).1) (fun t => (hr e t).2))
  have hSP (t : ℝ) (ht : t ∈ Icc 0 (3*Δ)) (i : ι) : 0 < S t i :=
    (half_pos hF).trans_le (hS t ht i)
  have hd (i : ι) (t : ℝ) (ht : t ∈ Ico 0 (3*Δ)) : HasDerivWithinAt (fun s => S s i)
      (-ρ*(S t i-F)+g.impact (S t i)*(tradingInput (pairedMatrix completePairedEdges) (rate t) i/S t i)) (Ici t) t := by
    convert hODE i t ht using 1
    dsimp [rate,r]
    rw [threeBinPairedRates_input hub u hu]
    ring
  let m := rightODERateSession completePairedEdges (fun _ => F) (fun _ => ρ) (fun _ => g)
    (fun _ => hF) (fun _ => hρ.le) (3*Δ) (by positivity) S K hSL hSP rate EB hEB hm hr G hGL hGP hc hd
  let v := (2*threeBinGrossConstant hub u r/F)*a
  have hv0 : 0 ≤ v := mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) (threeBinGrossConstant_positive hub u r).le) hF.le) ha.le
  have hv : m.RateBounded v := by
    refine ⟨hv0,Filter.Eventually.of_forall (fun t ht i => ?_)⟩
    exact threeBinPairedRates_gross_bound hub u Δ r a F ha.le hF S t i (hS t ht i)
  have hdae (e : CompleteEdgeIndex ι) := rate_stieltjes_derivative_ae (fun t => rate t e) (G e) (EB e) (3*Δ)
    (hEB e) (hGL e) (hGP e) (hm e)
    (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (hr e t).1];exact (hr e t).2) (hc e)
  have hi (i : ι) := m.signed_share_integrable i
  have hb := m.signed_share_bound v hv
  obtain ⟨hθL,hshort⟩ := rateShares_lipschitz_and_nonnegative completePairedEdges S rate H (3*Δ) v
    (by positivity) hv0 hi hb hH
  let p := acSessionOriginalPiece m rfl G (fun e => ⟨EB e,hEB e⟩) hGL hdae H 0 hshort
  refine ⟨m,p,rfl,rfl,rfl,rfl,rfl,rfl,hv,rfl,rfl,rfl,rfl,rfl,rfl,rateShares_initial _ _ _ _,?_,?_,?_,?_⟩
  · funext i
    simp [p,acSessionOriginalPiece,tradingInput]
  · funext i
    change 0+tradingInput (pairedMatrix completePairedEdges) (fun e => G e (3*Δ)-G e 0) i = 0
    rw [zero_add,paired_cumulative_ledger_integral completePairedEdges rate G (3*Δ) m.rates_integrable hGP i]
    exact threeBinPairedRates_ledger_closure hub u hu Δ r a hΔ i
  · intro i
    exact ⟨⟨v,hv0⟩,hθL i⟩
  · intro e
    exact ⟨⟨EB e,hEB e⟩,hGL e,fun _ _ => rfl,hdae e⟩

theorem systemicCrisis_lower_of_each_loss {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℝ) (k : ℕ) (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (d : ℝ)
    (hd : ∀ i, d ≤ -q i) : d ≤ systemicCrisis q k := by
  classical
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hm : d ≤ meanLogLoss q := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_neg_distrib] at hh
    exact (le_div_iff₀ hn).mpr (by nlinarith)
  have hq : d ≤ coverageQuantile q k := by
    apply (coverageQuantile_threshold_iff q k hk hkn d).mpr
    have hf : Finset.univ.filter (fun i => d ≤ -q i) = Finset.univ := Finset.filter_eq_self.mpr (fun i _ => hd i)
    simpa only [hf,Finset.card_univ] using hkn
  exact le_min hm hq

theorem positive_price_logloss_upper (F S d : ℝ) (hF : 0 < F) (hS : F/2 ≤ S)
    (hd : 0 ≤ d) (hb : |S-F| ≤ d) : Real.log F-Real.log S ≤ 2*d/F := by
  have hp : 0 < S := (half_pos hF).trans_le hS
  have hh := Real.log_le_sub_one_of_pos (div_pos hF hp)
  rw [Real.log_div hF.ne' hp.ne'] at hh
  apply hh.trans
  rw [div_sub_one hp.ne',div_le_iff₀ hp]
  have hC : 0 ≤ 2*d/F := div_nonneg (mul_nonneg (by norm_num) hd) hF.le
  have hhS := mul_le_mul_of_nonneg_left hS hC
  have he : (2*d/F)*(F/2) = d := by field_simp
  rw [he] at hhS
  exact (by linarith [neg_le_abs (S-F)] : F-S ≤ d).trans hhS

set_option maxHeartbeats 800000 in
theorem three_bin_original_family_of_direction {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (hub : ι) (u : ι → ℝ) (hu : ∑ i, u i = 0)
    (U : ℝ) (hU : 0 < U) (huB : ∀ i, |u i| ≤ U) (huq : ∀ i, 1 ≤ (u i)^2)
    (F ρ Δ v βminus βplus : ℝ) (g : Response)
    (hF : 0 < F) (hρ : 0 < ρ) (hΔ : 0 < Δ) (hv : 0 < v)
    (hβminus : 0 < βminus) (hβplus : 0 < βplus)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F < g.impact F)
    (H : ι → ℝ) (Hmin : ℝ) (hHm : 0 < Hmin) (hH : ∀ i, Hmin ≤ H i) :
    ∃ ε c C D : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ 0 < D ∧ ∀ a : ℝ, 0 < a → a < ε →
      ∃ (m : ACPhysicalSession (completePairedEdges (ι := ι)))
        (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => g) completePairedEdges),
        m.a = 0 ∧ m.b = 3*Δ ∧ m.F = (fun _ => F) ∧ m.rho = (fun _ => ρ) ∧ m.response = (fun _ => g) ∧
        (∀ i, m.prices 0 i = F) ∧ RealizesACSession m P ∧ m.RateBounded (C*a) ∧ m.RateBounded v ∧
        P.initial.shares = H ∧ P.terminal.time = 3*Δ ∧ P.terminal.prices = m.prices (3*Δ) ∧
        (∀ i x, P.trace.Visited i x → F*(1-βminus) < x ∧ x < F*(1+βplus)) ∧
        (∀ i, c*a^2 ≤ Real.log F-Real.log (P.terminal.prices i)) ∧
        (∀ i, Real.log F-Real.log (P.terminal.prices i) ≤ D*a) ∧
        c*a^2 ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) := by
  classical
  letI : Nonempty ι := ⟨hub⟩
  obtain ⟨ε,B,c,hε,hB,hc,hsol⟩ := three_bin_finite_prices F ρ Δ g hF hρ hΔ hg he u U hU huB huq
  let C := 2*threeBinGrossConstant hub u (Real.exp (-ρ*Δ))/F
  have hC : 0 < C := div_pos (mul_pos (by norm_num) (threeBinGrossConstant_positive hub u _)) hF
  let δ := min ε (min (F/(2*B)) (min (F*βminus/B) (min (F*βplus/B) (min (v/C) (Hmin/(C*(3*Δ)))))))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ,c/F,C,2*B/F,hδ,div_pos hc hF,hC,by positivity,?_⟩
  intro a ha haδ
  obtain ⟨haε,hrest⟩ := lt_min_iff.mp haδ
  obtain ⟨haF,hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨haβm,hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨haβp,hrest⟩ := lt_min_iff.mp hrest
  obtain ⟨hav,haH⟩ := lt_min_iff.mp hrest
  obtain ⟨S,K,hS0,hSL,hODE,hSb,hSE⟩ := hsol a ha haε
  have habF : B*a < F/2 := by
    have hh := (lt_div_iff₀ (show 0 < 2*B by positivity)).mp haF
    nlinarith
  have habm : B*a < F*βminus := by nlinarith [(lt_div_iff₀ hB).mp haβm]
  have habp : B*a < F*βplus := by nlinarith [(lt_div_iff₀ hB).mp haβp]
  have hSlo (t : ℝ) (ht : t ∈ Icc 0 (3*Δ)) (i : ι) : F/2 ≤ S t i := by
    have hh := (hSb t ht i).2
    linarith [neg_le_abs (S t i-F)]
  have hstock (i : ι) : (C*a)*(3*Δ) ≤ H i := by
    have hh := (lt_div_iff₀ (show 0 < C*(3*Δ) by positivity)).mp haH
    nlinarith [hH i]
  obtain ⟨m,w,hma,hmb,hmF,hmρ,hmg,hmS,hmcap,hwa,hwb,hwF,hwρ,hwg,hwS,hwH,hwL0,hwLT,hwLip,hwExec⟩ :=
    three_bin_economic_realization hub u hu F ρ Δ a g hF hρ hΔ ha S K hSL hSlo hODE H hstock
  have hBV (i : ι) : BoundedVariationOn (fun t => w.shares t i) (Icc w.a w.b) := by
    obtain ⟨L,hL⟩ := hwLip i
    have hh := hL.locallyBoundedVariationOn 0 (3*Δ) (left_mem_Icc.mpr (by positivity)) (right_mem_Icc.mpr (by positivity))
    simpa only [inter_self,hwa,hwb] using hh
  let P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => g) completePairedEdges := {
    benchmark_positive := fun _ => hF
    resilience_nonnegative := fun _ => hρ.le
    initial := ⟨w.a,w.prices w.a,w.shares w.a,w.dollarLedger w.a⟩
    terminal := ⟨w.b,w.prices w.b,w.shares w.b,w.dollarLedger w.b⟩
    trace := .append (.refl _) (.continuous w hwF hwρ hwg hBV)
    at_zero := hwa
    initial_prices := by simpa only [hwa,hwS] using hS0
    initial_holdings := w.no_short_sales w.a (left_mem_Icc.mpr w.time_order)
    initial_dollars := by rw [hwa,hwL0];intro i;rfl
    terminal_dollars := by rw [hwb,hwLT];intro i;rfl }
  have hend : P.terminal.prices = S (3*Δ) := by change w.prices w.b = S (3*Δ);rw [hwS,hwb]
  have hreal : RealizesACSession m P := by
    refine ⟨w,hwF,hwρ,hwg,hBV,rfl,rfl,HEq.rfl,?_,?_,?_,?_,?_,?_,hwExec⟩
    · rw [hwa,hma]
    · rw [hwb,hmb]
    · rw [hwF,hmF]
    · rw [hwρ,hmρ]
    · rw [hwg,hmg]
    · rw [hwS,hmS]
  have hband (t : ℝ) (ht : t ∈ Icc 0 (3*Δ)) (i : ι) :
      F*(1-βminus) < S t i ∧ S t i < F*(1+βplus) := by
    have hh := (hSb t ht i).2
    constructor <;> nlinarith [le_abs_self (S t i-F),neg_le_abs (S t i-F)]
  have hloss (i : ι) : (c/F)*a^2 ≤ Real.log F-Real.log (P.terminal.prices i) := by
    rw [hend]
    have hh := positive_price_logloss_lower F (S (3*Δ) i) (c*a^2) hF
      (hSb (3*Δ) ⟨by positivity,le_rfl⟩ i).1 (hSE i)
    convert hh using 1 <;> ring
  refine ⟨m,P,hma,hmb,hmF,hmρ,hmg,(by simpa only [hmS] using hS0),hreal,hmcap,?_,?_,?_,?_,?_,hloss,?_,?_⟩
  · refine ⟨hv.le,?_⟩
    filter_upwards [hmcap.2] with t ht hmem i
    exact (ht hmem i).trans ((mul_comm C a) ▸ ((lt_div_iff₀ hC).mp hav).le)
  · change w.shares w.a = H
    rw [hwa,hwH]
  · exact hwb
  · rw [hend,hmS]
  · intro i x hx
    change w.prices w.a i = x ∨ (∃ t ∈ Icc w.a w.b, w.prices t i = x) at hx
    rcases hx with hx | ⟨t,ht,hx⟩
    · rw [hwa,hwS] at hx
      rw [←hx]
      exact hband 0 ⟨le_rfl,by positivity⟩ i
    · rw [hwa,hwb] at ht
      rw [hwS] at hx
      rw [←hx]
      exact hband t ht i
  · intro i
    rw [hend]
    have hh := positive_price_logloss_upper F (S (3*Δ) i) (B*a) hF
      (hSlo (3*Δ) ⟨by positivity,le_rfl⟩ i) (mul_nonneg hB.le ha.le)
      (hSb (3*Δ) ⟨by positivity,le_rfl⟩ i).2
    convert hh using 1 <;> ring
  · apply systemicCrisis_lower_of_each_loss _ _ Fintype.card_pos le_rfl
    intro i
    dsimp [logPriceFromBenchmark]
    have hp : 0 < P.terminal.prices i := by rw [hend];exact (hSb (3*Δ) ⟨by positivity,le_rfl⟩ i).1
    rw [Real.log_div hp.ne' hF.ne']
    linarith [hloss i]

theorem theorem_6_3_original_family {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (F ρ T v βminus βplus : ℝ) (g : Response)
    (hF : 0 < F) (hρ : 0 < ρ) (hT : 0 < T) (hv : 0 < v)
    (hβminus : 0 < βminus) (hβplus : 0 < βplus)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F/g.impact F < 1)
    (H : ι → ℝ) (hH : ∀ i, 0 < H i) :
    ∃ ε c C D : ℝ, 0 < ε ∧ 0 < c ∧ 0 < C ∧ 0 < D ∧ ∀ a : ℝ, 0 < a → a < ε →
      ∃ (m : ACPhysicalSession (completePairedEdges (ι := ι)))
        (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => g) completePairedEdges),
        m.a = 0 ∧ m.b = T ∧ m.F = (fun _ => F) ∧ m.rho = (fun _ => ρ) ∧ m.response = (fun _ => g) ∧
        (∀ i, m.prices 0 i = F) ∧ RealizesACSession m P ∧ m.RateBounded (C*a) ∧ m.RateBounded v ∧
        P.initial.shares = H ∧ P.terminal.time = T ∧ P.terminal.prices = m.prices T ∧
        (∀ i x, P.trace.Visited i x → F*(1-βminus) < x ∧ x < F*(1+βplus)) ∧
        (∀ i, c*a^2 ≤ Real.log F-Real.log (P.terminal.prices i)) ∧
        (∀ i, Real.log F-Real.log (P.terminal.prices i) ≤ D*a) ∧
        c*a^2 ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) := by
  classical
  let hub : ι := Classical.arbitrary ι
  let u := partialCoveragePulseVector hub
  have hn : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  have huB (i : ι) : |u i| ≤ (Fintype.card ι : ℝ) := by
    by_cases hi : i = hub
    · simp only [u,partialCoveragePulseVector,if_pos hi]
      rw [abs_of_nonpos (by linarith : 1-(Fintype.card ι : ℝ) ≤ 0)]
      linarith
    · simp only [u,partialCoveragePulseVector,if_neg hi,sub_zero,abs_one]
      linarith
  have huq (i : ι) : 1 ≤ (u i)^2 := by
    by_cases hi : i = hub
    · simp only [u,partialCoveragePulseVector,if_pos hi]
      nlinarith
    · simp [u,partialCoveragePulseVector,hi]
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (Finset.univ : Finset ι) H Finset.univ_nonempty
  have hh := three_bin_original_family_of_direction hub u
    (partialCoveragePulseVector_zero_sum hub) (Fintype.card ι : ℝ) (by linarith) huB huq
    F ρ (T/3) v βminus βplus g hF hρ (by positivity) hv hβminus hβplus hg
    ((div_lt_one (g.positive F hF)).mp he) H (H j) (hH j) (fun i => hmin i (Finset.mem_univ i))
  simpa only [show 3*(T/3) = T by ring] using hh

theorem systemicCrisis_upper_of_each_loss {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℝ) (k : ℕ) (d : ℝ) (hd : ∀ i, -q i ≤ d) : systemicCrisis q k ≤ d := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  apply (systemicCrisis_le_meanLogLoss q k).trans
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Finset.sum_neg_distrib] at hh
  exact (div_le_iff₀ hn).mpr (by nlinarith)

theorem theorem_6_3_original {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (F ρ T v βminus βplus : ℝ) (g : Response)
    (hF : 0 < F) (hρ : 0 < ρ) (hT : 0 < T) (hv : 0 < v)
    (hβminus : 0 < βminus) (hβplus : 0 < βplus)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F/g.impact F < 1)
    (H : ι → ℝ) (hH : ∀ i, 0 < H i) (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ (m : ACPhysicalSession (completePairedEdges (ι := ι)))
      (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => g) completePairedEdges),
      m.a = 0 ∧ m.b = T ∧ m.F = (fun _ => F) ∧ m.rho = (fun _ => ρ) ∧ m.response = (fun _ => g) ∧
      (∀ i, m.prices 0 i = F) ∧ RealizesACSession m P ∧ m.RateBounded v ∧ P.initial.shares = H ∧ P.terminal.time = T ∧ P.terminal.prices = m.prices T ∧
      (∀ i x, P.trace.Visited i x → F*(1-βminus) < x ∧ x < F*(1+βplus)) ∧
      (∀ i, P.terminal.prices i < F) ∧
      0 < systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) ∧
      systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) < ζ := by
  obtain ⟨ε,c,C,D,hε,hc,hC,hD,hfamily⟩ :=
    theorem_6_3_original_family hN F ρ T v βminus βplus g hF hρ hT hv hβminus hβplus hg he H hH
  let a := min ε (ζ/D)/2
  have ha : 0 < a := half_pos (lt_min hε (div_pos hζ hD))
  have haε : a < ε := (half_lt_self (lt_min hε (div_pos hζ hD))).trans_le (min_le_left _ _)
  have haζ : D*a < ζ := by
    have hh : a < ζ/D := (half_lt_self (lt_min hε (div_pos hζ hD))).trans_le (min_le_right _ _)
    nlinarith [(lt_div_iff₀ hD).mp hh]
  obtain ⟨m,P,hma,hmb,hmF,hmρ,hmg,hm0,hreal,hmCa,hmv,hH0,hPT,hPS,hband,hloss,hupp,hcrisis⟩ := hfamily a ha haε
  have hlp (i : ι) : 0 < Real.log F-Real.log (P.terminal.prices i) :=
    (mul_pos hc (sq_pos_of_pos ha)).trans_le (hloss i)
  have hp (i : ι) : 0 < P.terminal.prices i := P.trace.endpoint_positive
    (fun j => by rw [P.initial_prices j];exact hF) i
  refine ⟨m,P,hma,hmb,hmF,hmρ,hmg,hm0,hreal,hmv,hH0,hPT,hPS,hband,?_,
    (mul_pos hc (sq_pos_of_pos ha)).trans_le hcrisis,?_⟩
  · intro i
    exact (Real.log_lt_log_iff (hp i) hF).mp (sub_pos.mp (hlp i))
  · have hh : systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) ≤ D*a := by
      apply systemicCrisis_upper_of_each_loss
      intro i
      dsimp [logPriceFromBenchmark]
      rw [Real.log_div (hp i).ne' hF.ne']
      linarith [hupp i]
    exact hh.trans_lt haζ

end MarketCrash
