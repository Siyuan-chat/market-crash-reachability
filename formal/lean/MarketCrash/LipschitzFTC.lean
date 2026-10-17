import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
namespace MarketCrash

theorem lipschitzFTC_stieltjes_ac_of_complement (G H : StieltjesFunction) (c : ℝ≥0)
    (hsum : ∀ x, G x + H x = c * x) : G.measure ≪ volume := by
  have heq : G.measure + H.measure = (c : ℝ≥0∞) • volume := by
    rw [← StieltjesFunction.measure_add]
    apply Measure.ext_of_Ioc
    intro a b hab
    rw [StieltjesFunction.measure_Ioc, Measure.smul_apply, Real.volume_Ioc]
    simp only [StieltjesFunction.add_apply, smul_eq_mul]
    rw [show G b + H b - (G a + H a) = (c : ℝ) * (b - a) by rw [hsum, hsum]; ring]
    rw [ENNReal.ofReal_mul c.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  apply Measure.absolutelyContinuous_of_le_smul (c := (c : ℝ≥0∞))
  rw [← heq]
  intro s
  exact le_self_add

theorem lipschitzFTC_stieltjes_integral (G : StieltjesFunction) (hG : G.measure ≪ volume)
    (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (deriv G) volume a b ∧
      (∫ x in a..b, deriv G x) = G b - G a := by
  let r := fun x => (G.measure.rnDeriv volume x).toReal
  have he : deriv G =ᵐ[volume] r := by
    filter_upwards [G.ae_hasDerivAt] with x hx using hx.deriv
  have hl : ∫⁻ x in Ioc a b, G.measure.rnDeriv volume x = G.measure (Ioc a b) := by
    simpa using setLIntegral_rnDeriv_mul hG
      (f := fun _ => (1 : ℝ≥0∞)) measurable_const.aemeasurable measurableSet_Ioc
  have hi : IntegrableOn r (Ioc a b) volume :=
    integrable_toReal_of_lintegral_ne_top
      ((Measure.measurable_rnDeriv G.measure volume).aemeasurable.restrict)
      (by rw [hl, G.measure_Ioc]; exact ENNReal.ofReal_ne_top)
  have hd : IntervalIntegrable (deriv G) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    exact hi.congr (ae_restrict_of_ae he.symm)
  refine ⟨hd, ?_⟩
  rw [intervalIntegral.integral_of_le hab]
  calc
    ∫ x in Ioc a b, deriv G x = ∫ x in Ioc a b, r x := integral_congr_ae (ae_restrict_of_ae he)
    _ = (G.measure (Ioc a b)).toReal := by
      simpa [r, measureReal_def] using
        (setIntegral_rnDeriv_smul hG (f := fun _ => (1 : ℝ)) measurableSet_Ioc)
    _ = G b - G a := by rw [G.measure_Ioc, ENNReal.toReal_ofReal (sub_nonneg.mpr (G.mono hab))]

theorem lipschitz_integral_deriv_eq_sub {C : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzWith C f) (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (deriv f) volume a b ∧
      (∫ x in a..b, deriv f x) = f b - f a := by
  let G : StieltjesFunction := {
    toFun := fun x => f x + C * x
    mono' := by
      intro x y hxy
      have h := hf.dist_le_mul x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
      have := (abs_le.mp h).2
      dsimp
      nlinarith
    right_continuous' := fun x => (hf.continuous.add (continuous_const.mul continuous_id)).continuousAt.continuousWithinAt }
  let H : StieltjesFunction := {
    toFun := fun x => C * x - f x
    mono' := by
      intro x y hxy
      have h := hf.dist_le_mul x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)] at h
      have := (abs_le.mp h).1
      dsimp
      nlinarith
    right_continuous' := fun x => ((continuous_const.mul continuous_id).sub hf.continuous).continuousAt.continuousWithinAt }
  have hac := lipschitzFTC_stieltjes_ac_of_complement G H (2 * C) (by intro x; dsimp [G, H]; ring)
  obtain ⟨hGi, hG⟩ := lipschitzFTC_stieltjes_integral G hac a b hab
  have he : deriv f =ᵐ[volume] fun x => deriv G x - C := by
    filter_upwards [hf.ae_differentiableAt_real] with x hx
    have h := hx.hasDerivAt.add ((hasDerivAt_id x).const_mul (C : ℝ))
    have hd : deriv G x = deriv f x + C := by simpa [G] using h.deriv
    linarith
  have hCi : IntervalIntegrable (fun _ : ℝ => (C : ℝ)) volume a b := intervalIntegrable_const
  have hi : IntervalIntegrable (deriv f) volume a b := by
    rw [intervalIntegrable_iff, uIoc_of_le hab]
    have ht := hGi.sub hCi
    rw [intervalIntegrable_iff, uIoc_of_le hab] at ht
    exact ht.congr (ae_restrict_of_ae he.symm)
  refine ⟨hi, ?_⟩
  have he' : ∀ᵐ x ∂volume, x ∈ uIoc a b → deriv f x = deriv G x - C :=
    he.mono (fun _ hx _ => hx)
  rw [intervalIntegral.integral_congr_ae he', intervalIntegral.integral_sub hGi hCi, hG,
    intervalIntegral.integral_const]
  dsimp [G]
  ring

theorem lipschitzOn_integral_eq_sub_of_hasDerivAt_ae {C : ℝ≥0} {f w : ℝ → ℝ}
    {a b : ℝ} (hf : LipschitzOnWith C f (Icc a b)) (hab : a ≤ b)
    (hw : ∀ᵐ x ∂volume, x ∈ Ioo a b → HasDerivAt f (w x) x) :
    IntervalIntegrable w volume a b ∧ (∫ x in a..b, w x) = f b - f a := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  obtain ⟨hgi, hge⟩ := lipschitz_integral_deriv_eq_sub hg a b hab
  have hae : ∀ᵐ x ∂volume, x ∈ uIoc a b → w x = deriv g x := by
    filter_upwards [hw, show ∀ᵐ x : ℝ ∂volume, x ≠ b by simp [ae_iff]] with x hx hxb hmem
    rw [uIoc_of_le hab] at hmem
    have hxi : x ∈ Ioo a b := ⟨hmem.1, lt_of_le_of_ne hmem.2 hxb⟩
    have hevent : g =ᶠ[nhds x] f := by
      filter_upwards [Ioo_mem_nhds hxi.1 hxi.2] with y hy
      exact (heq ⟨hy.1.le, hy.2.le⟩).symm
    exact ((hx hxi).congr_of_eventuallyEq hevent).deriv.symm
  have hi : IntervalIntegrable w volume a b := by
    constructor
    · exact hgi.1.congr (by
        filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Ioc] with x hx hmem
        exact (hx (by simpa [uIoc_of_le hab] using hmem)).symm)
    · simpa [Ioc_eq_empty_of_le hab] using hgi.2
  refine ⟨hi, ?_⟩
  rw [intervalIntegral.integral_congr_ae hae, hge, ← heq ⟨hab, le_rfl⟩, ← heq ⟨le_rfl, hab⟩]

theorem lipschitzOn_integral_deriv_eq_sub {C : ℝ≥0} {f : ℝ → ℝ}
    {a b : ℝ} (hf : LipschitzOnWith C f (Icc a b)) (hab : a ≤ b) :
    IntervalIntegrable (deriv f) volume a b ∧ (∫ x in a..b, deriv f x) = f b - f a := by
  obtain ⟨g, hg, heq⟩ := hf.extend_real
  apply lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hf hab
  filter_upwards [hg.ae_differentiableAt_real] with x hx hmem
  have hevent : f =ᶠ[nhds x] g := by
    filter_upwards [Ioo_mem_nhds hmem.1 hmem.2] with y hy
    exact heq ⟨hy.1.le, hy.2.le⟩
  exact (hx.hasDerivAt.congr_of_eventuallyEq hevent).differentiableAt.hasDerivAt

end MarketCrash
