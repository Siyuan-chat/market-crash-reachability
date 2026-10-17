import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Topology
namespace MarketCrash

theorem stieltjes_integral_one_increment (G : StieltjesFunction) (a b : ℝ) :
    (∫ _x in a..b, (1 : ℝ) ∂G.measure) = G b - G a := by
  rw [intervalIntegral.integral_const']
  simp only [measureReal_def, G.measure_Ioc, smul_eq_mul, mul_one]
  rcases le_total a b with hab | hba
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (G.mono hab)),
      ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (G.mono hab))]
    simp
  · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (G.mono hba)),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (G.mono hba))]
    simp

/-- A continuous integrand's Stieltjes primitive differentiates wherever
the actual monotone integrator differentiates, without assuming its FTC. -/
theorem stieltjes_primitive_hasDerivAt_local (G : StieltjesFunction) (w : ℝ → ℝ)
    (a t r : ℝ) (hint : IntervalIntegrable w G.measure a t)
    (hmeas : StronglyMeasurableAtFilter w (nhds t) G.measure)
    (hw : ContinuousAt w t) (hG : HasDerivAt G r t) :
    HasDerivAt (fun x => ∫ u in a..x, w u ∂G.measure) (w t * r) t := by
  have hlim : Tendsto w (nhds t ⊓ ae G.measure) (nhds (w t)) :=
    hw.mono_left inf_le_left
  have hsmall := intervalIntegral.measure_integral_sub_integral_sub_linear_isLittleO_of_tendsto_ae_right
    hint hmeas hlim (tendsto_const_nhds : Tendsto (fun _ : ℝ => t) (nhds t) (nhds t))
    (tendsto_id : Tendsto (fun x : ℝ => x) (nhds t) (nhds t))
  have hc (x : ℝ) : (∫ _u in t..x, w t ∂G.measure) = w t * (G x - G t) := by
    have he : (fun _u : ℝ => w t) = fun _u : ℝ => w t * (1 : ℝ) := by funext; ring
    rw [he, intervalIntegral.integral_const_mul, stieltjes_integral_one_increment]
  simp only [hc, stieltjes_integral_one_increment] at hsmall
  have herr := hsmall.trans_isBigO hG.isBigO_sub
  have hlin := (hasDerivAt_iff_isLittleO.mp (hG.const_mul (w t)))
  apply hasDerivAt_iff_isLittleO.mpr
  convert herr.add hlin using 1 <;> funext x <;> simp only [smul_eq_mul, id_eq] <;> ring

theorem stieltjes_primitive_hasDerivAt (G : StieltjesFunction) (w : ℝ → ℝ)
    (hw : Continuous w) (a t r : ℝ) (hG : HasDerivAt G r t) :
    HasDerivAt (fun x => ∫ u in a..x, w u ∂G.measure) (w t * r) t := by
  exact stieltjes_primitive_hasDerivAt_local G w a t r (hw.intervalIntegrable a t)
    hw.stronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt hG

theorem stieltjes_primitive_hasDerivAt_on_interval (G : StieltjesFunction) (w : ℝ → ℝ)
    (a b t r : ℝ) (hw : ContinuousOn w (Icc a b)) (ht : t ∈ Ioo a b)
    (hG : HasDerivAt G r t) :
    HasDerivAt (fun x => ∫ u in a..x, w u ∂G.measure) (w t * r) t := by
  have hi : IntervalIntegrable w G.measure a t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1.le
      (hw.mono (fun _ hx => ⟨hx.1, hx.2.trans ht.2.le⟩))
  have hm : StronglyMeasurableAtFilter w (nhds t) G.measure :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hw.mono Ioo_subset_Icc_self) t ht
  exact stieltjes_primitive_hasDerivAt_local G w a t r hi hm
    (hw.continuousAt (Icc_mem_nhds ht.1 ht.2)) hG

end MarketCrash
