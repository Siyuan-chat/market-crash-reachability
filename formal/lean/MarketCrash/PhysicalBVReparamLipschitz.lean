import MarketCrash.PhysicalContinuousBV
import MarketCrash.ContinuousClock

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace MarketCrash

theorem stieltjes_interval_norm_bound (G : StieltjesFunction) (w : ℝ → ℝ)
    (s t B : ℝ) (hst : s ≤ t) (hb : ∀ x ∈ Ioc s t, ‖w x‖ ≤ B) :
    ‖∫ x in s..t, w x ∂G.measure‖ ≤ B * (G t - G s) := by
  rw [intervalIntegral.integral_of_le hst]
  have hh := norm_setIntegral_le_of_norm_le_const (μ := G.measure)
    (s := Ioc s t) (by rw [G.measure_Ioc]; exact ENNReal.ofReal_lt_top) hb
  simpa [measureReal_def, G.measure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (G.mono hst)), mul_comm] using hh

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

/-- A physical primitive with bounded continuous coefficients becomes
Lipschitz under the actual dollar-variation clock, including singular controls. -/
theorem physicalBV_primitive_reparam_lipschitz
    (exec : StieltjesPairedExecution edges) (a b scale : ℝ) (hs : 0 < scale)
    (y f w : ℝ → ℝ) (coeff : κ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hw : ContinuousOn w (Icc a b))
    (hprim : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      y t - y s = (∫ x in s..t, f x) +
        ∑ e, coeff e * ∫ x in s..t, w x ∂(exec.cumulative e).measure)
    (time : Icc (exec.variationClock scale a) (exec.variationClock scale b) → Icc a b)
    (hright : ∀ u, exec.variationClock scale (time u) = (u : ℝ)) :
    ∃ C : ℝ≥0, LipschitzWith C (fun u => y (time u)) := by
  classical
  obtain ⟨A, hA⟩ := isCompact_Icc.bddAbove_image hf.norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hw.norm
  let A' := max A 0
  let B' := max B 0
  have hAn : 0 ≤ A' := le_max_right _ _
  have hBn : 0 ≤ B' := le_max_right _ _
  have hcoeff : 0 ≤ ∑ e, |coeff e| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let C : ℝ≥0 := ⟨A' + (∑ e, |coeff e|) * B' / scale, by positivity⟩
  have hordered (u v : Icc (exec.variationClock scale a) (exec.variationClock scale b))
      (huv : (u : ℝ) ≤ v) : |y (time v) - y (time u)| ≤ C * ((v : ℝ) - u) := by
    have htime : (time u : ℝ) ≤ time v :=
      (exec.variationClock_strictMono scale hs.le).le_iff_le.mp (by simpa [hright] using huv)
    have hdt := exec.physicalTime_le_clock_increment scale (time u) (time v) hs.le htime
    rw [hright, hright] at hdt
    have hI : |∫ x in (time u : ℝ)..(time v : ℝ), f x| ≤ A' * ((v : ℝ) - u) := by
      have hbound : ∀ x ∈ uIoc (time u : ℝ) (time v : ℝ), ‖f x‖ ≤ A' := by
        intro x hx
        rw [uIoc_of_le htime] at hx
        exact (hA (mem_image_of_mem _ ⟨(time u).property.1.trans hx.1.le,
          hx.2.trans (time v).property.2⟩)).trans (le_max_left _ _)
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (time u : ℝ)) (b := (time v : ℝ)) (C := A') hbound
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr htime)] at hh
      exact hh.trans (mul_le_mul_of_nonneg_left hdt hAn)
    have hedge (e : κ) : |∫ x in (time u : ℝ)..(time v : ℝ), w x ∂(exec.cumulative e).measure| ≤
        B' * (((v : ℝ) - u) / scale) := by
      have hm := exec.edgeMass_le_clock_increment scale (time u) (time v) hs.le htime e
      rw [exec.intervalMass_eq_delta e _ _ htime, hright, hright] at hm
      have hmass : (exec.cumulative e) (time v) - (exec.cumulative e) (time u) ≤
          ((v : ℝ) - u) / scale := (le_div_iff₀ hs).mpr (by nlinarith)
      have hh := stieltjes_interval_norm_bound (exec.cumulative e) w _ _ B' htime
        (fun x hx => (hB (mem_image_of_mem _ ⟨(time u).property.1.trans hx.1.le,
          hx.2.trans (time v).property.2⟩)).trans (le_max_left _ _))
      exact hh.trans (mul_le_mul_of_nonneg_left hmass hBn)
    rw [hprim (time u) (time u).property (time v) (time v).property]
    calc
      |(∫ x in (time u : ℝ)..(time v : ℝ), f x) +
          ∑ e, coeff e * ∫ x in (time u : ℝ)..(time v : ℝ), w x ∂(exec.cumulative e).measure| ≤
        |∫ x in (time u : ℝ)..(time v : ℝ), f x| +
          ∑ e, |coeff e| * |∫ x in (time u : ℝ)..(time v : ℝ), w x ∂(exec.cumulative e).measure| := by
            exact (abs_add_le _ _).trans (add_le_add_left
              ((Finset.abs_sum_le_sum_abs _ _).trans_eq (by simp only [abs_mul])) _)
      _ ≤ A' * ((v : ℝ) - u) + ∑ e, |coeff e| * (B' * (((v : ℝ) - u) / scale)) := by
        exact add_le_add hI (Finset.sum_le_sum (fun e _ =>
          mul_le_mul_of_nonneg_left (hedge e) (abs_nonneg _)))
      _ = C * ((v : ℝ) - u) := by
        dsimp [C]
        rw [← Finset.sum_mul]
        ring
  refine ⟨C, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  simp only [Real.dist_eq, Subtype.dist_eq]
  rcases le_total (u : ℝ) v with huv | hvu
  · rw [abs_sub_comm (y (time u)), abs_of_nonpos (sub_nonpos.mpr huv)]
    simpa only [neg_sub] using hordered u v huv
  · rw [abs_of_nonneg (sub_nonneg.mpr hvu)]
    exact hordered v u hvu

theorem PhysicalContinuousBVPiece.reparam_prices_lipschitz
    (m : PhysicalContinuousBVPiece edges) (scale : ℝ) (hs : 0 < scale)
    (time : Icc (m.execution.variationClock scale m.a) (m.execution.variationClock scale m.b) → Icc m.a m.b)
    (hright : ∀ u, m.execution.variationClock scale (time u) = (u : ℝ)) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C (fun u => m.prices (time u) i) := by
  apply physicalBV_primitive_reparam_lipschitz m.execution m.a m.b scale hs
    (fun x => m.prices x i) (fun x => -m.rho i * (m.prices x i - m.F i))
    (fun x => (m.response i).impact (m.prices x i) / m.prices x i) (pairedMatrix edges i)
    (continuousOn_const.mul ((m.continuous_prices i).sub continuousOn_const))
    (m.price_trade_integrand_continuous i) (m.physical_price_primitive i) time hright

theorem PhysicalContinuousBVPiece.reparam_shares_lipschitz
    (m : PhysicalContinuousBVPiece edges) (scale : ℝ) (hs : 0 < scale)
    (time : Icc (m.execution.variationClock scale m.a) (m.execution.variationClock scale m.b) → Icc m.a m.b)
    (hright : ∀ u, m.execution.variationClock scale (time u) = (u : ℝ)) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C (fun u => m.shares (time u) i) := by
  apply physicalBV_primitive_reparam_lipschitz m.execution m.a m.b scale hs
    (fun x => m.shares x i) (fun _ => 0) (fun x => 1 / m.prices x i) (pairedMatrix edges i)
    continuousOn_const (m.share_trade_integrand_continuous i) _ time hright
  intro s hs t ht
  simpa using m.physical_share_primitive i s hs t ht

end MarketCrash
