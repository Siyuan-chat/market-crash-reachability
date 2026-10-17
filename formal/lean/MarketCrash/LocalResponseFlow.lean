import MarketCrash.Coordinates
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
namespace MarketCrash
open Set Filter
open scoped Topology

theorem coordinate_contDiffAt_four (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) : ContDiffAt ℝ 4 (coordinate F g.impact) F := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun S => (1 : ℝ →L[ℝ] ℝ).smulRight (S / g.impact S), ?_, ?_⟩
  · refine ⟨Ioi 0, Ioi_mem_nhds hF, ?_⟩
    intro S hS
    exact (coordinate_hasDerivAt F g hF hS).hasFDerivAt
  · exact contDiffAt_const.smulRight (contDiffAt_id.div hg (g.positive F hF).ne')

/-- A local genuine inverse response, with no assumed price-response
identity. All inverse and derivative properties follow from the IFT. -/
theorem exists_local_response_inverse (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) :
    ∃ R : ℝ → ℝ, R 0 = F ∧ ContDiffAt ℝ 3 R 0 ∧
      (∀ᶠ y in nhds 0, 0 < R y ∧ coordinate F g.impact (R y) = y ∧
        HasDerivAt R (g.impact (R y) / R y) y) := by
  have hcoord := coordinate_hasDerivAt F g hF hF
  have hc := coordinate_contDiffAt_four F g hF hg
  have hs := hc.hasStrictDerivAt' hcoord (by norm_num)
  have hn : F / g.impact F ≠ 0 := div_ne_zero hF.ne' (g.positive _ hF).ne'
  let p := (hs.hasStrictFDerivAt_equiv hn).toPartialHomeomorph (coordinate F g.impact)
  have hpmap : (p : ℝ → ℝ) = coordinate F g.impact := rfl
  have hsource : F ∈ p.source := (hs.hasStrictFDerivAt_equiv hn).mem_toPartialHomeomorph_source
  have htarget : (0 : ℝ) ∈ p.target := by
    simpa only [hpmap, coordinate_at_benchmark] using p.map_source hsource
  have hzero : p.symm 0 = F := by
    have hh := p.left_inv hsource
    simpa only [hpmap, coordinate_at_benchmark] using hh
  have hR : ContDiffAt ℝ 3 p.symm 0 := by
    apply p.contDiffAt_symm_deriv hn htarget
    · simpa [hzero] using hcoord
    · simpa [hpmap, hzero] using hc.of_le (show (3 : WithTop ℕ∞) ≤ 4 by decide)
  refine ⟨p.symm, hzero, hR, ?_⟩
  have hpos : ∀ᶠ y in nhds 0, 0 < p.symm y :=
    (p.continuousAt_symm htarget).eventually (Ioi_mem_nhds (hzero ▸ hF))
  filter_upwards [p.open_target.mem_nhds htarget, hpos] with y hy hpy
  have hright : coordinate F g.impact (p.symm y) = y := p.right_inv hy
  have hd := p.hasDerivAt_symm hy (div_ne_zero hpy.ne' (g.positive _ hpy).ne')
    (coordinate_hasDerivAt F g hF hpy)
  refine ⟨hpy, hright, ?_⟩
  convert hd using 1
  simp only [inv_div]

theorem exists_local_response_chart (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) :
    ∃ (R : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ R 0 = F ∧
      ContDiffOn ℝ 3 R (Metric.ball 0 ε) ∧
      ∀ y ∈ Metric.ball 0 ε, 0 < R y ∧ coordinate F g.impact (R y) = y ∧
        HasDerivAt R (g.impact (R y) / R y) y := by
  obtain ⟨R, hR0, hR, hp⟩ := exists_local_response_inverse F g hF hg
  obtain ⟨U, hU, hCU⟩ := hR.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp (hp.and hU)
  refine ⟨R, ε, hε, hR0, hCU.mono ?_, ?_⟩
  · intro y hy
    exact (hb hy).2
  · intro y hy
    exact (hb hy).1

/-- The first two genuine inverse-response jets at the benchmark. -/
theorem local_response_inverse_jets (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y) / R y) y) :
    HasDerivAt R (g.impact F / F) 0 ∧
    HasDerivAt (deriv R)
      (g.impact F * (F * deriv g.impact F - g.impact F) / F ^ 3) 0 := by
  have hd : HasDerivAt R (g.impact F / F) 0 := by
    simpa [hR0] using hp.self_of_nhds
  refine ⟨hd, ?_⟩
  have heq : deriv R =ᶠ[nhds 0] (fun y => g.impact (R y) / R y) :=
    hp.mono fun y hy => hy.deriv
  have hgd : HasDerivAt g.impact (deriv g.impact F) F :=
    (hg.differentiableAt (by norm_num)).hasDerivAt
  have hc := ((hR0.symm ▸ hgd).comp 0 hd).div hd (hR0 ▸ hF.ne')
  have hc' := hc.congr_of_eventuallyEq heq
  convert hc' using 1
  simp only [Function.comp_apply, hR0]
  field_simp
  ring

/-- A local C3 response has a genuine uniform one-sided cubic remainder. -/
theorem local_cubic_taylor_bound (f : ℝ → ℝ) (hf : ContDiffAt ℝ 3 f 0) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε,
      ‖f h - (f 0 + deriv f 0 * h + deriv (deriv f) 0 / 2 * h ^ 2)‖ ≤ C * h ^ 3 := by
  obtain ⟨U, hU, hCU⟩ := hf.contDiffOn (m := 3) le_rfl (by simp)
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hU
  let ε := r / 2
  have hε : 0 < ε := half_pos hr
  have hsub : Icc 0 ε ⊆ U := by
    intro x hx
    apply hb
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hx.1]
    exact hx.2.trans_lt (by dsimp [ε]; linarith)
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 2) hε.le (hCU.mono hsub)
  have hjet (n : ℕ) (hn : (n : WithTop ℕ∞) ≤ 3) :
      iteratedDerivWithin n f (Icc 0 ε) 0 = iteratedDeriv n f 0 := by
    unfold iteratedDerivWithin iteratedDeriv
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc hε)
      (hf.of_le hn) (left_mem_Icc.mpr hε.le)]
  refine ⟨ε, C, hε, ?_⟩
  intro h hh
  have hhC := hC h hh
  have ht : taylorWithinEval f 2 (Icc 0 ε) 0 h =
      f 0 + deriv f 0 * h + deriv (deriv f) 0 / 2 * h ^ 2 := by
    rw [show 2 = 1 + 1 from rfl, taylorWithinEval_succ,
      show 1 = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval,
      hjet 1 (by decide), hjet 2 (by decide)]
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, Nat.factorial_zero,
      Nat.factorial_one, Nat.cast_zero, Nat.cast_one, zero_add, one_mul,
      inv_one, sub_zero, pow_one, smul_eq_mul]
    norm_num
    ring
  simpa only [ht, sub_zero] using hhC

/-- Scalar second-order chain rule, retaining only local smoothness. -/
theorem local_second_derivative_comp (f g : ℝ → ℝ) (x : ℝ)
    (hf : ContDiffAt ℝ 1 f (g x)) (hg : ContDiffAt ℝ 1 g x)
    (hf2 : HasDerivAt (deriv f) (deriv (deriv f) (g x)) (g x))
    (hg2 : HasDerivAt (deriv g) (deriv (deriv g) x) x) :
    HasDerivAt (deriv (f ∘ g))
      (deriv (deriv f) (g x) * (deriv g x) ^ 2 +
        deriv f (g x) * deriv (deriv g) x) x := by
  have hge := hg.eventually (by decide)
  have hfe := hg.continuousAt.eventually (hf.eventually (by decide))
  have heq : deriv (f ∘ g) =ᶠ[nhds x] fun y => deriv f (g y) * deriv g y := by
    filter_upwards [hge, hfe] with y hgy hfy
    exact deriv_comp y (hfy.differentiableAt le_rfl) (hgy.differentiableAt le_rfl)
  have hbase := (hf2.comp x (hg.differentiableAt le_rfl).hasDerivAt).mul hg2
  have hh := hbase.congr_of_eventuallyEq heq
  convert hh using 1
  simp only [Function.comp_apply]
  ring

theorem coordinate_second_derivative (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) :
    HasDerivAt (deriv (coordinate F g.impact))
      ((g.impact F - F * deriv g.impact F) / (g.impact F) ^ 2) F := by
  have heq : deriv (coordinate F g.impact) =ᶠ[nhds F]
      fun x => x / g.impact x := by
    filter_upwards [Ioi_mem_nhds hF] with x hx
    exact (coordinate_hasDerivAt F g hF hx).deriv
  have hd := (hasDerivAt_id F).div
    (hg.differentiableAt (by norm_num)).hasDerivAt (g.positive F hF).ne'
  simpa only [one_mul, id_eq] using hd.congr_of_eventuallyEq heq

theorem exists_inverse_response_cubic_bound (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) :
    ∃ (R : ℝ → ℝ) (ε C : ℝ), 0 < ε ∧ R 0 = F ∧ ContDiffAt ℝ 3 R 0 ∧
      (∀ᶠ y in nhds 0, 0 < R y ∧ coordinate F g.impact (R y) = y ∧
        HasDerivAt R (g.impact (R y) / R y) y) ∧
      ∀ h ∈ Icc 0 ε,
        ‖R h - (F + g.impact F / F * h +
          (g.impact F * (F * deriv g.impact F - g.impact F) / F ^ 3) / 2 * h ^ 2)‖
          ≤ C * h ^ 3 := by
  obtain ⟨R, hR0, hR, hp⟩ := exists_local_response_inverse F g hF hg
  obtain ⟨ε, C, hε, hb⟩ := local_cubic_taylor_bound R hR
  have hj := local_response_inverse_jets F g hF hg R hR0 (hp.mono fun _ h => h.2.2)
  refine ⟨R, ε, C, hε, hR0, hR, hp, ?_⟩
  intro h hh
  simpa only [hR0, hj.1.deriv, hj.2.deriv] using hb h hh

end MarketCrash
