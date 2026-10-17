import MarketCrash.LocalResponseFlow

noncomputable section
namespace MarketCrash
open Filter
open scoped Topology

/-- Actual local scalar derivatives, used to compose the paper's pulse maps. -/
structure ScalarSecondJet (f : ℝ → ℝ) (x a b c : ℝ) : Prop where
  value : f x = a
  smooth : ContDiffAt ℝ 2 f x
  first : HasDerivAt f b x
  second : HasDerivAt (deriv f) c x

theorem ScalarSecondJet.comp {f g : ℝ → ℝ} {x a b c d e k : ℝ}
    (hf : ScalarSecondJet f a d e k) (hg : ScalarSecondJet g x a b c) :
    ScalarSecondJet (f ∘ g) x d (e*b) (k*b^2+e*c) := by
  refine ⟨by simp only [Function.comp_apply, hg.value, hf.value], ?_,
    (hg.value.symm ▸ hf.first).comp x hg.first, ?_⟩
  · exact (hg.value.symm ▸ hf.smooth).comp x hg.smooth
  · have hh := local_second_derivative_comp f g x
      (by simpa only [hg.value] using hf.smooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide))
      (hg.smooth.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide))
      (by simpa only [hg.value, hf.second.deriv] using hf.second)
      (by simpa only [hg.second.deriv] using hg.second)
    simpa only [hg.value, hf.first.deriv, hg.first.deriv, hf.second.deriv, hg.second.deriv] using hh

theorem scalarSecondJet_affine (m b x : ℝ) :
    ScalarSecondJet (fun t => m*t+b) x (m*x+b) m 0 := by
  refine ⟨rfl, by fun_prop, by convert ((hasDerivAt_id x).const_mul m).add_const b using 1 <;> simp, ?_⟩
  have he : deriv (fun t : ℝ => m*t+b) = fun _ => m := by
    funext t
    simpa using (((hasDerivAt_id t).const_mul m).add_const b).deriv
  rw [he]
  exact hasDerivAt_const x m

theorem ScalarSecondJet.add {f g : ℝ → ℝ} {x a b c d e k : ℝ}
    (hf : ScalarSecondJet f x a b c) (hg : ScalarSecondJet g x d e k) :
    ScalarSecondJet (fun t => f t+g t) x (a+d) (b+e) (c+k) := by
  refine ⟨by rw [hf.value,hg.value], hf.smooth.add hg.smooth, hf.first.add hg.first, ?_⟩
  have hfe := hf.smooth.eventually (by norm_num)
  have hge := hg.smooth.eventually (by norm_num)
  have he : deriv (fun t => f t+g t) =ᶠ[nhds x] fun t => deriv f t+deriv g t := by
    filter_upwards [hfe,hge] with t ht hu
    exact deriv_add (ht.differentiableAt (by decide)) (hu.differentiableAt (by decide))
  exact (hf.second.add hg.second).congr_of_eventuallyEq he

theorem ScalarSecondJet.scale {f : ℝ → ℝ} {x a b c : ℝ}
    (hf : ScalarSecondJet f x a b c) (m : ℝ) :
    ScalarSecondJet (fun t => m*f t) x (m*a) (m*b) (m*c) := by
  have hh := (scalarSecondJet_affine m 0 a).comp hf
  simpa only [Function.comp_def, add_zero, zero_mul, zero_add] using hh

theorem ScalarSecondJet.sub {f g : ℝ → ℝ} {x a b c d e k : ℝ}
    (hf : ScalarSecondJet f x a b c) (hg : ScalarSecondJet g x d e k) :
    ScalarSecondJet (fun t => f t-g t) x (a-d) (b-e) (c-k) := by
  have hh := hf.add (hg.scale (-1))
  simpa only [neg_one_mul, sub_eq_add_neg] using hh

theorem scalarSecondJet_const (a x : ℝ) : ScalarSecondJet (fun _ => a) x a 0 0 := by
  simpa only [zero_mul, zero_add] using scalarSecondJet_affine 0 a x

theorem scalarSecondJet_log_loss (F : ℝ) (hF : 0 < F) :
    ScalarSecondJet (fun S => Real.log F-Real.log S) F 0 (-1/F) (1/F^2) := by
  refine ⟨sub_self _, contDiffAt_const.sub (contDiffAt_id.log hF.ne'), ?_, ?_⟩
  · simpa only [zero_sub, neg_div, one_div] using (hasDerivAt_const F (Real.log F)).sub (Real.hasDerivAt_log hF.ne')
  · have he : deriv (fun S => Real.log F-Real.log S) =ᶠ[nhds F] fun S => -S⁻¹ := by
      filter_upwards [eventually_ne_nhds hF.ne'] with S hS
      simpa using ((hasDerivAt_const S (Real.log F)).sub (Real.hasDerivAt_log hS)).deriv
    have hh := (hasDerivAt_inv hF.ne').neg
    convert hh.congr_of_eventuallyEq he using 1 <;> simp

end MarketCrash
