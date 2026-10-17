import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import MarketCrash.LipschitzFTC
import MarketCrash.Coordinates
import Mathlib.Analysis.Calculus.Taylor

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace MarketCrash

/-- Bounded globally Lipschitz scalar fields have genuine solutions over any
fixed finite interval; no local endpoint or invariant-strip hypothesis. -/
theorem bounded_scalar_ode_exists (v : ℝ → ℝ) (L : ℝ≥0) (C a b x₀ : ℝ)
    (hab : a ≤ b) (hC : 0 ≤ C) (hv : LipschitzWith L v) (hb : ∀ x, ‖v x‖ ≤ C) :
    ∃ X : ℝ → ℝ, X a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt X (v (X t)) (Icc a b) t) ∧
      LipschitzOnWith ⟨C,hC⟩ X (Icc a b) := by
  have hp : IsPicardLindelof (fun _ x => v x) a a b x₀ L (C*(b-a)) C := by
    refine ⟨⟨le_rfl,hab⟩,mul_nonneg hC (sub_nonneg.mpr hab),
      fun _ _ => hv.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ x _ => hb x, ?_⟩
    simp only [sub_self, max_eq_left (sub_nonneg.mpr hab)]
    exact le_rfl
  obtain ⟨X,hX,hd⟩ := hp.exists_forall_hasDerivWithinAt_Icc_eq x₀
  refine ⟨X,hX,hd,?_⟩
  exact (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => hd t ht)
    (fun t ht => by exact_mod_cast hb (X t))

/-- Quantitative error against a real approximate trajectory. The residual
bound is proved separately from the original nonlinear vector field. -/
theorem scalar_ode_residual_bound (v : ℝ → ℝ) (L : ℝ≥0)
    (X Q Q' : ℝ → ℝ) (a b δ ε : ℝ)
    (hv : LipschitzWith L v) (hX : ContinuousOn X (Icc a b))
    (hXd : ∀ t ∈ Ico a b, HasDerivWithinAt X (v (X t)) (Ici t) t)
    (hQ : ContinuousOn Q (Icc a b))
    (hQd : ∀ t ∈ Ico a b, HasDerivWithinAt Q (Q' t) (Ici t) t)
    (hres : ∀ t ∈ Ico a b, dist (Q' t) (v (Q t)) ≤ ε)
    (hinit : dist (X a) (Q a) ≤ δ) :
    ∀ t ∈ Icc a b, dist (X t) (Q t) ≤ gronwallBound δ L ε (t-a) := by
  simpa only [zero_add] using dist_le_of_approx_trajectories_ODE
    (v := fun _ x => v x) (εf := 0) (εg := ε) (fun _ => hv) hX hXd (fun _ _ => by simp)
    hQ hQd hres hinit

def responseClamp (F δ x : ℝ) : ℝ := max (F-δ) (min x (F+δ))

theorem responseClamp_mem (F δ x : ℝ) (hδ : 0 ≤ δ) :
    responseClamp F δ x ∈ Icc (F-δ) (F+δ) :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

theorem responseClamp_eq (F δ x : ℝ) (hx : x ∈ Icc (F-δ) (F+δ)) :
    responseClamp F δ x = x := by
  simp [responseClamp, min_eq_left hx.2, max_eq_right hx.1]

theorem responseClamp_lipschitz (F δ : ℝ) : LipschitzWith 1 (responseClamp F δ) := by
  simpa [responseClamp] using
    (LipschitzWith.const (F-δ)).max (LipschitzWith.id.min (LipschitzWith.const (F+δ)))

/-- Local original response regularity supplies a bounded global Lipschitz
extension agreeing with g(S)/S throughout a positive price neighborhood. -/
theorem exists_bounded_response_extension (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) :
    ∃ (δ M : ℝ) (L : ℝ≥0) (H : ℝ → ℝ), 0 < δ ∧ δ < F ∧ 0 ≤ M ∧
      LipschitzWith L H ∧ (∀ x, |H x| ≤ M) ∧
      ∀ x ∈ Icc (F-δ) (F+δ), H x = g.impact x / x := by
  let h : ℝ → ℝ := fun x => g.impact x / x
  have hh : ContDiffAt ℝ 1 h F :=
    (hg.of_le (show (1 : WithTop ℕ∞) ≤ 3 by decide)).div contDiffAt_id hF.ne'
  obtain ⟨L,U,hU,hLip⟩ := hh.exists_lipschitzOnWith
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hU
  let δ := min (F/2) (r/2)
  have hδ : 0 < δ := lt_min (half_pos hF) (half_pos hr)
  have hδF : δ < F := (min_le_left _ _).trans_lt (by linarith)
  have hsub : Icc (F-δ) (F+δ) ⊆ U := by
    intro x hx
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    have hd : δ ≤ r/2 := min_le_right _ _
    constructor <;> linarith [hx.1,hx.2]
  let H : ℝ → ℝ := fun x => h (responseClamp F δ x)
  have hHL : LipschitzWith L H := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    exact (hLip.dist_le_mul _ (hsub (responseClamp_mem F δ x hδ.le)) _
      (hsub (responseClamp_mem F δ y hδ.le))).trans
      (by simpa using mul_le_mul_of_nonneg_left ((responseClamp_lipschitz F δ).dist_le_mul x y) L.coe_nonneg)
  have hcenter : H F = h F := by
    dsimp [H]
    rw [responseClamp_eq F δ F ⟨by linarith,by linarith⟩]
  let M := |h F| + L*δ
  have hM : 0 ≤ M := add_nonneg (abs_nonneg _) (mul_nonneg L.coe_nonneg hδ.le)
  refine ⟨δ,M,L,H,hδ,hδF,hM,hHL,?_,?_⟩
  · intro x
    have hl := hLip.dist_le_mul _ (hsub (responseClamp_mem F δ x hδ.le)) F (hsub ⟨by linarith,by linarith⟩)
    have hc : |responseClamp F δ x-F| ≤ δ := by
      rw [abs_le]
      have hm := responseClamp_mem F δ x hδ.le
      constructor <;> linarith [hm.1,hm.2]
    have ht := abs_add_le (H x - h F) (h F)
    simp only [sub_add_cancel] at ht
    dsimp [H] at ht ⊢
    rw [Real.dist_eq,Real.dist_eq] at hl
    have hl' := hl.trans (mul_le_mul_of_nonneg_left hc L.coe_nonneg)
    dsimp [M]
    linarith
  · intro x hx
    dsimp [H,h]
    rw [responseClamp_eq F δ x hx]

def clampedResponseField (F ρ δ p : ℝ) (H : ℝ → ℝ) (x : ℝ) : ℝ :=
  -ρ * (responseClamp F δ x-F) + p * H x

theorem clampedResponseField_lipschitz (F ρ δ p : ℝ) (H : ℝ → ℝ) (L : ℝ≥0)
    (hH : LipschitzWith L H) :
    LipschitzWith ⟨|ρ|+|p| *L, by positivity⟩ (clampedResponseField F ρ δ p H) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hc := (responseClamp_lipschitz F δ).dist_le_mul x y
  have hh := hH.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc hh ⊢
  have he : clampedResponseField F ρ δ p H x - clampedResponseField F ρ δ p H y =
      -ρ*(responseClamp F δ x-responseClamp F δ y)+p*(H x-H y) := by
    unfold clampedResponseField
    ring
  rw [he]
  calc
    _ ≤ |-ρ*(responseClamp F δ x-responseClamp F δ y)|+|p*(H x-H y)| := abs_add_le _ _
    _ = |ρ| *|responseClamp F δ x-responseClamp F δ y|+|p| *|H x-H y| := by rw [abs_mul,abs_mul,abs_neg]
    _ ≤ |ρ| *|x-y|+|p| *(L*|x-y|) := add_le_add
      (mul_le_mul_of_nonneg_left hc (abs_nonneg _)) (mul_le_mul_of_nonneg_left hh (abs_nonneg _))
    _ = _ := by simp only [NNReal.coe_mk]; ring

theorem clampedResponseField_bound (F ρ δ p M : ℝ) (H : ℝ → ℝ)
    (hδ : 0 ≤ δ) (hH : ∀ x, |H x| ≤ M) :
    ∀ x, ‖clampedResponseField F ρ δ p H x‖ ≤ |ρ| *δ+|p| *M := by
  intro x
  have hc : |responseClamp F δ x-F| ≤ δ := by
    rw [abs_le]
    have hm := responseClamp_mem F δ x hδ
    constructor <;> linarith [hm.1,hm.2]
  simp only [clampedResponseField, Real.norm_eq_abs]
  exact (abs_add_le _ _).trans (by
    rw [abs_mul,abs_neg,abs_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hc (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (hH x) (abs_nonneg _)))

theorem clamped_response_ode_exists (F ρ δ p M a b x₀ : ℝ) (H : ℝ → ℝ) (L : ℝ≥0)
    (hab : a ≤ b) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hH : LipschitzWith L H)
    (hb : ∀ x, |H x| ≤ M) :
    ∃ X : ℝ → ℝ, X a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt X (clampedResponseField F ρ δ p H (X t)) (Icc a b) t) ∧
      LipschitzOnWith ⟨|ρ| *δ+|p| *M,by positivity⟩ X (Icc a b) := by
  exact bounded_scalar_ode_exists _ _ _ a b x₀ hab (by positivity)
    (clampedResponseField_lipschitz F ρ δ p H L hH)
    (clampedResponseField_bound F ρ δ p M H hδ hb)

theorem local_quadratic_right_bound (f : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ x ∈ Icc 0 ε,
      |f x - f 0 - deriv f 0 * x| ≤ C*x^2 := by
  obtain ⟨U,hU,hCU⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨r,hr,hb⟩ := Metric.mem_nhds_iff.mp hU
  let ε := r/2
  have hε : 0 < ε := half_pos hr
  have hsub : Icc 0 ε ⊆ U := by
    intro x hx
    apply hb
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg hx.1]
    exact hx.2.trans_lt (by dsimp [ε];linarith)
  obtain ⟨C,hC⟩ := exists_taylor_mean_remainder_bound (n := 1) hε.le (hCU.mono hsub)
  have hj : iteratedDerivWithin 1 f (Icc 0 ε) 0 = deriv f 0 := by
    unfold iteratedDerivWithin
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (n := 1) (uniqueDiffOn_Icc hε)
      (hf.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)) (left_mem_Icc.mpr hε.le)]
    exact congrFun iteratedDeriv_one 0
  refine ⟨ε,C,hε,?_⟩
  intro x hx
  have ht : taylorWithinEval f 1 (Icc 0 ε) 0 x = f 0 + deriv f 0*x := by
    rw [show 1 = 0+1 from rfl,taylorWithinEval_succ,taylor_within_zero_eval,hj]
    simp [mul_comm]
  have hh := hC x hx
  simpa only [ht,sub_zero,Real.norm_eq_abs,sub_add_eq_sub_sub] using hh

theorem local_quadratic_bound (f : ℝ → ℝ) (hf : ContDiffAt ℝ 2 f 0) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 ≤ C ∧ ∀ x, |x| ≤ ε →
      |f x-f 0-deriv f 0*x| ≤ C*x^2 := by
  obtain ⟨ε₁,C₁,hε₁,hb₁⟩ := local_quadratic_right_bound f hf
  have hfn : ContDiffAt ℝ 2 (fun x => f (-x)) 0 := by
    exact (show ContDiffAt ℝ 2 f (-0) by simpa using hf).comp 0 contDiffAt_id.neg
  obtain ⟨ε₂,C₂,hε₂,hb₂⟩ := local_quadratic_right_bound (fun x => f (-x)) hfn
  have hd : deriv (fun x => f (-x)) 0 = -deriv f 0 := by
    have hf' : HasDerivAt f (deriv f 0) (-0) := by simpa using (hf.differentiableAt (by decide)).hasDerivAt
    simpa using (hf'.comp 0 (hasDerivAt_neg (0:ℝ))).deriv
  refine ⟨min ε₁ ε₂,max |C₁| |C₂|,lt_min hε₁ hε₂,(abs_nonneg C₁).trans (le_max_left _ _),?_⟩
  intro x hx
  rcases le_total 0 x with hpos | hneg
  · exact (hb₁ x ⟨hpos,(le_abs_self x).trans (hx.trans (min_le_left _ _))⟩).trans
      (mul_le_mul_of_nonneg_right ((le_abs_self C₁).trans (le_max_left _ _)) (sq_nonneg x))
  · have hh := hb₂ (-x) ⟨neg_nonneg.mpr hneg,by rw [←abs_of_nonpos hneg]; exact hx.trans (min_le_right _ _)⟩
    simp only [neg_neg,neg_zero,hd,neg_mul_neg,neg_sq] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right ((le_abs_self C₂).trans (le_max_right _ _)) (sq_nonneg x))

theorem response_quotient_taylor_bound (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ S, |S-F| ≤ δ →
      |g.impact S/S-g.impact F/F-
        ((F*deriv g.impact F-g.impact F)/F^2)*(S-F)| ≤ C*(S-F)^2 := by
  let f : ℝ → ℝ := fun x => g.impact (F+x)/(F+x)
  have hq : ContDiffAt ℝ 2 (fun S => g.impact S/S) F :=
    (hg.of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)).div contDiffAt_id hF.ne'
  have hf : ContDiffAt ℝ 2 f 0 := by
    have hh : ContDiffAt ℝ 2 (fun S => g.impact S/S) (F+0) := by simpa using hq
    exact hh.comp 0 (contDiffAt_const.add contDiffAt_id)
  have hqd := (hg.differentiableAt (by decide)).hasDerivAt.div (hasDerivAt_id F) hF.ne'
  have hd : deriv f 0 = (F*deriv g.impact F-g.impact F)/F^2 := by
    have hh : HasDerivAt (fun S => g.impact S/S)
        ((deriv g.impact F*F-g.impact F)/F^2) (F+0) := by simpa using hqd
    have hh' := (hh.comp 0 ((hasDerivAt_id (0:ℝ)).const_add F)).deriv
    convert hh' using 1 <;> dsimp [f,Function.comp_def] <;> ring
  obtain ⟨δ,C,hδ,hC,hb⟩ := local_quadratic_bound f hf
  refine ⟨δ,C,hδ,hC,?_⟩
  intro S hS
  have hh := hb (S-F) hS
  simpa only [f,hd,add_sub_cancel,add_zero] using hh

/-- Cubic nonlinear residual of the second-order price approximation. -/
theorem nonlinear_response_cubic_residual
    (H : ℝ → ℝ) (F h₀ h₁ p y z K Y Z f : ℝ)
    (hp : |p| ≤ 1) (hK : 0 ≤ K) (hY : 0 ≤ Y) (hZ : 0 ≤ Z)
    (hy : |y| ≤ Y) (hz : |z| ≤ Z)
    (ht : |H (F+p*y+p^2*z)-h₀-h₁*(p*y+p^2*z)| ≤ K*(p*y+p^2*z)^2) :
    |p*f*(h₀+h₁*p*y-H (F+p*y+p^2*z))| ≤
      |p|^3 * |f| * (|h₁| * Z+K*(Y+Z)^2) := by
  have hp2 : |p|^2 ≤ |p| := by nlinarith [abs_nonneg p]
  have hq : |p*y+p^2*z| ≤ |p| *(Y+Z) := by
    calc
      _ ≤ |p*y|+|p^2*z| := abs_add_le _ _
      _ = |p| * |y|+|p|^2 * |z| := by rw [abs_mul,abs_mul,abs_pow]
      _ ≤ |p| * Y+|p|^2 * Z := add_le_add (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hz (sq_nonneg _))
      _ ≤ _ := by nlinarith
  have hq2 : (p*y+p^2*z)^2 ≤ |p|^2*(Y+Z)^2 := by
    have hh := mul_le_mul hq hq (abs_nonneg _) (mul_nonneg (abs_nonneg p) (add_nonneg hY hZ))
    nlinarith [sq_abs (p*y+p^2*z)]
  have he : h₀+h₁*p*y-H (F+p*y+p^2*z) =
      -(H (F+p*y+p^2*z)-h₀-h₁*(p*y+p^2*z))-h₁*p^2*z := by ring
  rw [abs_mul,abs_mul,he]
  have hinner : |-(H (F+p*y+p^2*z)-h₀-h₁*(p*y+p^2*z))-h₁*p^2*z| ≤
      |p|^2 * (|h₁| * Z+K*(Y+Z)^2) := by
    calc
      _ ≤ |H (F+p*y+p^2*z)-h₀-h₁*(p*y+p^2*z)|+|h₁| * |p|^2 * |z| := by
        have hh := abs_sub_le (-(H (F+p*y+p^2*z)-h₀-h₁*(p*y+p^2*z))) 0 (h₁*p^2*z)
        simp only [sub_zero,zero_sub,abs_neg] at hh
        simpa only [abs_mul,abs_pow] using hh
      _ ≤ K*(|p|^2*(Y+Z)^2)+|h₁| * |p|^2 * Z := add_le_add
        (ht.trans (mul_le_mul_of_nonneg_left hq2 hK))
        (mul_le_mul_of_nonneg_left hz (mul_nonneg (abs_nonneg h₁) (sq_nonneg _)))
      _ = _ := by ring
  have hh := mul_le_mul_of_nonneg_left hinner (mul_nonneg (abs_nonneg p) (abs_nonneg f))
  convert hh using 1 <;> ring

theorem bounded_primitive_lipschitz (w : ℝ → ℝ) (a b K : ℝ) (hab : a ≤ b) (hK : 0 ≤ K)
    (hi : IntervalIntegrable w volume a b) (hb : ∀ t ∈ Icc a b, ‖w t‖ ≤ K) :
    LipschitzOnWith ⟨K,hK⟩ (fun t => ∫ s in a..t, w s) (Icc a b) := by
  have hfull : uIcc a b = Icc a b := uIcc_of_le hab
  have hisub (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) : IntervalIntegrable w volume s t :=
    hi.mono_set (by rw [hfull]; exact uIcc_subset_Icc hs ht)
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro s hs t ht
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hadd := intervalIntegral.integral_add_adjacent_intervals (hisub a t ha ht) (hisub t s ht hs)
  have heq : (∫ u in a..s, w u)-(∫ u in a..t, w u) = ∫ u in t..s, w u := by linarith
  rw [Real.dist_eq,heq,Real.dist_eq]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu =>
    hb u ((uIcc_subset_Icc ht hs) (uIoc_subset_uIcc hu)))

theorem bounded_lipschitz_product (f g : ℝ → ℝ) (s : Set ℝ) (K L : ℝ≥0)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hf : LipschitzOnWith K f s) (hg : LipschitzOnWith L g s)
    (hfb : ∀ x ∈ s, |f x| ≤ M) (hgb : ∀ x ∈ s, |g x| ≤ N) :
    LipschitzOnWith ⟨M*L+N*K,by positivity⟩ (fun x => f x*g x) s := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hf' := hf.dist_le_mul x hx y hy
  have hg' := hg.dist_le_mul x hx y hy
  simp only [Real.dist_eq] at hf' hg' ⊢
  have he : f x*g x-f y*g y = f x*(g x-g y)+(f x-f y)*g y := by ring
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|(f x-f y)*g y| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|f x-f y| * |g y| := by rw [abs_mul,abs_mul]
    _ ≤ M*(L*|x-y|)+(K*|x-y|)*N := add_le_add
      (mul_le_mul (hfb x hx) hg' (abs_nonneg _) hM)
      (mul_le_mul hf' (hgb y hy) (abs_nonneg _) (mul_nonneg K.coe_nonneg (abs_nonneg _)))
    _ = _ := by simp only [NNReal.coe_mk];ring

theorem bounded_field_solution_approximation (v : ℝ → ℝ) (L : ℝ≥0)
    (C a b x₀ δ ε : ℝ) (Q Q' : ℝ → ℝ) (hab : a ≤ b) (hC : 0 ≤ C)
    (hv : LipschitzWith L v) (hb : ∀ x, ‖v x‖ ≤ C)
    (hQ : ContinuousOn Q (Icc a b))
    (hQd : ∀ t ∈ Icc a b, HasDerivWithinAt Q (Q' t) (Icc a b) t)
    (hres : ∀ t ∈ Ico a b, dist (Q' t) (v (Q t)) ≤ ε)
    (hinit : dist x₀ (Q a) ≤ δ) :
    ∃ X : ℝ → ℝ, X a = x₀ ∧
      (∀ t ∈ Icc a b, HasDerivWithinAt X (v (X t)) (Icc a b) t) ∧
      LipschitzOnWith ⟨C,hC⟩ X (Icc a b) ∧
      ∀ t ∈ Icc a b, dist (X t) (Q t) ≤ gronwallBound δ L ε (t-a) := by
  obtain ⟨X,hX,hd,hL⟩ := bounded_scalar_ode_exists v L C a b x₀ hab hC hv hb
  refine ⟨X,hX,hd,hL,?_⟩
  apply scalar_ode_residual_bound v L X Q Q' a b δ ε hv hL.continuousOn
  · intro t ht
    exact (hd t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · exact hQ
  · intro t ht
    exact (hQd t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  · exact hres
  · simpa only [hX] using hinit

def joinSolution (b : ℝ) (X Y : ℝ → ℝ) (t : ℝ) : ℝ := if t < b then X t else Y t

theorem joinSolution_eq_left (b : ℝ) (X Y : ℝ → ℝ) (hjoin : X b = Y b)
    (t : ℝ) (ht : t ≤ b) : joinSolution b X Y t = X t := by
  by_cases h : t < b
  · simp [joinSolution,h]
  · have he : t = b := le_antisymm ht (not_lt.mp h)
    subst t
    simp [joinSolution,hjoin]

theorem joinSolution_eq_right (b : ℝ) (X Y : ℝ → ℝ) (t : ℝ) (ht : b ≤ t) :
    joinSolution b X Y t = Y t := by simp [joinSolution,not_lt.mpr ht]

theorem joinSolution_lipschitz (a b c : ℝ) (hab : a ≤ b) (hbc : b ≤ c)
    (X Y : ℝ → ℝ) (K L : ℝ≥0) (hX : LipschitzOnWith K X (Icc a b))
    (hY : LipschitzOnWith L Y (Icc b c)) (hjoin : X b = Y b) :
    LipschitzOnWith (K+L) (joinSolution b X Y) (Icc a c) := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  have hord (x y : ℝ) (hx : x ∈ Icc a c) (hy : y ∈ Icc a c) (hxy : x ≤ y) :
      dist (joinSolution b X Y x) (joinSolution b X Y y) ≤ (K+L : ℝ≥0)*dist x y := by
    by_cases hyb : y ≤ b
    · rw [joinSolution_eq_left b X Y hjoin x (hxy.trans hyb),joinSolution_eq_left b X Y hjoin y hyb]
      exact (hX.dist_le_mul x ⟨hx.1,hxy.trans hyb⟩ y ⟨hy.1,hyb⟩).trans
        (mul_le_mul_of_nonneg_right (by simp) dist_nonneg)
    · have hby : b ≤ y := (not_le.mp hyb).le
      by_cases hxb : b ≤ x
      · rw [joinSolution_eq_right b X Y x hxb,joinSolution_eq_right b X Y y hby]
        exact (hY.dist_le_mul x ⟨hxb,hx.2⟩ y ⟨hby,hy.2⟩).trans
          (mul_le_mul_of_nonneg_right (by simp) dist_nonneg)
      · have hxb' : x ≤ b := (not_le.mp hxb).le
        rw [joinSolution_eq_left b X Y hjoin x hxb',joinSolution_eq_right b X Y y hby]
        have hYb : dist (X b) (Y y) ≤ L*dist b y := by
          rw [hjoin]
          exact hY.dist_le_mul b ⟨le_rfl,hbc⟩ y ⟨hby,hy.2⟩
        have hh := (dist_triangle (X x) (X b) (Y y)).trans
          (add_le_add (hX.dist_le_mul x ⟨hx.1,hxb'⟩ b ⟨hab,le_rfl⟩) hYb)
        refine hh.trans ?_
        simp only [NNReal.coe_add,Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hxb'),
          abs_of_nonpos (sub_nonpos.mpr hby),abs_of_nonpos (sub_nonpos.mpr hxy)]
        nlinarith [mul_nonneg K.coe_nonneg (sub_nonneg.mpr hby),mul_nonneg L.coe_nonneg (sub_nonneg.mpr hxb')]
  intro x hx y hy
  rcases le_total x y with hxy | hyx
  · exact hord x y hx hy hxy
  · simpa only [dist_comm] using hord y x hy hx hyx

theorem joinSolution_right_ode (a b c : ℝ) (X Y : ℝ → ℝ)
    (v w : ℝ → ℝ → ℝ) (hjoin : X b = Y b)
    (hX : ∀ t ∈ Ico a b, HasDerivWithinAt X (v t (X t)) (Ici t) t)
    (hY : ∀ t ∈ Ico b c, HasDerivWithinAt Y (w t (Y t)) (Ici t) t) :
    ∀ t ∈ Ico a c, HasDerivWithinAt (joinSolution b X Y)
      ((if t < b then v t else w t) (joinSolution b X Y t)) (Ici t) t := by
  intro t ht
  by_cases htb : t < b
  · have he : joinSolution b X Y =ᶠ[nhdsWithin t (Ici t)] X := by
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds htb)] with s hs
      have hs' : s < b := hs
      exact if_pos hs'
    have hd := (hX t ⟨ht.1,htb⟩).congr_of_eventuallyEq_of_mem he (by simp)
    simpa only [if_pos htb,joinSolution_eq_left b X Y hjoin t htb.le] using hd
  · have hbt : b ≤ t := not_lt.mp htb
    have he : joinSolution b X Y =ᶠ[nhdsWithin t (Ici t)] Y := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact joinSolution_eq_right b X Y s (hbt.trans hs)
    have hd := (hY t ⟨hbt,ht.2⟩).congr_of_eventuallyEq_of_mem he (by simp)
    simpa only [if_neg htb,joinSolution_eq_right b X Y t hbt] using hd

theorem three_stage_bounded_ode_exists (Δ C x₀ : ℝ) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (v₁ v₂ v₃ : ℝ → ℝ) (L : ℝ≥0)
    (h₁ : LipschitzWith L v₁) (h₂ : LipschitzWith L v₂) (h₃ : LipschitzWith L v₃)
    (hb₁ : ∀ x, ‖v₁ x‖ ≤ C) (hb₂ : ∀ x, ‖v₂ x‖ ≤ C) (hb₃ : ∀ x, ‖v₃ x‖ ≤ C) :
    ∃ (X : ℝ → ℝ) (K : ℝ≥0), X 0 = x₀ ∧ LipschitzOnWith K X (Icc 0 (3*Δ)) ∧
      ∀ t ∈ Ico 0 (3*Δ), HasDerivWithinAt X
        ((if t < Δ then v₁ else if t < 2*Δ then v₂ else v₃) (X t)) (Ici t) t := by
  obtain ⟨X₁,hX₁,hd₁,hL₁⟩ := bounded_scalar_ode_exists v₁ L C 0 Δ x₀ hΔ.le hC h₁ hb₁
  obtain ⟨X₂,hX₂,hd₂,hL₂⟩ := bounded_scalar_ode_exists v₂ L C Δ (2*Δ) (X₁ Δ) (by linarith) hC h₂ hb₂
  obtain ⟨X₃,hX₃,hd₃,hL₃⟩ := bounded_scalar_ode_exists v₃ L C (2*Δ) (3*Δ) (X₂ (2*Δ)) (by linarith) hC h₃ hb₃
  let X₁₂ := joinSolution Δ X₁ X₂
  have hjoin₁ : X₁ Δ = X₂ Δ := hX₂.symm
  have hjoin₂ : X₁₂ (2*Δ) = X₃ (2*Δ) := by
    dsimp only [X₁₂]
    rw [joinSolution_eq_right Δ X₁ X₂ (2*Δ) (by linarith)]
    exact hX₃.symm
  have hL₁₂ := joinSolution_lipschitz 0 Δ (2*Δ) hΔ.le (by linarith) X₁ X₂ _ _ hL₁ hL₂ hjoin₁
  have hLf := joinSolution_lipschitz 0 (2*Δ) (3*Δ) (by linarith) (by linarith) X₁₂ X₃ _ _ hL₁₂ hL₃ hjoin₂
  have hright₁₂ := joinSolution_right_ode 0 Δ (2*Δ) X₁ X₂ (fun _ => v₁) (fun _ => v₂) hjoin₁
    (fun t ht => (hd₁ t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => (hd₂ t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
  have hright := joinSolution_right_ode 0 (2*Δ) (3*Δ) X₁₂ X₃
    (fun t => if t < Δ then v₁ else v₂) (fun _ => v₃) hjoin₂ hright₁₂
    (fun t ht => (hd₃ t ⟨ht.1,ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht))
  refine ⟨joinSolution (2*Δ) X₁₂ X₃,_,?_,hLf,?_⟩
  · simp only [joinSolution,if_pos hΔ,if_pos (show 0 < 2*Δ by linarith),X₁₂,hX₁]
  · intro t ht
    have hh := hright t ht
    have he : (if t < 2*Δ then (if t < Δ then v₁ else v₂) else v₃) =
        (if t < Δ then v₁ else if t < 2*Δ then v₂ else v₃) := by
      by_cases htd : t < Δ
      · simp [htd,show t < 2*Δ by linarith]
      · simp [htd]
    rwa [he] at hh

theorem three_stage_solution_approximation (Δ C x₀ δ ε : ℝ) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (v₁ v₂ v₃ : ℝ → ℝ) (L : ℝ≥0)
    (h₁ : LipschitzWith L v₁) (h₂ : LipschitzWith L v₂) (h₃ : LipschitzWith L v₃)
    (hb₁ : ∀ x, ‖v₁ x‖ ≤ C) (hb₂ : ∀ x, ‖v₂ x‖ ≤ C) (hb₃ : ∀ x, ‖v₃ x‖ ≤ C)
    (Q Q' : ℝ → ℝ) (hQ : ContinuousOn Q (Icc 0 (3*Δ)))
    (hQd : ∀ t ∈ Ico 0 (3*Δ), HasDerivWithinAt Q (Q' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 (3*Δ),
      dist (Q' t) ((if t < Δ then v₁ else if t < 2*Δ then v₂ else v₃) (Q t)) ≤ ε)
    (hinit : dist x₀ (Q 0) ≤ δ) :
    ∃ (X : ℝ → ℝ) (K : ℝ≥0), X 0 = x₀ ∧ LipschitzOnWith K X (Icc 0 (3*Δ)) ∧
      (∀ t ∈ Ico 0 (3*Δ), HasDerivWithinAt X
        ((if t < Δ then v₁ else if t < 2*Δ then v₂ else v₃) (X t)) (Ici t) t) ∧
      ∀ t ∈ Icc 0 (3*Δ), dist (X t) (Q t) ≤ gronwallBound δ L ε t := by
  obtain ⟨X,K,hX,hL,hd⟩ := three_stage_bounded_ode_exists Δ C x₀ hΔ hC v₁ v₂ v₃ L h₁ h₂ h₃ hb₁ hb₂ hb₃
  refine ⟨X,K,hX,hL,hd,?_⟩
  have hv : ∀ t : ℝ, LipschitzWith L (if t < Δ then v₁ else if t < 2*Δ then v₂ else v₃) := by
    intro t
    split
    · exact h₁
    · split <;> assumption
  have hh := dist_le_of_approx_trajectories_ODE
    (v := fun t => if t < Δ then v₁ else if t < 2*Δ then v₂ else v₃)
    (εf := 0) (εg := ε) hv hL.continuousOn hd (fun _ _ => by simp) hQ hQd hres
    (by simpa only [hX] using hinit)
  simpa only [zero_add,sub_zero] using hh

theorem gronwallBound_uniform_linear_error (L T : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ ε, 0 ≤ ε → ∀ t ∈ Icc 0 T, gronwallBound 0 L ε t ≤ B*ε := by
  let G := fun t => gronwallBound 0 L 1 t
  have hG : Continuous G := continuous_iff_continuousAt.mpr
    (fun t => (hasDerivAt_gronwallBound 0 L 1 t).continuousAt)
  obtain ⟨M,hM⟩ := isCompact_Icc.bddAbove_image hG.continuousOn
  refine ⟨max 1 M,lt_of_lt_of_le (by norm_num) (le_max_left _ _),?_⟩
  intro ε hε t ht
  have hb : G t ≤ max 1 M := (hM (mem_image_of_mem G ht)).trans (le_max_right _ _)
  have he : gronwallBound 0 L ε t = ε*G t := by
    unfold G gronwallBound
    split <;> ring
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb hε

structure LocalResponseModel (F : ℝ) (g : Response) where
  δ : ℝ
  M : ℝ
  Q : ℝ
  L : ℝ≥0
  H : ℝ → ℝ
  radius_positive : 0 < δ
  radius_lt_benchmark : δ < F
  bound_nonnegative : 0 ≤ M
  remainder_nonnegative : 0 ≤ Q
  lipschitz : LipschitzWith L H
  bounded : ∀ x, |H x| ≤ M
  actual : ∀ x ∈ Icc (F-δ) (F+δ), H x = g.impact x/x
  taylor : ∀ x ∈ Icc (F-δ) (F+δ),
    |H x-g.impact F/F-((F*deriv g.impact F-g.impact F)/F^2)*(x-F)| ≤ Q*(x-F)^2

theorem exists_local_response_model (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) : Nonempty (LocalResponseModel F g) := by
  obtain ⟨δ₁,M,L,H,hδ₁,hδF,hM,hL,hH,hactual⟩ := exists_bounded_response_extension F g hF hg
  obtain ⟨δ₂,Q,hδ₂,hQ,hTaylor⟩ := response_quotient_taylor_bound F g hF hg
  let δ := min δ₁ δ₂
  have hs : Icc (F-δ) (F+δ) ⊆ Icc (F-δ₁) (F+δ₁) := by
    intro x hx
    have hle : δ ≤ δ₁ := min_le_left _ _
    constructor <;> linarith [hx.1,hx.2]
  refine ⟨⟨δ,M,Q,L,H,lt_min hδ₁ hδ₂,(min_le_left _ _).trans_lt hδF,hM,hQ,hL,hH,
    fun x hx => hactual x (hs hx),?_⟩⟩
  intro x hx
  rw [hactual x (hs hx)]
  apply hTaylor
  rw [abs_le]
  have hle : δ ≤ δ₂ := min_le_right _ _
  constructor <;> linarith [hx.1,hx.2]

theorem continuousOn_compact_abs_bound (f : ℝ → ℝ) (s : Set ℝ) (hs : IsCompact s)
    (hf : ContinuousOn f s) : ∃ B : ℝ, 0 < B ∧ ∀ t ∈ s, |f t| ≤ B := by
  obtain ⟨M,hM⟩ := hs.bddAbove_image hf.abs
  exact ⟨max 1 M,lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    fun t ht => (hM (mem_image_of_mem _ ht)).trans (le_max_right _ _)⟩

theorem lipschitz_right_derivative_ae (f w : ℝ → ℝ) (a b : ℝ) (K : ℝ≥0)
    (hL : LipschitzOnWith K f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (w t) (Ici t) t) :
    ∀ᵐ t ∂volume, t ∈ Icc a b → HasDerivAt f (w t) t := by
  obtain ⟨g,hg,heq⟩ := hL.extend_real
  filter_upwards [hg.ae_differentiableAt_real,
    show ∀ᵐ t : ℝ ∂volume, t ≠ a by simp [ae_iff],
    show ∀ᵐ t : ℝ ∂volume, t ≠ b by simp [ae_iff]] with t ht hta htb hmem
  have hti : t ∈ Ioo a b := ⟨lt_of_le_of_ne hmem.1 hta.symm,lt_of_le_of_ne hmem.2 htb⟩
  have hevent : f =ᶠ[nhds t] g := by
    filter_upwards [Ioo_mem_nhds hti.1 hti.2] with s hs
    exact heq ⟨hs.1.le,hs.2.le⟩
  have hdf : DifferentiableAt ℝ f t := ht.congr_of_eventuallyEq hevent
  have hI := hdf.hasDerivAt.hasDerivWithinAt (s := Ici t) |>.derivWithin (uniqueDiffOn_Ici t t left_mem_Ici)
  have hR := (hd t ⟨hti.1.le,hti.2⟩).derivWithin (uniqueDiffOn_Ici t t left_mem_Ici)
  exact hdf.hasDerivAt.congr_deriv (hI.symm.trans hR)

theorem lipschitz_right_ode_primitive (f w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (K : ℝ≥0)
    (hL : LipschitzOnWith K f (Icc a b))
    (hd : ∀ t ∈ Ico a b, HasDerivWithinAt f (w t) (Ici t) t) :
    IntervalIntegrable w volume a b ∧ ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      f t-f s = ∫ u in s..t, w u := by
  have hae := lipschitz_right_derivative_ae f w a b K hL hd
  obtain ⟨hi,_⟩ := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hL hab
    (hae.mono (fun t ht hmem => ht ⟨hmem.1.le,hmem.2.le⟩))
  have hbase (t : ℝ) (ht : t ∈ Icc a b) : f t-f a = ∫ u in a..t, w u := by
    have hLt := hL.mono (show Icc a t ⊆ Icc a b from fun s hs => ⟨hs.1,hs.2.trans ht.2⟩)
    exact (lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hLt ht.1
      (hae.mono (fun x hx hmem => hx ⟨hmem.1.le,hmem.2.le.trans ht.2⟩))).2.symm
  refine ⟨hi,?_⟩
  intro s hs t ht
  have his : IntervalIntegrable w volume a s := hi.mono_set (by rw [uIcc_of_le hab];exact uIcc_subset_Icc (left_mem_Icc.mpr hab) hs)
  have hist : IntervalIntegrable w volume s t := hi.mono_set (by rw [uIcc_of_le hab];exact uIcc_subset_Icc hs ht)
  have hh := intervalIntegral.integral_add_adjacent_intervals his hist
  linarith [hbase s hs,hbase t ht]

theorem bounded_measurable_intervalIntegrable (w : ℝ → ℝ) (B : ℝ)
    (hm : Measurable w) (hb : ∀ t, ‖w t‖ ≤ B) (a b : ℝ) :
    IntervalIntegrable w volume a b := by
  apply (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume a b).mono_fun'
  · exact hm.aestronglyMeasurable.restrict
  · exact Filter.Eventually.of_forall hb

theorem exists_bounded_rate_stieltjes (w : ℝ → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hm : Measurable w) (hn : ∀ t, 0 ≤ w t) (hb : ∀ t, w t ≤ B) :
    ∃ G : StieltjesFunction, G 0 = 0 ∧
      (∀ t, G t = ∫ u in (0:ℝ)..t, w u) ∧ LipschitzWith ⟨B,hB⟩ G := by
  let P := fun t => ∫ u in (0:ℝ)..t, w u
  have hnorm : ∀ t, ‖w t‖ ≤ B := fun t => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hn t)] using hb t
  have hi := bounded_measurable_intervalIntegrable w B hm hnorm
  have hdiff (s t : ℝ) : P t-P s = ∫ u in s..t, w u := by
    have hh := intervalIntegral.integral_add_adjacent_intervals (hi 0 s) (hi s t)
    dsimp [P]
    linarith
  have hL : LipschitzWith ⟨B,hB⟩ P := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro s t
    rw [Real.dist_eq,hdiff t s,Real.dist_eq]
    exact intervalIntegral.norm_integral_le_of_norm_le_const (fun u _ => hnorm u)
  have hmono : Monotone P := by
    intro s t hst
    have hh := intervalIntegral.integral_nonneg_of_forall (μ := volume) hst hn
    rw [← hdiff s t] at hh
    linarith
  let G : StieltjesFunction := {
    toFun := P
    mono' := hmono
    right_continuous' := fun _ => hL.continuous.continuousAt.continuousWithinAt }
  exact ⟨G,by simp [G,P],fun _ => rfl,hL⟩

end MarketCrash
