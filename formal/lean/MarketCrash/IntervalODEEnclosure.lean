import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Tactic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MarketCrash.RationalIntervalChecker
import MarketCrash.LipschitzFTC

/-! Analytic facts required by the numerical enclosure. These do not yet
establish solution existence or 80k propagation.

Precise remaining D01 obligations (not mathematical impossibility claims):
1. Apply compensator_local_exists inductively to the exact checked step boxes,
   then paste the unique solutions across all six segment boundaries. Local
   existence and its noncircular bootstrap are proved below using a globally
   clamped field, Picard-Lindelof, and a real displacement bound.
2. Connect the proved scalar comparison to both endpoint flows at every step.
   Scalar flow order is proved below by crossing IVT and backward uniqueness;
   compensator_solution_order accepts the actual within-segment ODE directly.
3. Instantiate the proved segment_taylor_remainder and endpoint_flow_taylor_step
   on the endpoint solutions supplied by item 1. These theorems use actual
   interior derivatives and never cross a segment knot. The strip assumption
   in compensator_bootstrap_bounds is not itself a bootstrap proof.
4. Implement/replay the 80,000 step exact integer recurrence in Lean and
   prove every check by kernel reduction/reflection. The pinned JSON stores
   only six segment summaries and six knot boxes, not the intermediate
   integer states. RationalIntervalCheckerWorking proves arithmetic
   operations, not this full checker or its execution.
5. Construct the ten-asset physical path, directed gross-dollar controls,
   continuous shares and ledgers; prove closure, inventory, rolling bands,
   and integrated turnover against the certified solution. Only then may
   OriginalCertificate.actual_crisis_of_endpoint_bound be instantiated.

External verification: the unchanged Python generator's 80,000 checks and
verify_consistency both PASS in .validation311. The regenerated certificate
in build/formal/d01-reproduction is byte-identical to the pinned JSON,
SHA256 354c7797c1e25ebee143d04d11e23ec92cb93214b7333eed7fcd91dd0493c18f.
That external result is not a Lean soundness bridge or Proposition 7.6 proof. -/
noncomputable section
namespace MarketCrash
namespace OriginalCertificate

def compensatorField (u y : ℝ) : ℝ := -(2 / 5 : ℝ) * (y - 1) - 9 * u / y
def compensatorFt (du y : ℝ) : ℝ := -9 * du / y
def compensatorFy (u y : ℝ) : ℝ := -(2 / 5 : ℝ) + 9 * u / y ^ 2

theorem compensator_velocity_hasDerivAt (U Y : ℝ → ℝ) (t du : ℝ)
    (hU : HasDerivAt U du t)
    (hY : HasDerivAt Y (compensatorField (U t) (Y t)) t) (hy : Y t ≠ 0) :
    HasDerivAt (fun s => compensatorField (U s) (Y s))
      (compensatorFt du (Y t) + compensatorFy (U t) (Y t) * compensatorField (U t) (Y t)) t := by
  have hh := ((hY.sub_const 1).const_mul (-(2 / 5 : ℝ))).sub ((hU.const_mul 9).div hY hy)
  convert hh using 1
  dsimp [compensatorField, compensatorFt, compensatorFy]
  field_simp [hy]
  ring

theorem compensator_bootstrap_bounds (u du y : ℝ)
    (hu : |u| ≤ 107 / 1000) (hdu : |du| ≤ 41 / 1000)
    (hy : 7 / 10 ≤ y ∧ y ≤ 8 / 5) :
    |compensatorField u y| < 17 / 10 ∧
      |compensatorFt du y + compensatorFy u y * compensatorField u y| < 5 := by
  have hyp : 0 < y := by linarith [hy.1]
  have hyabs : |y - 1| ≤ 3 / 5 := abs_le.mpr (by constructor <;> linarith [hy.1, hy.2])
  have hsq : 49 / 100 ≤ y ^ 2 := by nlinarith [hy.1]
  have hu9 : |9 * u / y| ≤ 963 / 700 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9), abs_of_pos hyp]
    apply (div_le_iff₀ hyp).mpr
    nlinarith
  have hdu9 : |9 * du / y| ≤ 369 / 700 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9), abs_of_pos hyp]
    apply (div_le_iff₀ hyp).mpr
    nlinarith
  have hu92 : |9 * u / y ^ 2| ≤ 963 / 490 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9), abs_of_nonneg (sq_nonneg y)]
    apply (div_le_iff₀ (sq_pos_of_pos hyp)).mpr
    nlinarith
  have hf : |compensatorField u y| ≤ 1131 / 700 := by
    have hc : |-(2 / 5 : ℝ) * (y - 1)| ≤ 6 / 25 := by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
      linarith
    have hh := abs_add_le (-(2 / 5 : ℝ) * (y - 1)) (-(9 * u / y))
    simp only [abs_neg] at hh
    change |-(2 / 5 : ℝ) * (y - 1) + -(9 * u / y)| ≤ 1131 / 700
    linarith
  have hfy : |compensatorFy u y| ≤ 1159 / 490 := by
    have hh := abs_add_le (-(2 / 5 : ℝ)) (9 * u / y ^ 2)
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)] at hh
    dsimp [compensatorFy]
    linarith
  refine ⟨hf.trans_lt (by norm_num), ?_⟩
  have hprod := mul_le_mul hfy hf (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1159 / 490)
  have hh := abs_add_le (compensatorFt du y) (compensatorFy u y * compensatorField u y)
  rw [abs_mul] at hh
  have ht : |compensatorFt du y| ≤ 369 / 700 := by
    simpa only [compensatorFt, neg_mul, neg_div, abs_neg] using hdu9
  linarith

theorem compensator_second_derivative_on (U Y : ℝ → ℝ) (a b t du : ℝ)
    (ht : t ∈ Set.Ioo a b) (hU : HasDerivAt U du t)
    (hflow : ∀ s ∈ Set.Ioo a b, HasDerivAt Y (compensatorField (U s) (Y s)) s)
    (hy : Y t ≠ 0) :
    HasDerivAt (deriv Y)
      (compensatorFt du (Y t) + compensatorFy (U t) (Y t) * compensatorField (U t) (Y t)) t := by
  have hh := compensator_velocity_hasDerivAt U Y t du hU (hflow t ht) hy
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact (hflow s hs).deriv

theorem compensator_actual_second_derivative_bound (U Y : ℝ → ℝ) (a b t du : ℝ)
    (ht : t ∈ Set.Ioo a b) (hU : HasDerivAt U du t)
    (hflow : ∀ s ∈ Set.Ioo a b, HasDerivAt Y (compensatorField (U s) (Y s)) s)
    (hu : |U t| ≤ 107 / 1000) (hdu : |du| ≤ 41 / 1000)
    (hy : 7 / 10 ≤ Y t ∧ Y t ≤ 8 / 5) :
    |deriv (deriv Y) t| < 5 := by
  have hyp : Y t ≠ 0 := ne_of_gt (by linarith [hy.1])
  rw [(compensator_second_derivative_on U Y a b t du ht hU hflow hyp).deriv]
  exact (compensator_bootstrap_bounds (U t) du (Y t) hu hdu hy).2

/-- Second-order Taylor remainder proved from actual segment derivatives.
Only interior differentiability is used, so a step must not cross a knot. -/
theorem segment_taylor_remainder (Y V : ℝ → ℝ) (a b B : ℝ) (hab : a < b)
    (hY : ContinuousOn Y (Set.Icc a b)) (hV : ContinuousOn V (Set.Icc a b))
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (V t) t)
    (hdd : ∀ t ∈ Set.Ioo a b, HasDerivAt V (deriv V t) t)
    (hbound : ∀ t ∈ Set.Ioo a b, |deriv V t| ≤ B) :
    |Y b - (Y a + (b - a) * V a)| ≤ B * (b - a) ^ 2 / 2 := by
  let E := Y b - Y a - V a * (b - a)
  let K := E / (b - a) ^ 2
  let R := fun t => Y t - Y a - V a * (t - a) - K * (t - a) ^ 2
  let S := fun t => V t - V a - 2 * K * (t - a)
  have hR : ContinuousOn R (Set.Icc a b) := by dsimp [R]; fun_prop
  have hS : ContinuousOn S (Set.Icc a b) := by dsimp [S]; fun_prop
  have hRa : R a = 0 := by simp [R]
  have hRb : R b = 0 := by
    dsimp [R, K, E]
    field_simp [sub_ne_zero.mpr hab.ne']
  have hdR : ∀ t ∈ Set.Ioo a b, HasDerivAt R (S t) t := by
    intro t ht
    have hh := (((hd t ht).sub_const (Y a)).sub
      (((hasDerivAt_id t).sub_const a).const_mul (V a))).sub
      ((((hasDerivAt_id t).sub_const a).pow 2).const_mul K)
    convert hh using 1; dsimp [R, S]; ring
  obtain ⟨c, hc, hSc⟩ := exists_hasDerivAt_eq_zero hab hR (hRa.trans hRb.symm) hdR
  have hSa : S a = 0 := by simp [S]
  have hSc' : S a = S c := hSa.trans hSc.symm
  have hdS : ∀ t ∈ Set.Ioo a c, HasDerivAt S (deriv V t - 2 * K) t := by
    intro t ht
    have hh := ((hdd t ⟨ht.1, ht.2.trans hc.2⟩).sub_const (V a)).sub
      (((hasDerivAt_id t).sub_const a).const_mul (2 * K))
    simpa only [S, mul_one] using hh
  obtain ⟨d, hdmem, hd0⟩ := exists_hasDerivAt_eq_zero hc.1
    (hS.mono (fun _ ht => ⟨ht.1, ht.2.trans hc.2.le⟩)) hSc' hdS
  have hKd : deriv V d = 2 * K := by linarith
  have heq : Y b - (Y a + (b - a) * V a) = deriv V d * (b - a) ^ 2 / 2 := by
    rw [hKd]
    dsimp [K, E]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  rw [heq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg (b - a))]
  norm_num
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (hbound d ⟨hdmem.1, hdmem.2.trans hc.2⟩) (sq_nonneg _)) (by norm_num)

def eulerTaylorBox (initial slope : RationalInterval.Box) (h B : ℚ) : RationalInterval.Box :=
  RationalInterval.add
    (RationalInterval.add initial (RationalInterval.mul (RationalInterval.point h) slope))
    ⟨-B * h ^ 2 / 2, B * h ^ 2 / 2⟩

/-- Arithmetic end of the sound Taylor step, using actual segment calculus. -/
theorem outward_taylor_euler_step (Y V : ℝ → ℝ) (a : ℝ) (h B : ℚ)
    (hh : 0 < h) (initial slope : RationalInterval.Box) (Q : ℕ) (hQ : 0 < Q)
    (hY : ContinuousOn Y (Set.Icc a (a + h))) (hV : ContinuousOn V (Set.Icc a (a + h)))
    (hd : ∀ t ∈ Set.Ioo a (a + h), HasDerivAt Y (V t) t)
    (hdd : ∀ t ∈ Set.Ioo a (a + h), HasDerivAt V (deriv V t) t)
    (hbound : ∀ t ∈ Set.Ioo a (a + h), |deriv V t| ≤ B)
    (hinit : RationalInterval.Contains initial (Y a))
    (hslope : RationalInterval.Contains slope (V a)) :
    RationalInterval.Contains (RationalInterval.roundOut Q (eulerTaylorBox initial slope h B))
      (Y (a + h)) := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have ht := segment_taylor_remainder Y V a (a + h) B (by linarith) hY hV hd hdd hbound
  simp only [add_sub_cancel_left] at ht
  have hc := RationalInterval.add_sound hinit
    (RationalInterval.mul_sound (RationalInterval.point_sound h) hslope)
  have he : RationalInterval.Contains
      ⟨-B * h ^ 2 / 2, B * h ^ 2 / 2⟩ (Y (a + h) - (Y a + (h : ℝ) * V a)) := by
    dsimp [RationalInterval.Contains]
    push_cast
    constructor <;> linarith [abs_le.mp ht]
  have hout := RationalInterval.roundOut_sound Q hQ (RationalInterval.add_sound hc he)
  convert hout using 1; dsimp [eulerTaylorBox]; ring

/-- Scalar solutions cannot cross before leaving their actual Lipschitz strip.
This uses uniqueness backwards from a crossing, not monotonicity of an Euler map. -/
theorem scalar_flow_strict_order (v : ℝ → ℝ → ℝ) (s : ℝ → Set ℝ)
    (K : NNReal) (f g : ℝ → ℝ) (a b : ℝ) (_hab : a ≤ b)
    (hv : ∀ t ∈ Set.Ioc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hf' : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt f (v t (f t)) (Set.Iic t) t)
    (hg' : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt g (v t (g t)) (Set.Iic t) t)
    (hfs : ∀ t ∈ Set.Ioc a b, f t ∈ s t)
    (hgs : ∀ t ∈ Set.Ioc a b, g t ∈ s t)
    (hinit : f a < g a) : ∀ t ∈ Set.Icc a b, f t < g t := by
  intro t ht
  by_contra hn
  have hnon : g t ≤ f t := le_of_not_gt hn
  have hc : ContinuousOn (fun u => f u - g u) (Set.Icc a t) :=
    (hf.sub hg).mono (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩)
  obtain ⟨c, hc, heq⟩ := intermediate_value_Icc ht.1 hc
    (show (0 : ℝ) ∈ Set.Icc (f a - g a) (f t - g t) by
      constructor <;> linarith)
  have heq' : f c = g c := sub_eq_zero.mp heq
  have hsub : Set.Icc a c ⊆ Set.Icc a b :=
    fun u hu => ⟨hu.1, hu.2.trans (hc.2.trans ht.2)⟩
  have hoc : Set.Ioc a c ⊆ Set.Ioc a b :=
    fun u hu => ⟨hu.1, hu.2.trans (hc.2.trans ht.2)⟩
  have hu := ODE_solution_unique_of_mem_Icc_left
    (fun u hu => hv u (hoc hu)) (hf.mono hsub)
    (fun u hu => hf' u (hoc hu)) (fun u hu => hfs u (hoc hu))
    (hg.mono hsub) (fun u hu => hg' u (hoc hu))
    (fun u hu => hgs u (hoc hu)) heq'
  have := hu (show a ∈ Set.Icc a c from ⟨le_rfl, hc.1⟩)
  linarith

/-- Weak scalar order also covers a singleton initial box. -/
theorem scalar_flow_order (v : ℝ → ℝ → ℝ) (s : ℝ → Set ℝ)
    (K : NNReal) (f g : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hv : ∀ t ∈ Set.Icc a b, LipschitzOnWith K (v t) (s t))
    (hf : ContinuousOn f (Set.Icc a b)) (hg : ContinuousOn g (Set.Icc a b))
    (hfL : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt f (v t (f t)) (Set.Iic t) t)
    (hgL : ∀ t ∈ Set.Ioc a b, HasDerivWithinAt g (v t (g t)) (Set.Iic t) t)
    (hfR : ∀ t ∈ Set.Ico a b, HasDerivWithinAt f (v t (f t)) (Set.Ici t) t)
    (hgR : ∀ t ∈ Set.Ico a b, HasDerivWithinAt g (v t (g t)) (Set.Ici t) t)
    (hfs : ∀ t ∈ Set.Icc a b, f t ∈ s t)
    (hgs : ∀ t ∈ Set.Icc a b, g t ∈ s t)
    (hinit : f a ≤ g a) : ∀ t ∈ Set.Icc a b, f t ≤ g t := by
  rcases hinit.eq_or_lt with heq | hlt
  · have hu := ODE_solution_unique_of_mem_Icc_right
      (fun t ht => hv t ⟨ht.1, ht.2.le⟩) hf hfR
      (fun t ht => hfs t ⟨ht.1, ht.2.le⟩) hg hgR
      (fun t ht => hgs t ⟨ht.1, ht.2.le⟩) heq
    intro t ht
    exact (hu ht).le
  · intro t ht
    exact (scalar_flow_strict_order v s K f g a b hab
      (fun t ht => hv t ⟨ht.1.le, ht.2⟩) hf hg hfL hgL
      (fun t ht => hfs t ⟨ht.1.le, ht.2⟩)
      (fun t ht => hgs t ⟨ht.1.le, ht.2⟩) hlt t ht).le

def endpointEulerTaylorBox (initial lowSlope highSlope : RationalInterval.Box)
    (h B : ℚ) : RationalInterval.Box :=
  ⟨initial.lo + h * lowSlope.lo - B * h ^ 2 / 2,
   initial.hi + h * highSlope.hi + B * h ^ 2 / 2⟩

/-- The sharper update used by the certificate: Taylor is applied separately to
the two endpoint flows. The supplied sandwich is obtained from `scalar_flow_order`;
it is not an assumed monotonicity of the discrete update. -/
theorem endpoint_flow_taylor_step (L LV U UV : ℝ → ℝ) (a y : ℝ) (h B : ℚ)
    (hh : 0 < h) (initial lowSlope highSlope : RationalInterval.Box)
    (Q : ℕ) (hQ : 0 < Q)
    (hL : ContinuousOn L (Set.Icc a (a + h)))
    (hLV : ContinuousOn LV (Set.Icc a (a + h)))
    (hU : ContinuousOn U (Set.Icc a (a + h)))
    (hUV : ContinuousOn UV (Set.Icc a (a + h)))
    (hdL : ∀ t ∈ Set.Ioo a (a + h), HasDerivAt L (LV t) t)
    (hddL : ∀ t ∈ Set.Ioo a (a + h), HasDerivAt LV (deriv LV t) t)
    (hdU : ∀ t ∈ Set.Ioo a (a + h), HasDerivAt U (UV t) t)
    (hddU : ∀ t ∈ Set.Ioo a (a + h), HasDerivAt UV (deriv UV t) t)
    (hBL : ∀ t ∈ Set.Ioo a (a + h), |deriv LV t| ≤ B)
    (hBU : ∀ t ∈ Set.Ioo a (a + h), |deriv UV t| ≤ B)
    (hLa : L a = initial.lo) (hUa : U a = initial.hi)
    (hLs : RationalInterval.Contains lowSlope (LV a))
    (hUs : RationalInterval.Contains highSlope (UV a))
    (hbetween : L (a + h) ≤ y ∧ y ≤ U (a + h)) :
    RationalInterval.Contains
      (RationalInterval.roundOut Q (endpointEulerTaylorBox initial lowSlope highSlope h B)) y := by
  have hhr : (0 : ℝ) < h := by exact_mod_cast hh
  have hl := segment_taylor_remainder L LV a (a + h) B (by linarith)
    hL hLV hdL hddL hBL
  have hu := segment_taylor_remainder U UV a (a + h) B (by linarith)
    hU hUV hdU hddU hBU
  simp only [add_sub_cancel_left] at hl hu
  have hl' := (abs_le.mp hl).1
  have hu' := (abs_le.mp hu).2
  apply RationalInterval.roundOut_sound Q hQ
  dsimp [RationalInterval.Contains, endpointEulerTaylorBox] at *
  push_cast
  constructor
  · have hs := mul_le_mul_of_nonneg_left hLs.1 hhr.le
    linarith [hbetween.1]
  · have hs := mul_le_mul_of_nonneg_left hUs.2 hhr.le
    linarith [hbetween.2]

/-- Actual price ODE implies the compensator's dollar-rate identity. -/
theorem actual_compensator_dollars (U Y : ℝ → ℝ) (t : ℝ)
    (hy : Y t ≠ 0)
    (hode : HasDerivAt Y (compensatorField (U t) (Y t)) t) :
    Y t * (deriv Y t + (2 / 5 : ℝ) * (Y t - 1)) = -9 * U t := by
  rw [hode.deriv]
  dsimp [compensatorField]
  field_simp; ring

/-- Uniform state Lipschitz constant on the actual positive bootstrap strip. -/
theorem compensator_state_lipschitz (u : ℝ) (hu : |u| ≤ 107 / 1000) :
    LipschitzOnWith 3 (compensatorField u) (Set.Icc (7 / 10 : ℝ) (8 / 5)) := by
  have hd (y : ℝ) (hy : y ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) :
      HasDerivAt (compensatorField u) (compensatorFy u y) y := by
    have hyn : y ≠ 0 := by linarith [hy.1]
    have hh := (((hasDerivAt_id y).sub_const 1).const_mul (-(2 / 5 : ℝ))).sub
      ((hasDerivAt_const y (9 * u)).div (hasDerivAt_id y) hyn)
    convert hh using 1
    dsimp [compensatorField, compensatorFy]
    field_simp [hyn]; ring
  apply (convex_Icc (7 / 10 : ℝ) (8 / 5)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun y hy => (hd y hy).hasDerivWithinAt)
  intro y hy
  have hyp : 0 < y := by linarith [hy.1]
  have hsq : 49 / 100 ≤ y ^ 2 := by nlinarith [hy.1]
  have hterm : |9 * u / y ^ 2| ≤ 963 / 490 := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9),
      abs_of_nonneg (sq_nonneg y)]
    apply (div_le_iff₀ (sq_pos_of_pos hyp)).mpr
    nlinarith
  have hh := abs_add_le (-(2 / 5 : ℝ)) (9 * u / y ^ 2)
  rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)] at hh
  change ‖compensatorFy u y‖₊ ≤ (3 : NNReal)
  rw [← NNReal.coe_le_coe]
  change |compensatorFy u y| ≤ (3 : ℝ)
  dsimp [compensatorFy]
  linarith

def positiveStripClamp (y : ℝ) : ℝ := max (7 / 10) (min y (8 / 5))

theorem positiveStripClamp_mem (y : ℝ) :
    positiveStripClamp y ∈ Set.Icc (7 / 10 : ℝ) (8 / 5) := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_right _ _)

theorem positiveStripClamp_eq (y : ℝ) (hy : y ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) :
    positiveStripClamp y = y := by
  simp [positiveStripClamp, min_eq_left hy.2, max_eq_right hy.1]

theorem positiveStripClamp_lipschitz : LipschitzWith 1 positiveStripClamp := by
  have hc : LipschitzWith 0 (fun _ : ℝ => (7 / 10 : ℝ)) := LipschitzWith.const _
  have hd : LipschitzWith 0 (fun _ : ℝ => (8 / 5 : ℝ)) := LipschitzWith.const _
  simpa [positiveStripClamp] using hc.max (LipschitzWith.id.min hd)

theorem clamped_compensator_lipschitz (u : ℝ) (hu : |u| ≤ 107 / 1000) :
    LipschitzWith 3 (fun y => compensatorField u (positiveStripClamp y)) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hf := (compensator_state_lipschitz u hu).dist_le_mul
    (positiveStripClamp x) (positiveStripClamp_mem x)
    (positiveStripClamp y) (positiveStripClamp_mem y)
  have hc := positiveStripClamp_lipschitz.dist_le_mul x y
  norm_num at hc ⊢
  exact hf.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

/-- Noncircular local bootstrap. Solve a globally clamped field first; its
global velocity bound proves the actual solution stays in the positive strip,
where the clamp disappears. No assumed invariant strip or endpoint enclosure. -/
theorem compensator_local_exists (U : ℝ → ℝ) (a h y₀ : ℝ) (hh : 0 < h)
    (hU : ContinuousOn U (Set.Icc a (a + h)))
    (hu : ∀ t ∈ Set.Icc a (a + h), |U t| ≤ 107 / 1000)
    (hlower : 7 / 10 ≤ y₀ - (17 / 10) * h)
    (hupper : y₀ + (17 / 10) * h ≤ 8 / 5) :
    ∃ Y : ℝ → ℝ, Y a = y₀ ∧
      (∀ t ∈ Set.Icc a (a + h), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ t ∈ Set.Icc a (a + h),
        HasDerivWithinAt Y (compensatorField (U t) (Y t)) (Set.Icc a (a + h)) t) ∧
      (∀ t ∈ Set.Icc a (a + h), |Y t - y₀| ≤ (17 / 10) * (t - a)) := by
  let v := fun t y => compensatorField (U t) (positiveStripClamp y)
  have hb : ∀ t ∈ Set.Icc a (a + h), ∀ y : ℝ, |v t y| ≤ 17 / 10 := by
    intro t ht y
    exact (compensator_bootstrap_bounds (U t) 0 (positiveStripClamp y)
      (hu t ht) (by norm_num) (positiveStripClamp_mem y)).1.le
  have hp : IsPicardLindelof v a a (a + h) y₀ 3 ((17 / 10) * h) (17 / 10) := by
    constructor
    · exact ⟨le_rfl, by linarith⟩
    · positivity
    · intro t ht
      exact (clamped_compensator_lipschitz (U t) (hu t ht)).lipschitzOnWith
    · intro y _
      dsimp [v, compensatorField]
      fun_prop
    · intro t ht y _
      simpa only [Real.norm_eq_abs] using hb t ht y
    · rw [sub_self, add_sub_cancel_left, max_eq_left hh.le]
  obtain ⟨Y, hYa, hd⟩ := hp.exists_forall_hasDerivWithinAt_Icc_eq y₀
  have hmove : ∀ t ∈ Set.Icc a (a + h), |Y t - y₀| ≤ (17 / 10) * (t - a) := by
    intro t ht
    have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd
      (fun s hs => by simpa only [Real.norm_eq_abs] using hb s hs (Y s))
      (convex_Icc a (a + h)) (show a ∈ Set.Icc a (a + h) from ⟨le_rfl, by linarith⟩) ht
    simpa only [Real.norm_eq_abs, hYa, abs_of_nonneg (sub_nonneg.mpr ht.1)] using hm
  have hstrip : ∀ t ∈ Set.Icc a (a + h), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5) := by
    intro t ht
    have hm := abs_le.mp (hmove t ht)
    constructor <;> linarith [ht.2]
  refine ⟨Y, hYa, hstrip, ?_, hmove⟩
  intro t ht
  simpa only [v, positiveStripClamp_eq (Y t) (hstrip t ht)] using hd t ht

theorem segment_derivative_left (Y W : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y (W t) (Set.Icc a b) t) :
    ∀ t ∈ Set.Ioc a b, HasDerivWithinAt Y (W t) (Set.Iic t) t := by
  intro t ht
  apply (hd t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin
  exact Icc_mem_nhdsLE_of_mem ht

theorem segment_derivative_right (Y W : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y (W t) (Set.Icc a b) t) :
    ∀ t ∈ Set.Ico a b, HasDerivWithinAt Y (W t) (Set.Ici t) t := by
  intro t ht
  apply (hd t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
  exact Icc_mem_nhdsGE_of_mem ht

/-- Original-field comparison directly usable for the endpoint solutions
constructed by `compensator_local_exists`, including degenerate initial boxes. -/
theorem compensator_solution_order (U Y Z : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hu : ∀ t ∈ Set.Icc a b, |U t| ≤ 107 / 1000)
    (hY : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt Y (compensatorField (U t) (Y t)) (Set.Icc a b) t)
    (hZ : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt Z (compensatorField (U t) (Z t)) (Set.Icc a b) t)
    (hYs : ∀ t ∈ Set.Icc a b, Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5))
    (hZs : ∀ t ∈ Set.Icc a b, Z t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5))
    (hinit : Y a ≤ Z a) : ∀ t ∈ Set.Icc a b, Y t ≤ Z t := by
  apply scalar_flow_order (fun t y => compensatorField (U t) y)
    (fun _ => Set.Icc (7 / 10 : ℝ) (8 / 5)) 3 Y Z a b hab
    (fun t ht => compensator_state_lipschitz (U t) (hu t ht))
    (fun t ht => (hY t ht).continuousWithinAt)
    (fun t ht => (hZ t ht).continuousWithinAt)
    (segment_derivative_left Y _ a b hY) (segment_derivative_left Z _ a b hZ)
    (segment_derivative_right Y _ a b hY) (segment_derivative_right Z _ a b hZ)
    hYs hZs hinit

/-- Economic conservation follows from the actual ODE almost everywhere;
segment knots may be omitted and no derivative at a knot is postulated. -/
theorem compensator_dollar_integral (U Y : ℝ → ℝ) (a b : ℝ)
    (hflow : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
      Y t ≠ 0 ∧ HasDerivAt Y (compensatorField (U t) (Y t)) t) :
    (∫ t in a..b, Y t * (deriv Y t + (2 / 5 : ℝ) * (Y t - 1))) =
      -9 * (∫ t in a..b, U t) := by
  calc
    _ = ∫ t in a..b, (-9 : ℝ) * U t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hflow] with t ht hmem
      exact actual_compensator_dollars U Y t (ht hmem).1 (ht hmem).2
    _ = _ := intervalIntegral.integral_const_mul _ _

theorem compensator_dollar_closure_of_target (U Y : ℝ → ℝ) (a b : ℝ)
    (hflow : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc a b →
      Y t ≠ 0 ∧ HasDerivAt Y (compensatorField (U t) (Y t)) t)
    (hclosure : (∫ t in a..b, U t) = 0) :
    (∫ t in a..b, Y t * (deriv Y t + (2 / 5 : ℝ) * (Y t - 1))) = 0 := by
  rw [compensator_dollar_integral U Y a b hflow, hclosure, mul_zero]

/-- Exact segment-dependent second-derivative majorant used by the checker,
rather than replacing every segment by the coarser constant five. -/
theorem compensator_segment_second_bound (u du y M D : ℝ)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hu : |u| ≤ M) (hdu : |du| ≤ D)
    (hy : 7 / 10 ≤ y ∧ y ≤ 8 / 5) :
    |compensatorFt du y + compensatorFy u y * compensatorField u y| ≤
      9 * D / (7 / 10) + (2 / 5 + 9 * M / (49 / 100)) *
        (6 / 25 + 9 * M / (7 / 10)) := by
  have hyp : 0 < y := by linarith [hy.1]
  have hsq : 49 / 100 ≤ y ^ 2 := by nlinarith [hy.1]
  have hr (z A : ℝ) (hA : 0 ≤ A) (hz : |z| ≤ A) :
      |9 * z / y| ≤ 9 * A / (7 / 10) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9), abs_of_pos hyp]
    apply (div_le_iff₀ hyp).mpr
    nlinarith [mul_nonneg hA (sub_nonneg.mpr hy.1)]
  have hterm : |9 * u / y ^ 2| ≤ 9 * M / (49 / 100) := by
    rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 9),
      abs_of_nonneg (sq_nonneg y)]
    apply (div_le_iff₀ (sq_pos_of_pos hyp)).mpr
    nlinarith [mul_nonneg hM (sub_nonneg.mpr hsq)]
  have hFy : |compensatorFy u y| ≤ 2 / 5 + 9 * M / (49 / 100) := by
    have hh := abs_add_le (-(2 / 5 : ℝ)) (9 * u / y ^ 2)
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)] at hh
    dsimp [compensatorFy]
    linarith
  have hF : |compensatorField u y| ≤ 6 / 25 + 9 * M / (7 / 10) := by
    have hyabs : |y - 1| ≤ 3 / 5 := abs_le.mpr (by constructor <;> linarith [hy.1, hy.2])
    have hc : |-(2 / 5 : ℝ) * (y - 1)| ≤ 6 / 25 := by
      rw [abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 2 / 5)]
      linarith
    have hh := abs_sub (-(2 / 5 : ℝ) * (y - 1)) (9 * u / y)
    dsimp [compensatorField]
    linarith [hr u M hM hu]
  have hFt : |compensatorFt du y| ≤ 9 * D / (7 / 10) := by
    simpa only [compensatorFt, neg_mul, neg_div, abs_neg] using hr du D hD hdu
  have hh := abs_add_le (compensatorFt du y) (compensatorFy u y * compensatorField u y)
  rw [abs_mul] at hh
  have hm := mul_le_mul hFy hF (abs_nonneg _) (by positivity)
  linarith

/-- Full analytic Taylor bridge from the actual within-segment ODE and the
actual forcing derivative; no C2 trajectory field is assumed. -/
theorem compensator_actual_taylor (U dU Y : ℝ → ℝ) (a b M D : ℝ) (hab : a < b)
    (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hU : ContinuousOn U (Set.Icc a b))
    (hdU : ∀ t ∈ Set.Ioo a b, HasDerivAt U (dU t) t)
    (hY : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt Y (compensatorField (U t) (Y t)) (Set.Icc a b) t)
    (hu : ∀ t ∈ Set.Ioo a b, |U t| ≤ M)
    (hdu : ∀ t ∈ Set.Ioo a b, |dU t| ≤ D)
    (hstrip : ∀ t ∈ Set.Icc a b, Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) :
    |Y b - (Y a + (b - a) * compensatorField (U a) (Y a))| ≤
      (9 * D / (7 / 10) + (2 / 5 + 9 * M / (49 / 100)) *
        (6 / 25 + 9 * M / (7 / 10))) * (b - a) ^ 2 / 2 := by
  let V := fun t => compensatorField (U t) (Y t)
  have hyc : ContinuousOn Y (Set.Icc a b) := fun t ht => (hY t ht).continuousWithinAt
  have hyn (t : ℝ) (ht : t ∈ Set.Icc a b) : Y t ≠ 0 := by
    have hh := (hstrip t ht).1
    linarith
  have hvc : ContinuousOn V (Set.Icc a b) := by
    exact (continuousOn_const.mul (hyc.sub continuousOn_const)).sub
      ((continuousOn_const.mul hU).div hyc hyn)
  have hdY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (V t) t := by
    intro t ht
    exact (hY t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hdV (t : ℝ) (ht : t ∈ Set.Ioo a b) : HasDerivAt V
      (compensatorFt (dU t) (Y t) + compensatorFy (U t) (Y t) *
        compensatorField (U t) (Y t)) t :=
    compensator_velocity_hasDerivAt U Y t (dU t) (hdU t ht) (hdY t ht)
      (hyn t ⟨ht.1.le, ht.2.le⟩)
  apply segment_taylor_remainder Y V a b _ hab hyc hvc hdY
  · intro t ht
    rw [(hdV t ht).deriv]
    exact hdV t ht
  · intro t ht
    rw [(hdV t ht).deriv]
    exact compensator_segment_second_bound (U t) (dU t) (Y t) M D hM hD
      (hu t ht) (hdu t ht) (hstrip t ⟨ht.1.le, ht.2.le⟩)

def joinSolutions (f g : ℝ → ℝ) (b : ℝ) : ℝ → ℝ :=
  fun t => if t ≤ b then f t else g t

/-- Endpoint-matched actual solution pieces preserve a common Lipschitz
bound when pasted; no smoothness at the knot is asserted. -/
theorem joinSolutions_lipschitz (f g : ℝ → ℝ) (a b c : ℝ) (K : NNReal)
    (hab : a ≤ b) (hbc : b ≤ c)
    (hf : LipschitzOnWith K f (Set.Icc a b))
    (hg : LipschitzOnWith K g (Set.Icc b c)) (heq : f b = g b) :
    LipschitzOnWith K (joinSolutions f g b) (Set.Icc a c) := by
  have bound (x y : ℝ) (hx : x ∈ Set.Icc a c) (hy : y ∈ Set.Icc a c) (hxy : x ≤ y) :
      |joinSolutions f g b y - joinSolutions f g b x| ≤ (K : ℝ) * (y - x) := by
    by_cases hyb : y ≤ b
    · have hxb := hxy.trans hyb
      simpa only [joinSolutions, if_pos hyb, if_pos hxb, Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr hxy)] using
        hf.dist_le_mul y ⟨hy.1, hyb⟩ x ⟨hx.1, hxb⟩
    · have hby : b < y := lt_of_not_ge hyb
      by_cases hxb : x ≤ b
      · have hfd := hf.dist_le_mul b ⟨hab, le_rfl⟩ x ⟨hx.1, hxb⟩
        have hgd := hg.dist_le_mul y ⟨hby.le, hy.2⟩ b ⟨le_rfl, hbc⟩
        simp only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxb),
          abs_of_nonneg (sub_nonneg.mpr hby.le)] at hfd hgd
        have ha := abs_add_le (g y - g b) (f b - f x)
        rw [heq] at ha hfd
        simp only [sub_add_sub_cancel] at ha
        simp only [joinSolutions, if_neg hyb, if_pos hxb]
        linarith
      · have hbx : b < x := lt_of_not_ge hxb
        simpa only [joinSolutions, if_neg hyb, if_neg hxb, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr hxy)] using
          hg.dist_le_mul y ⟨hby.le, hy.2⟩ x ⟨hbx.le, hx.2⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  by_cases hxy : x ≤ y
  · rw [Real.dist_eq, Real.dist_eq, abs_sub_comm x y,
      abs_of_nonneg (sub_nonneg.mpr hxy), abs_sub_comm (joinSolutions f g b x) (joinSolutions f g b y)]
    exact bound x y hx hy hxy
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hyx)] using bound y x hy hx hyx

theorem compensator_solution_lipschitz (U Y : ℝ → ℝ) (a b : ℝ)
    (hu : ∀ t ∈ Set.Icc a b, |U t| ≤ 107 / 1000)
    (hY : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt Y (compensatorField (U t) (Y t)) (Set.Icc a b) t)
    (hstrip : ∀ t ∈ Set.Icc a b, Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) :
    LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc a b) := by
  apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hY
  intro t ht
  rw [← NNReal.coe_le_coe]
  change |compensatorField (U t) (Y t)| ≤ (17 / 10 : ℝ)
  exact (compensator_bootstrap_bounds (U t) 0 (Y t) (hu t ht)
    (by norm_num) (hstrip t ht)).1.le

theorem joinSolutions_hasDerivAt (f g : ℝ → ℝ) (b t df dg : ℝ) (hne : t ≠ b)
    (hf : t < b → HasDerivAt f df t) (hg : b < t → HasDerivAt g dg t) :
    HasDerivAt (joinSolutions f g b) (if t ≤ b then df else dg) t := by
  rcases lt_or_gt_of_ne hne with htb | hbt
  · rw [if_pos htb.le]
    apply (hf htb).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds htb] with s hs
    exact if_pos hs.le
  · rw [if_neg (not_le.mpr hbt)]
    apply (hg hbt).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hbt] with s hs
    exact if_neg (not_le.mpr hs)

theorem joinSolutions_ae_ode (f g : ℝ → ℝ) (v : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hf : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo a b → HasDerivAt f (v t (f t)) t)
    (hg : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo b c → HasDerivAt g (v t (g t)) t) :
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo a c →
      HasDerivAt (joinSolutions f g b) (v t (joinSolutions f g b t)) t := by
  have hne : ∀ᵐ t : ℝ ∂MeasureTheory.volume, t ≠ b := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne, hf, hg] with t ht hft hgt hmem
  have hd := joinSolutions_hasDerivAt f g b t (v t (f t)) (v t (g t)) ht
    (fun htb => hft ⟨hmem.1, htb⟩) (fun hbt => hgt ⟨hbt, hmem.2⟩)
  by_cases htb : t ≤ b
  · simpa only [joinSolutions, if_pos htb] using hd
  · simpa only [joinSolutions, if_neg htb] using hd

/-- True physical price primitive follows from the pasted Lipschitz path and
its actual a.e. ODE. No FTC or integral representation is an input. -/
theorem compensator_physical_price_primitive (U Y : ℝ → ℝ) (a b : ℝ) (C : NNReal)
    (hab : a ≤ b) (hY : LipschitzOnWith C Y (Set.Icc a b))
    (hode : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo a b →
      HasDerivAt Y (compensatorField (U t) (Y t)) t) :
    IntervalIntegrable (fun t => -9 * U t / Y t) MeasureTheory.volume a b ∧
    Y b - Y a = (∫ t in a..b, -(2 / 5 : ℝ) * (Y t - 1)) +
      (∫ t in a..b, -9 * U t / Y t) := by
  obtain ⟨hi, he⟩ := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hY hab hode
  have hr : IntervalIntegrable (fun t => -(2 / 5 : ℝ) * (Y t - 1))
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact continuousOn_const.mul (hY.continuousOn.sub continuousOn_const)
  have ht : IntervalIntegrable (fun t => -9 * U t / Y t) MeasureTheory.volume a b := by
    convert hi.sub hr using 1
    funext t
    dsimp [compensatorField]
    ring
  refine ⟨ht, ?_⟩
  rw [← he, ← intervalIntegral.integral_add hr ht]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [compensatorField]
  ring

theorem compensator_physical_price_primitive_on (U Y : ℝ → ℝ) (a b s t : ℝ)
    (C : NNReal) (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (hY : LipschitzOnWith C Y (Set.Icc a b))
    (hode : ∀ᵐ u ∂MeasureTheory.volume, u ∈ Set.Ioo a b →
      HasDerivAt Y (compensatorField (U u) (Y u)) u) :
    IntervalIntegrable (fun u => -9 * U u / Y u) MeasureTheory.volume s t ∧
    Y t - Y s = (∫ u in s..t, -(2 / 5 : ℝ) * (Y u - 1)) +
      (∫ u in s..t, -9 * U u / Y u) := by
  apply compensator_physical_price_primitive U Y s t C hst
  · exact hY.mono (fun u hu => ⟨hs.1.trans hu.1, hu.2.trans ht.2⟩)
  · filter_upwards [hode] with u hu hmem
    exact hu ⟨hs.1.trans_lt hmem.1, hmem.2.trans_le ht.2⟩

/-- One complete analytic/checker step: actual positive solutions are built
first, endpoint flows are compared, true Taylor bounds are applied, and the
integer update encloses the actual endpoint. No ODE solution is an input. -/
theorem validated_compensator_step (U dU : ℝ → ℝ) (a y₀ M D : ℝ)
    (s : RationalInterval.CertificateReplay.IntegerReplay.Segment)
    (j : ℕ) (st : RationalInterval.CertificateReplay.IntegerReplay.State)
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hMcoarse : M ≤ 107 / 1000)
    (hU : ContinuousOn U (Set.Icc a (a + 1 / 2000)))
    (hdU : ∀ t ∈ Set.Ioo a (a + 1 / 2000), HasDerivAt U (dU t) t)
    (hu : ∀ t ∈ Set.Icc a (a + 1 / 2000), |U t| ≤ M)
    (hdu : ∀ t ∈ Set.Ioo a (a + 1 / 2000), |dU t| ≤ D)
    (hinit : RationalInterval.Contains
      (RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure) y₀)
    (hmargin : (73 / 100 : ℝ) ≤
      (RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure).lo ∧
      ((RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure).hi : ℝ) ≤ 157 / 100)
    (hEvalL : RationalInterval.Contains
      (RationalInterval.CertificateReplay.IntegerReplay.view
        (RationalInterval.CertificateReplay.IntegerReplay.field s j
          ⟨st.enclosure.lo, st.enclosure.lo⟩))
      (compensatorField (U a)
        (RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure).lo))
    (hEvalU : RationalInterval.Contains
      (RationalInterval.CertificateReplay.IntegerReplay.view
        (RationalInterval.CertificateReplay.IntegerReplay.field s j
          ⟨st.enclosure.hi, st.enclosure.hi⟩))
      (compensatorField (U a)
        (RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure).hi))
    (hError : RationalInterval.Contains
      (RationalInterval.CertificateReplay.IntegerReplay.view s.error)
      ((9 * D / (7 / 10) + (2 / 5 + 9 * M / (49 / 100)) *
        (6 / 25 + 9 * M / (7 / 10))) * (1 / 2000 : ℝ) ^ 2 / 2)) :
    ∃ Y : ℝ → ℝ, Y a = y₀ ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc a (a + 1 / 2000)) ∧
      (∀ t ∈ Set.Icc a (a + 1 / 2000), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ t ∈ Set.Icc a (a + 1 / 2000), HasDerivWithinAt Y
        (compensatorField (U t) (Y t)) (Set.Icc a (a + 1 / 2000)) t) ∧
      RationalInterval.Contains
        (RationalInterval.CertificateReplay.IntegerReplay.view
          (RationalInterval.CertificateReplay.IntegerReplay.step s j st).enclosure)
        (Y (a + 1 / 2000)) := by
  let lo : ℝ := (RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure).lo
  let hi : ℝ := (RationalInterval.CertificateReplay.IntegerReplay.view st.enclosure).hi
  have hini : lo ≤ y₀ ∧ y₀ ≤ hi := hinit
  have hm : 73 / 100 ≤ lo ∧ hi ≤ 157 / 100 := hmargin
  have huc : ∀ t ∈ Set.Icc a (a + 1 / 2000), |U t| ≤ 107 / 1000 :=
    fun t ht => (hu t ht).trans hMcoarse
  have build (y : ℝ) (hl : lo ≤ y) (hh : y ≤ hi) :=
    compensator_local_exists U a (1 / 2000) y (by norm_num) hU huc
      (by linarith [hm.1]) (by linarith [hm.2])
  obtain ⟨Y, hYa, hYs, hYd, _⟩ := build y₀ hini.1 hini.2
  obtain ⟨L, hLa, hLs, hLd, _⟩ := build lo le_rfl (hini.1.trans hini.2)
  obtain ⟨V, hVa, hVs, hVd, _⟩ := build hi (hini.1.trans hini.2) le_rfl
  have hLY := compensator_solution_order U L Y a (a + 1 / 2000)
    (by linarith) huc hLd hYd hLs hYs (by rw [hLa, hYa]; exact hini.1)
  have hYV := compensator_solution_order U Y V a (a + 1 / 2000)
    (by linarith) huc hYd hVd hYs hVs (by rw [hYa, hVa]; exact hini.2)
  have htL := compensator_actual_taylor U dU L a (a + 1 / 2000) M D
    (by linarith) hM hD hU hdU hLd (fun t ht => hu t ⟨ht.1.le, ht.2.le⟩) hdu hLs
  have htV := compensator_actual_taylor U dU V a (a + 1 / 2000) M D
    (by linarith) hM hD hU hdU hVd (fun t ht => hu t ⟨ht.1.le, ht.2.le⟩) hdu hVs
  simp only [add_sub_cancel_left, hLa] at htL
  simp only [add_sub_cancel_left, hVa] at htV
  have hend : a + 1 / 2000 ∈ Set.Icc a (a + 1 / 2000) := ⟨by linarith, le_rfl⟩
  refine ⟨Y, hYa, compensator_solution_lipschitz U Y a (a + 1 / 2000) huc hYd hYs,
    hYs, hYd, ?_⟩
  apply RationalInterval.CertificateReplay.IntegerReplay.step_endpoint_sound s j st
    (compensatorField (U a) lo) (compensatorField (U a) hi) _ _ hEvalL hEvalU hError
  · have h := (abs_le.mp htL).1
    have hb := hLY _ hend
    change lo + (1 / 2000 : ℝ) * compensatorField (U a) lo - _ ≤ _
    linarith
  · have h := (abs_le.mp htV).2
    have hb := hYV _ hend
    change _ ≤ hi + (1 / 2000 : ℝ) * compensatorField (U a) hi + _
    linarith

/-- Finite induction pastes actual local solutions and preserves every mesh
enclosure. The step hypothesis is required only below the requested horizon;
there is no condition about future steps or an assumed global invariant. -/
theorem finite_scalar_trajectory (T : ℕ → ℝ) (hT : StrictMono T)
    (boxes : ℕ → RationalInterval.Box) (v : ℝ → ℝ → ℝ)
    (C : NNReal) (lower upper y₀ : ℝ)
    (hinit : RationalInterval.Contains (boxes 0) y₀) (hinitStrip : y₀ ∈ Set.Icc lower upper) :
    ∀ N : ℕ,
      (∀ k < N, ∀ y : ℝ, RationalInterval.Contains (boxes k) y →
        ∃ W : ℝ → ℝ, W (T k) = y ∧
          LipschitzOnWith C W (Set.Icc (T k) (T (k + 1))) ∧
          (∀ t ∈ Set.Icc (T k) (T (k + 1)), W t ∈ Set.Icc lower upper) ∧
          (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (T k) (T (k + 1)) →
            HasDerivAt W (v t (W t)) t) ∧
          RationalInterval.Contains (boxes (k + 1)) (W (T (k + 1)))) →
      ∃ Y : ℝ → ℝ, Y (T 0) = y₀ ∧
        LipschitzOnWith C Y (Set.Icc (T 0) (T N)) ∧
        (∀ t ∈ Set.Icc (T 0) (T N), Y t ∈ Set.Icc lower upper) ∧
        (∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (T 0) (T N) → HasDerivAt Y (v t (Y t)) t) ∧
        (∀ k ≤ N, RationalInterval.Contains (boxes k) (Y (T k))) := by
  intro N
  induction N with
  | zero =>
      intro _
      refine ⟨fun _ => y₀, rfl, ?_, (fun _ _ => hinitStrip), ?_, ?_⟩
      · rw [lipschitzOnWith_iff_dist_le_mul]
        intro x _ y _
        simp only [dist_self]
        exact mul_nonneg C.coe_nonneg dist_nonneg
      · exact Filter.Eventually.of_forall (fun t ht => by exfalso; linarith [ht.1, ht.2])
      · intro k hk
        have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
        subst k
        exact hinit
  | succ n ih =>
      intro hstep
      obtain ⟨Y, hYa, hYLip, hYs, hYd, hYbox⟩ :=
        ih (fun k hk => hstep k (Nat.lt_succ_of_lt hk))
      obtain ⟨W, hWa, hWLip, hWs, hWd, hWbox⟩ :=
        hstep n (Nat.lt_succ_self n) (Y (T n)) (hYbox n le_rfl)
      have h0n : T 0 ≤ T n := hT.monotone (Nat.zero_le n)
      have hnn : T n < T (n + 1) := hT (Nat.lt_succ_self n)
      let Z := joinSolutions Y W (T n)
      refine ⟨Z, ?_, joinSolutions_lipschitz Y W (T 0) (T n) (T (n + 1)) C
        h0n hnn.le hYLip hWLip hWa.symm, ?_,
        joinSolutions_ae_ode Y W v (T 0) (T n) (T (n + 1)) hYd hWd, ?_⟩
      · simpa only [Z, joinSolutions, if_pos h0n] using hYa
      · intro t ht
        by_cases htn : t ≤ T n
        · simpa only [Z, joinSolutions, if_pos htn] using hYs t ⟨ht.1, htn⟩
        · simpa only [Z, joinSolutions, if_neg htn] using
            hWs t ⟨(lt_of_not_ge htn).le, ht.2⟩
      · intro k hk
        by_cases hkn : k ≤ n
        · have hkt := hT.monotone hkn
          simpa only [Z, joinSolutions, if_pos hkt] using hYbox k hkn
        · have heq : k = n + 1 := by omega
          subst k
          simpa only [Z, joinSolutions, if_neg (not_le.mpr hnn)] using hWbox

def affineForcing (x₀ velocity t₀ t : ℝ) : ℝ :=
  (x₀ + velocity * (t - t₀)) *
    (velocity + (2 / 5 : ℝ) * (x₀ + velocity * (t - t₀) - 1))

def affineForcingDeriv (x₀ velocity t₀ t : ℝ) : ℝ :=
  velocity * (velocity + (2 / 5 : ℝ) * (2 * (x₀ + velocity * (t - t₀)) - 1))

theorem affineForcing_continuous (x₀ velocity t₀ : ℝ) :
    Continuous (affineForcing x₀ velocity t₀) := by unfold affineForcing; fun_prop

theorem affineForcing_hasDerivAt (x₀ velocity t₀ t : ℝ) :
    HasDerivAt (affineForcing x₀ velocity t₀) (affineForcingDeriv x₀ velocity t₀ t) t := by
  have hx : HasDerivAt (fun s => x₀ + velocity * (s - t₀)) velocity t := by
    simpa only [mul_one, sub_zero] using
      ((((hasDerivAt_id t).sub_const t₀).const_mul velocity).const_add x₀)
  have hh := hx.mul ((hasDerivAt_const t velocity).add ((hx.sub_const 1).const_mul (2 / 5 : ℝ)))
  convert hh using 1; dsimp [affineForcing, affineForcingDeriv]; ring

namespace ForcingBoxes
open RationalInterval RationalInterval.CertificateReplay

def velocity (I₀ I₁ : Box) (duration : ℚ) : Box := divide (subtract I₁ I₀) (rat duration)
def dollars (I₀ I₁ : Box) (duration : ℚ) : Box :=
  let X := hull I₀ I₁
  times X (add (velocity I₀ I₁ duration) (times rho (subtract X (rat 1))))
def dollarsDeriv (I₀ I₁ : Box) (duration : ℚ) : Box :=
  let V := velocity I₀ I₁ duration
  times V (add V (times rho (subtract (times (rat 2) (hull I₀ I₁)) (rat 1))))
def majorant (I₀ I₁ : Box) (duration : ℚ) : ℚ :=
  let M := magnitude (dollars I₀ I₁ duration)
  let D := magnitude (dollarsDeriv I₀ I₁ duration)
  9 * D / (7 / 10) + (2 / 5 + 9 * M / (49 / 100)) * (6 / 25 + 9 * M / (7 / 10))

theorem magnitude_nonnegative (I : Box) : 0 ≤ magnitude I :=
  (abs_nonneg I.lo).trans (le_max_left _ _)

theorem contains_abs_le {I : Box} {x : ℝ} (hx : Contains I x) : |x| ≤ (magnitude I : ℝ) := by
  have hl : -(magnitude I : ℝ) ≤ (I.lo : ℝ) := by
    exact_mod_cast (neg_le_neg (le_max_left |I.lo| |I.hi|)).trans (neg_abs_le I.lo)
  have hh : (I.hi : ℝ) ≤ (magnitude I : ℝ) := by
    exact_mod_cast (le_abs_self I.hi).trans (le_max_right |I.lo| |I.hi|)
  exact abs_le.mpr ⟨hl.trans hx.1, hx.2.trans hh⟩

theorem hull_contains_affine (I₀ I₁ : Box) (x₀ x₁ t₀ duration t : ℝ)
    (hd : 0 < duration) (hx₀ : Contains I₀ x₀) (hx₁ : Contains I₁ x₁)
    (ht : t ∈ Set.Icc t₀ (t₀ + duration)) :
    Contains (hull I₀ I₁) (x₀ + (x₁ - x₀) / duration * (t - t₀)) := by
  have hl₀ : ((hull I₀ I₁).lo : ℝ) ≤ (I₀.lo : ℝ) := by exact_mod_cast min_le_left I₀.lo I₁.lo
  have hl₁ : ((hull I₀ I₁).lo : ℝ) ≤ (I₁.lo : ℝ) := by exact_mod_cast min_le_right I₀.lo I₁.lo
  have hh₀ : (I₀.hi : ℝ) ≤ ((hull I₀ I₁).hi : ℝ) := by exact_mod_cast le_max_left I₀.hi I₁.hi
  have hh₁ : (I₁.hi : ℝ) ≤ ((hull I₀ I₁).hi : ℝ) := by exact_mod_cast le_max_right I₀.hi I₁.hi
  let θ := (t - t₀) / duration
  have hθ₀ : 0 ≤ θ := div_nonneg (sub_nonneg.mpr ht.1) hd.le
  have hθ₁ : θ ≤ 1 := (div_le_one hd).mpr (by linarith [ht.2])
  have hm := (convex_Icc ((hull I₀ I₁).lo : ℝ) ((hull I₀ I₁).hi : ℝ))
    (show x₀ ∈ Set.Icc _ _ from ⟨hl₀.trans hx₀.1, hx₀.2.trans hh₀⟩)
    (show x₁ ∈ Set.Icc _ _ from ⟨hl₁.trans hx₁.1, hx₁.2.trans hh₁⟩)
    (sub_nonneg.mpr hθ₁) hθ₀ (show 1 - θ + θ = 1 by ring)
  change x₀ + (x₁ - x₀) / duration * (t - t₀) ∈ Set.Icc _ _
  convert hm using 1; simp only [smul_eq_mul]; dsimp [θ]; ring

theorem velocity_sound (I₀ I₁ : Box) (duration : ℚ) (x₀ x₁ : ℝ)
    (hd : 0 < (rat duration).lo) (hx₀ : Contains I₀ x₀) (hx₁ : Contains I₁ x₁) :
    Contains (velocity I₀ I₁ duration) ((x₁ - x₀) / (duration : ℝ)) :=
  divide_sound hd (subtract_sound hx₁ hx₀) (rat_sound duration)

theorem forcing_bounds (I₀ I₁ : Box) (duration : ℚ) (x₀ x₁ t₀ t : ℝ)
    (hd : 0 < duration) (hden : 0 < (rat duration).lo)
    (hx₀ : Contains I₀ x₀) (hx₁ : Contains I₁ x₁)
    (ht : t ∈ Set.Icc t₀ (t₀ + duration)) :
    |affineForcing x₀ ((x₁ - x₀) / duration) t₀ t| ≤ (magnitude (dollars I₀ I₁ duration) : ℝ) ∧
    |affineForcingDeriv x₀ ((x₁ - x₀) / duration) t₀ t| ≤
      (magnitude (dollarsDeriv I₀ I₁ duration) : ℝ) := by
  have hdr : (0 : ℝ) < duration := by exact_mod_cast hd
  have hv := velocity_sound I₀ I₁ duration x₀ x₁ hden hx₀ hx₁
  have hx := hull_contains_affine I₀ I₁ x₀ x₁ t₀ duration t hdr hx₀ hx₁ ht
  have hr : Contains rho (2 / 5 : ℝ) := by simpa [rho] using rat_sound (2 / 5)
  have hu := times_sound hx (add_sound hv (times_sound hr (subtract_sound hx (rat_sound 1))))
  have hdu := times_sound hv (add_sound hv
    (times_sound hr (subtract_sound (times_sound (rat_sound 2) hx) (rat_sound 1))))
  constructor
  · simpa [dollars, affineForcing] using contains_abs_le hu
  · simpa [dollarsDeriv, affineForcingDeriv] using contains_abs_le hdu

theorem prepare_error_eq (I₀ I₁ : Box) (duration : ℚ) :
    (prepare I₀ I₁ duration).error = times (times (rat (majorant I₀ I₁ duration / 2)) dt) dt := rfl

theorem prepare_error_sound (I₀ I₁ : Box) (duration : ℚ) :
    Contains (prepare I₀ I₁ duration).error
      ((majorant I₀ I₁ duration : ℝ) * (1 / 2000 : ℝ) ^ 2 / 2) := by
  have hdt : Contains dt (1 / 2000 : ℝ) := by simpa [dt] using rat_sound (1 / 2000)
  have hh := times_sound (times_sound (rat_sound (majorant I₀ I₁ duration / 2)) hdt) hdt
  rw [prepare_error_eq]
  convert hh using 1; push_cast; ring

def integerPreparation (I₀ I₁ : Box) (duration : ℚ) : IntegerReplay.Segment :=
  let p := prepare I₀ I₁ duration
  ⟨IntegerReplay.ofRatBox p.x₀, IntegerReplay.ofRatBox p.velocity, IntegerReplay.ofRatBox p.error⟩

theorem integer_ofRatBox_sound {I : Box} {x : ℝ} (hx : Contains I x) :
    Contains (IntegerReplay.view (IntegerReplay.ofRatBox I)) x :=
  roundOut_sound grid grid_pos hx

theorem integerPreparation_parameters (I₀ I₁ : Box) (duration : ℚ) (x₀ x₁ : ℝ)
    (hden : 0 < (rat duration).lo) (hx₀ : Contains I₀ x₀) (hx₁ : Contains I₁ x₁) :
    Contains (IntegerReplay.view (integerPreparation I₀ I₁ duration).x₀) x₀ ∧
      Contains (IntegerReplay.view (integerPreparation I₀ I₁ duration).velocity)
        ((x₁ - x₀) / duration) := by
  exact ⟨integer_ofRatBox_sound hx₀,
    integer_ofRatBox_sound (velocity_sound I₀ I₁ duration x₀ x₁ hden hx₀ hx₁)⟩

theorem integerPreparation_error (I₀ I₁ : Box) (duration : ℚ) :
    Contains (IntegerReplay.view (integerPreparation I₀ I₁ duration).error)
      ((majorant I₀ I₁ duration : ℝ) * (1 / 2000 : ℝ) ^ 2 / 2) :=
  integer_ofRatBox_sound (prepare_error_sound I₀ I₁ duration)

theorem integer_field_at_affine_start (s : IntegerReplay.Segment) (j : ℕ)
    (x₀ velocity t₀ : ℝ) (k : Int)
    (hx₀ : Contains (IntegerReplay.view s.x₀) x₀)
    (hv : Contains (IntegerReplay.view s.velocity) velocity) (hk : 0 < k) :
    Contains (IntegerReplay.view (IntegerReplay.field s j ⟨k, k⟩))
      (compensatorField (affineForcing x₀ velocity t₀ (t₀ + (j : ℝ) / 2000))
        ((((k : ℚ) / grid : ℚ) : ℝ))) := by
  have hh := IntegerReplay.field_sound s j ⟨k, k⟩ x₀ velocity
    ((((k : ℚ) / grid : ℚ) : ℝ)) hx₀ hv (IntegerReplay.point_sound k) hk hk.le
  simpa only [compensatorField, affineForcing, add_sub_cancel_left] using hh

theorem positive_integer_endpoint_of_margin (k : Int)
    (hk : (73 / 100 : ℝ) ≤ ((((k : ℚ) / grid : ℚ) : ℝ))) : 0 < k := by
  by_contra hn
  have hn₀ : k ≤ 0 := le_of_not_gt hn
  have hq : (k : ℚ) / grid ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by exact_mod_cast hn₀) (by exact_mod_cast grid_pos.le)
  have hr : ((((k : ℚ) / grid : ℚ) : ℝ)) ≤ 0 := by exact_mod_cast hq
  linarith

/-- Prepared parameter boxes yield an actual physical step for every pair of
real endpoints in those boxes. All forcing calculus and both field evaluations
are derived here; only the exact static majorant and old-box checks remain. -/
theorem prepared_affine_step (I₀ I₁ : Box) (duration : ℚ)
    (x₀ x₁ t₀ y₀ : ℝ) (j : ℕ) (st : IntegerReplay.State)
    (hd : 0 < duration) (hden : 0 < (rat duration).lo)
    (hx₀ : Contains I₀ x₀) (hx₁ : Contains I₁ x₁)
    (hj : (j : ℝ) / 2000 + 1 / 2000 ≤ duration)
    (hcoarse : magnitude (dollars I₀ I₁ duration) ≤ 107 / 1000)
    (hinit : Contains (IntegerReplay.view st.enclosure) y₀)
    (hmargin : (73 / 100 : ℝ) ≤ (IntegerReplay.view st.enclosure).lo ∧
      ((IntegerReplay.view st.enclosure).hi : ℝ) ≤ 157 / 100) :
    let a := t₀ + (j : ℝ) / 2000
    ∃ Y : ℝ → ℝ, Y a = y₀ ∧
      LipschitzOnWith (17 / 10 : NNReal) Y (Set.Icc a (a + 1 / 2000)) ∧
      (∀ t ∈ Set.Icc a (a + 1 / 2000), Y t ∈ Set.Icc (7 / 10 : ℝ) (8 / 5)) ∧
      (∀ t ∈ Set.Icc a (a + 1 / 2000), HasDerivWithinAt Y
        (compensatorField (affineForcing x₀ ((x₁ - x₀) / duration) t₀ t) (Y t))
        (Set.Icc a (a + 1 / 2000)) t) ∧
      Contains (IntegerReplay.view (IntegerReplay.step (integerPreparation I₀ I₁ duration) j st).enclosure)
        (Y (a + 1 / 2000)) := by
  let a := t₀ + (j : ℝ) / 2000
  let M : ℝ := magnitude (dollars I₀ I₁ duration)
  let D : ℝ := magnitude (dollarsDeriv I₀ I₁ duration)
  have hm : 0 ≤ M := by dsimp [M]; exact_mod_cast magnitude_nonnegative (dollars I₀ I₁ duration)
  have hd₀ : 0 ≤ D := by dsimp [D]; exact_mod_cast magnitude_nonnegative (dollarsDeriv I₀ I₁ duration)
  have hmc : M ≤ 107 / 1000 := by
    have hc : ((magnitude (dollars I₀ I₁ duration) : ℚ) : ℝ) ≤ ((107 / 1000 : ℚ) : ℝ) := by
      exact_mod_cast hcoarse
    simpa only [M, Rat.cast_div, Rat.cast_ofNat] using hc
  have sub (t : ℝ) (ht : t ∈ Set.Icc a (a + 1 / 2000)) : t ∈ Set.Icc t₀ (t₀ + duration) := by
    have ha : t₀ ≤ a := by
      dsimp [a]
      exact le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg j) (by norm_num))
    constructor
    · exact ha.trans ht.1
    · dsimp [a] at ht
      linarith [ht.2]
  have hu : ∀ t ∈ Set.Icc a (a + 1 / 2000),
      |affineForcing x₀ ((x₁ - x₀) / duration) t₀ t| ≤ M :=
    fun t ht => (forcing_bounds I₀ I₁ duration x₀ x₁ t₀ t hd hden hx₀ hx₁ (sub t ht)).1
  have hdu : ∀ t ∈ Set.Ioo a (a + 1 / 2000),
      |affineForcingDeriv x₀ ((x₁ - x₀) / duration) t₀ t| ≤ D :=
    fun t ht => (forcing_bounds I₀ I₁ duration x₀ x₁ t₀ t hd hden hx₀ hx₁
      (sub t ⟨ht.1.le, ht.2.le⟩)).2
  have hpar := integerPreparation_parameters I₀ I₁ duration x₀ x₁ hden hx₀ hx₁
  have hlo : 0 < st.enclosure.lo := positive_integer_endpoint_of_margin _ hmargin.1
  have hhi : 0 < st.enclosure.hi := positive_integer_endpoint_of_margin _
    (hmargin.1.trans (hinit.1.trans hinit.2))
  have he := integerPreparation_error I₀ I₁ duration
  have he' : Contains (IntegerReplay.view (integerPreparation I₀ I₁ duration).error)
      ((9 * D / (7 / 10) + (2 / 5 + 9 * M / (49 / 100)) *
        (6 / 25 + 9 * M / (7 / 10))) * (1 / 2000 : ℝ) ^ 2 / 2) := by
    convert he using 1
    dsimp [M, D, majorant]
    push_cast
    ring
  exact validated_compensator_step
    (affineForcing x₀ ((x₁ - x₀) / duration) t₀)
    (affineForcingDeriv x₀ ((x₁ - x₀) / duration) t₀) a y₀ M D
    (integerPreparation I₀ I₁ duration) j st hm hd₀ hmc
    (affineForcing_continuous _ _ _).continuousOn
    (fun t _ => affineForcing_hasDerivAt _ _ _ t) hu hdu hinit hmargin
    (integer_field_at_affine_start _ j x₀ _ t₀ _ hpar.1 hpar.2 hlo)
    (integer_field_at_affine_start _ j x₀ _ t₀ _ hpar.1 hpar.2 hhi) he'

end ForcingBoxes

namespace IntegerChecks
open RationalInterval.CertificateReplay.IntegerReplay

theorem step_valid_imp_current (s : Segment) (j : ℕ) (st : State)
    (h : (step s j st).valid = true) : st.valid = true := by
  simp only [step, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem step_valid_old_bounds (s : Segment) (j : ℕ) (st : State)
    (h : (step s j st).valid = true) :
    73 * Q / 100 < st.enclosure.lo ∧ st.enclosure.hi < 157 * Q / 100 := by
  simp only [step, Bool.and_eq_true, decide_eq_true_eq] at h
  tauto

theorem run_valid_imp_current (s : Segment) (n : ℕ) :
    ∀ j st, (run s n j st).valid = true → st.valid = true := by
  induction n with
  | zero => intro j st h; exact h
  | succ n ih =>
      intro j st h
      exact step_valid_imp_current s j st (ih (j + 1) (step s j st) h)

theorem run_prefix_valid (s : Segment) (n : ℕ) :
    ∀ j st, (run s n j st).valid = true → ∀ k ≤ n, (run s k j st).valid = true := by
  induction n with
  | zero =>
      intro j st h k hk
      have heq : k = 0 := Nat.eq_zero_of_le_zero hk
      subst k
      exact h
  | succ n ih =>
      intro j st h k hk
      cases k with
      | zero => exact run_valid_imp_current s (n + 1) j st h
      | succ k => exact ih (j + 1) (step s j st) h k (by omega)

theorem run_succ_last (s : Segment) (n : ℕ) :
    ∀ j st, run s (n + 1) j st = step s (j + n) (run s n j st) := by
  induction n with
  | zero => intro j st; simp only [run, Nat.add_zero]
  | succ n ih =>
      intro j st
      simpa only [run, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (j + 1) (step s j st)

theorem run_step_valid (s : Segment) (n j : ℕ) (st : State)
    (h : (run s n j st).valid = true) (k : ℕ) (hk : k < n) :
    (step s (j + k) (run s k j st)).valid = true := by
  have hp := run_prefix_valid s n j st h (k + 1) (by omega)
  rwa [run_succ_last] at hp

end IntegerChecks

namespace WitnessMesh
open RationalInterval RationalInterval.CertificateReplay

def startBox (g : ℕ) : Box :=
  if g < 46 then rat 1 else if g < 354 then plateau else if g < 400 then plateau
  else if g < 446 then rat (97 / 100) else if g < 754 then rat (199 / 200) else rat (199 / 200)
def endBox (g : ℕ) : Box :=
  if g < 46 then plateau else if g < 354 then plateau else if g < 400 then rat (97 / 100)
  else if g < 446 then rat (199 / 200) else if g < 754 then rat (199 / 200) else rat (9409 / 10000)
def duration (g : ℕ) : ℚ :=
  if g < 46 then 23 / 10 else if g < 354 then 77 / 5 else if g < 400 then 23 / 10
  else if g < 446 then 23 / 10 else if g < 754 then 77 / 5 else 23 / 10
def pieceSteps (g : ℕ) : ℕ :=
  if g < 46 then 4600 else if g < 354 then 30800 else if g < 400 then 4600
  else if g < 446 then 4600 else if g < 754 then 30800 else 4600
def offset (g : ℕ) : ℕ :=
  if g < 46 then 0 else if g < 354 then 46 else if g < 400 then 354
  else if g < 446 then 400 else if g < 754 then 446 else 754
def startTime (g : ℕ) : ℝ := (offset g : ℝ) / 20
def actualStart (h : ℝ) (g : ℕ) : ℝ :=
  if g < 46 then 1 else if g < 354 then h else if g < 400 then h
  else if g < 446 then 97 / 100 else if g < 754 then 199 / 200 else 199 / 200
def actualEnd (h : ℝ) (g : ℕ) : ℝ :=
  if g < 46 then h else if g < 354 then h else if g < 400 then 97 / 100
  else if g < 446 then 199 / 200 else if g < 754 then 199 / 200 else 9409 / 10000

theorem parameter_boxes_contain (h : ℝ) (hh : Contains plateau h) (g : ℕ) :
    Contains (startBox g) (actualStart h g) ∧ Contains (endBox g) (actualEnd h g) := by
  have h1 : Contains (rat 1) (1 : ℝ) := by simpa using rat_sound 1
  have h97 : Contains (rat (97 / 100)) (97 / 100 : ℝ) := by simpa using rat_sound (97 / 100)
  have h995 : Contains (rat (199 / 200)) (199 / 200 : ℝ) := by simpa using rat_sound (199 / 200)
  have h9409 : Contains (rat (9409 / 10000)) (9409 / 10000 : ℝ) := by simpa using rat_sound (9409 / 10000)
  unfold startBox endBox actualStart actualEnd
  split_ifs
  · exact ⟨h1, hh⟩
  · exact ⟨hh, hh⟩
  · exact ⟨hh, h97⟩
  · exact ⟨h97, h995⟩
  · exact ⟨h995, h995⟩
  · exact ⟨h995, h9409⟩

set_option maxRecDepth 20000 in
theorem static_piece_checks (g : ℕ) :
    0 < duration g ∧ 0 < (rat (duration g)).lo ∧
      magnitude (ForcingBoxes.dollars (startBox g) (endBox g) (duration g)) < 107 / 1000 ∧
      magnitude (ForcingBoxes.dollarsDeriv (startBox g) (endBox g) (duration g)) < 41 / 1000 ∧
      ForcingBoxes.majorant (startBox g) (endBox g) (duration g) < 5 := by
  unfold startBox endBox duration
  split_ifs <;> decide +kernel

theorem integer_segment_eq (g : ℕ) :
    ForcingBoxes.integerPreparation (startBox g) (endBox g) (duration g) = IntegerReplay.segment g := by
  unfold ForcingBoxes.integerPreparation IntegerReplay.segment blockSegment
    startBox endBox duration
  split_ifs <;> rfl

theorem offset_le (g : ℕ) : offset g ≤ g := by unfold offset; split_ifs <;> omega

theorem blockStart_eq (g : ℕ) : blockStart g = 100 * (g - offset g) := rfl

theorem duration_eq_steps (g : ℕ) : (duration g : ℝ) = (pieceSteps g : ℝ) / 2000 := by
  unfold duration pieceSteps
  split_ifs <;> norm_num

theorem block_clock (g m : ℕ) :
    startTime g + ((blockStart g + m : ℕ) : ℝ) / 2000 =
      ((100 * g + m : ℕ) : ℝ) / 2000 := by
  rw [blockStart_eq]
  simp only [startTime, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (offset_le g), Nat.cast_ofNat]
  ring

theorem step_within_piece (g m : ℕ) (hg : g < 800) (hm : m < 100) :
    ((blockStart g + m : ℕ) : ℝ) / 2000 + 1 / 2000 ≤ duration g := by
  have hn : blockStart g + m + 1 ≤ pieceSteps g := by
    unfold blockStart pieceSteps
    split_ifs <;> omega
  have hr : (((blockStart g + m + 1 : ℕ) : ℝ)) ≤ (pieceSteps g : ℝ) := by
    exact_mod_cast hn
  rw [duration_eq_steps]
  have hh := div_le_div_of_nonneg_right hr (by norm_num : (0 : ℝ) ≤ 2000)
  simp only [Nat.cast_add, Nat.cast_one] at hh ⊢
  linarith

end WitnessMesh

namespace ResourceCertificate
open RationalInterval.CertificateReplay
open IntegerReplay

structure Row where
  lo : Int
  hi : Int
  compensatorSold : Int
  targetSold : Int
  pairedTurnover : Int
  deriving Inhabited

def initialRow : Row := ⟨Q, Q, 0, 0, 0⟩

-- BEGIN D01 RESOURCE ROW DATA
def resourceChunk_079_8 : Array Row := #[⟨139251984886387907461814955648378, 139327368634891341194642971499321, 187934212473014020097377836279580, 16460819812742191238996485356648, 294369483183397907338803969082840⟩,
⟨139258209935720057596309356968648, 139333600405232207145510664451479, 187934212473014020097377836279580, 16463131355476892718033545045032, 294389106003440761232943855661290⟩,
⟨139264434368379442434588338097141, 139339831556877429142523486555858, 187934212473014020097377836279580, 16465443133432277775812189074941, 294408730575588939172452362277548⟩,
⟨139270658184459866249324746180039, 139346062089921402820758482375022, 187934212473014020097377836279580, 16467755146608346494435468985222, 294428356899792646658274668515734⟩,
⟨139276881384055117366386113836188, 139352292004458507691593318617338, 187934212473014020097377836279580, 16470067395005098956009507593565, 294447984976002089191355953959969⟩,
⟨139283103967258968166657611184625, 139358521300583107144585878748799, 187934212473014020097377836279580, 16472379878622535242643499149688, 294467614804167472272641398194374⟩,
⟨139289325934165175087865437099325, 139364749978389548449354276409415, 187934212473014020097377836279580, 16474692597460655436449709488538, 294487246384239001403076180803070⟩,
⟨139295547284867478626400649114827, 139370978037972162757457287066454, 187934212473014020097377836279580, 16477005551519459619543476183495, 294506879716166882083605481370178⟩,
⟨139301768019459603339143431406853, 139377205479425265104275197337212, 187934212473014020097377836279580, 16479318740798947874043208699588, 294526514799901319815174479479819⟩,
⟨139307988138035257845287800272447, 139383432302843154410891071414468, 187934212473014020097377836279580, 16481632165299120282070388546721, 294546151635392520098728354716114⟩,
⟨139314207640688134828166746534626, 139389658508320113485972434028175, 187934212473014020097377836279580, 16483945825019976925749569432910, 294565790222590688435212286663184⟩,
⟨139320426527511911037077814296952, 139395884095950409027653369377399, 187934212473014020097377836279580, 16486259719961517887208377417526, 294585430561446030325571454905150⟩,
⟨139326644798600247289109115473885, 139402109065828291625417035466938, 187934212473014020097377836279580, 16488573850123743248577511064549, 294605072651908751270751039026133⟩,
⟨139332862454046788470965779523202, 139408333418047995761978593283488, 187934212473014020097377836279580, 16490888215506653091990741595834, 294624716493929056771696218610254⟩,
⟨139339079493945163540796837807215, 139414557152703739815168550246657, 187934212473014020097377836279580, 16493202816110247499584913044382, 294644362087457152329352173241634⟩,
⟨139345295918388985530022542009954, 139420780269889726059816517370560, 187934212473014020097377836279580, 16495517651934526553499942407626, 294664009432443243444664082504394⟩,
⟨139351511727471851545162116037911, 139427002769700140669635379572159, 187934212473014020097377836279580, 16497832722979490335878819800720, 294683658528837535618577125982655⟩,
⟨139357726921287342769661940832382, 139433224652229153719105878562944, 187934212473014020097377836279580, 16500148029245138928867608609845, 294703309376590234352036483260538⟩,
⟨139363941499929024465724171521883, 139439445917570919185361607760982, 187934212473014020097377836279580, 16502463570731472414615445645517, 294722961975651545145987333922164⟩,
⟨139370155463490445976135786343545, 139445666565819574950074418660792, 187934212473014020097377836279580, 16504779347438490875274541295911, 294742616325971673501374857551654⟩,
⟨139376368812065140726098066762823, 139451886597069242801340238098938, 187934212473014020097377836279580, 16507095359366194393000179680191, 294762272427500824919144233733129⟩,
⟨139382581545746626225056508221311, 139458106011414028435565295853652, 187934212473014020097377836279580, 16509411606514583049950718801851, 294781930280189204900240642050710⟩,
⟨139388793664628404068531160942852, 139464324808948021459352762017243, 187934212473014020097377836279580, 16511728088883656928287590702063, 294801589883987018945609262088518⟩,
⟨139395005168803959939947400228607, 139470542989765295391389793580466, 187934212473014020097377836279580, 16514044806473416110175301613038, 294821251238844472556195273430674⟩,
⟨139401216058366763612467125672147, 139476760553959907664334989668463, 187934212473014020097377836279580, 16516361759283860677781432111396, 294840914344711771232943855661298⟩,
⟨139407426333410268950820388726086, 139482977501625899626706254868307, 187934212473014020097377836279580, 16518678947314990713276637271542, 294860579201539120476800188364512⟩,
⟨139413635994027913913137448052195, 139489193832857296544769070088621, 187934212473014020097377836279580, 16520996370566806298834646819057, 294880245809276725788709451124437⟩,
⟨139419845040313120552781252087371, 139495409547748107604425170392162, 187934212473014020097377836279580, 16523314029039307516632265284095, 294899914167874792669616823525194⟩,
⟨139426053472359295020180348258278, 139501624646392325913101629242689, 187934212473014020097377836279580, 16525631922732494448849372154789, 294919584277283526620467485150903⟩,
⟨139432261290259827564662218277888, 139507839128883928501640348607875, 187934212473014020097377836279580, 16527950051646367177668922030670, 294939256137453133142206615585686⟩,
⟨139438468494108092536287038957601, 139514052995316876326187954360429, 187934212473014020097377836279580, 16530268415780925785276944776091, 294958929748333817735779394413664⟩,
⟨139444675083997448387681867969050, 139520266245785114270086096420033, 187934212473014020097377836279580, 16532587015136170353862545673665, 294978605109875785902131001218958⟩,
⟨139450881060021237675875253990110, 139526478880382571145762153079136, 187934212473014020097377836279580, 16534905849712100965617905577710, 294998282222029243142206615585688⟩,
⟨139457086422272787064132270670094, 139532690899203159696620338956045, 187934212473014020097377836279580, 16537224919508717702738281067705, 295017961084744394956951417097976⟩,
⟨139463291170845407323789973849516, 139538902302340776598933216019213, 187934212473014020097377836279580, 16539544224526020647422004601754, 295037641697971446847310585339942⟩,
⟨139469495305832393336093281470253, 139545113089889302463733607127020, 187934212473014020097377836279580, 16541863764764009881870484670059, 295057324061660604314229299895708⟩,
⟨139475698827327024094031275612357, 139551323261942601838706911527788, 187934212473014020097377836279580, 16544183540222685488288205948407, 295077008175762072858652740349395⟩,
⟨139481901735422562704173926094197, 139557532818594523210083821765189, 187934212473014020097377836279580, 16546503550902047548882729451661, 295096694040226057981526086285123⟩,
⟨139488104030212256388509235073055, 139563741759938899004533441434629, 187934212473014020097377836279580, 16548823796802096145864692687265, 295116381655002765183794517287014⟩,
⟨139494305711789336486280802083699, 139569950086069545591056803236618, 187934212473014020097377836279580, 16551144277922831361447809808753, 295136071020042399966403212939188⟩,
⟨139500506780247018455825808952919, 139576157797080263282880786773560, 187934212473014020097377836279580, 16553464994264253277848871769276, 295155762135295167830297352825767⟩,
⟨139506707235678501876413424028411, 139582364893064836339352435536814, 187934212473014020097377836279580, 16555785945826361977287746475131, 295175455000711274276422116530871⟩,
⟨139512907078176970450083625160843, 139588571374117032967833672531318, 187934212473014020097377836279580, 16558107132609157541987378939303, 295195149616240924805722683638622⟩,
⟨139519106307835592003486440878345, 139594777240330605325596413985469, 187934212473014020097377836279580, 16560428554612640054173791435015, 295214845981834324919144233733140⟩,
⟨139525304924747518489721609193115, 139600982491799289521718080594388, 187934212473014020097377836279580, 16562750211836809596076083649290, 295234544097441680117631946398547⟩,
⟨139531502929005885990178653480233, 139607187128616805618977505745126, 187934212473014020097377836279580, 16565072104281666249926432836520, 295254243963013195902131001218963⟩,
⟨139537700320703814716377374869226, 139613391150876857635751240172774, 187934212473014020097377836279580, 16567394231947210097960093972047, 295273945578499077773586577778510⟩,
⟨139543897099934409011808760589336, 139619594558673133547910252496875, 187934212473014020097377836279580, 16569716594833441222415399905751, 295293648943849531232943855661308⟩,
⟨139550093266790757353776307709881, 139625797352099305290717025087955, 187934212473014020097377836279580, 16572039192940359705533761515648, 295313354059014761781148014451479⟩,
⟨139556288821365932355237761717512, 139631999531249028760723044714400, 187934212473014020097377836279580, 16574362026267965629559667861502, 295333060923944974919144233733143⟩,
⟨139562483763752990766647269372604, 139638201096215943817666687420351, 187934212473014020097377836279580, 16576685094816259076740686338439, 295352769538590376147877693090421⟩,
⟨139568678094044973477797945287445, 139644402047093674286371497085685, 187934212473014020097377836279580, 16579008398585240129327462830577, 295372479902901170968293572107435⟩,
⟨139574871812334905519664851669295, 139650602383975827958644857119581, 187934212473014020097377836279580, 16581331937574908869573721864661, 295392192016827564881337050368305⟩,
⟨139581064918715796066248390671837, 139656802106955996595177054739595, 187934212473014020097377836279580, 16583655711785265379736266763713, 295411905880319763387953307457152⟩,
⟨139587257413280638436418108798944, 139663001216127755927440737288580, 187934212473014020097377836279580, 16585979721216309742074979800686, 295431621493327971989087522958098⟩,
⟨139593449296122410095756912805118, 139669199711584665659590760042205, 187934212473014020097377836279580, 16588303965868042038852822352130, 295451338855802396185684876455263⟩,
⟨139599640567334072658405696537383, 139675397593420269470364424960259, 187934212473014020097377836279580, 16590628445740462352335835051868, 295471057967693241478690547532768⟩,
⟨139605831227008571888908378163831, 139681594861728095014982109835326, 187934212473014020097377836279580, 16592953160833570764793137944681, 295490778828950713369049715774734⟩,
⟨139612021275238837704057347234450, 139687791516601653927048287292850, 187934212473014020097377836279580, 16595278111147367358496930640004, 295510501439525017357707560765283⟩,
⟨139618210712117784174739321020270, 139693987558134441820452933097029, 187934212473014020097377836279580, 16597603296681852215722492465627, 295530225799366358945609262088535⟩,
⟨139624399537738309527781609577311, 139700182986419938291273323217375, 187934212473014020097377836279580, 16599928717437025418748182621412, 295549951908424943633699999328611⟩,
⟨139630587752193296147798788982210, 139706377801551606919676219111216, 187934212473014020097377836279580, 16602254373412887049855440333016, 295569679766650976922924952069632⟩,
⟨139636775355575610579039782186845, 139712572003622895271820440677831, 187934212473014020097377836279580, 16604580264609437191328785005622, 295589409373994664314229299895719⟩,
⟨139642962347978103527235346939689, 139718765592727234901759826340306, 187934212473014020097377836279580, 16606906391026675925455816377684, 295609140730406211308558222390994⟩,
⟨139649148729493609861445970222044, 139724958568958041353346579711642, 187934212473014020097377836279580, 16609232752664603334527214674677, 295628873835835823406856899139577⟩,
⟨139655334500214948615910168647733, 139731150932408714162135002302048, 187934212473014020097377836279580, 16611559349523219500836740762862, 295648608690233706110070509725589⟩,
⟨139661519660234922991893194275238, 139737342683172636857285611724763, 187934212473014020097377836279580, 16613886181602524506681236303055, 295668345293550064919144233733151⟩,
⟨139667704209646320359536145281704, 139743533821343176963469644858183, 187934212473014020097377836279580, 16616213248902518434360623904407, 295688083645735105335023250746384⟩,
⟨139673888148541912259705480948642, 139749724347013686002773945422473, 187934212473014020097377836279580, 16618540551423201366177907278198, 295707823746739032858652740349409⟩,
⟨139680071477014454405842940409572, 139755914260277499496606235429254, 187934212473014020097377836279580, 16620868089164573384439171391634, 295727565596512052990977882126347⟩,
⟨139686254195156686685815864610298, 139762103561227936967600769963393, 187934212473014020097377836279580, 16623195862126634571453582621659, 295747309195004371232943855661319⟩,
⟨139692436303061333163767920932880, 139768292249958301941524374756303, 187934212473014020097377836279580, 16625523870309385009533388908774, 295767054542166193085495840538446⟩,
⟨139698617800821102081970229934833, 139774480326561881949182866010614, 187934212473014020097377836279580, 16627852113712824780993919910864, 295786801637947724049579016341849⟩,
⟨139704798688528685862672893655464, 139780667791131948528327851936449, 187934212473014020097377836279580, 16630180592336953968153587157039, 295806550482299169626138562655649⟩,
⟨139710978966276761109956924941696, 139786854643761757225563915459993, 187934212473014020097377836279580, 16632509306181772653333884201482, 295826301075170735316119659063967⟩,
⟨139717158634157988611586577246143, 139793040884544547598256177565424, 187934212473014020097377836279580, 16634838255247280918859386777305, 295846053416512626620467485150924⟩,
⟨139723337692265013340862074350602, 139799226513573543216438240731702, 187934212473014020097377836279580, 16637167439533478847057752950418, 295865807506275049040127220500641⟩,
⟨139729516140690464458472739468572, 139805411530941951664720511926126, 187934212473014020097377836279580, 16639496859040366520259723273406, 295885563344408208076044044697239⟩,
⟨139735693979526955314350523180797, 139811595936742964544198904616980, 187934212473014020097377836279580, 16641826513767944020799120939415, 295905320930862309229163137324839⟩,
⟨139741871208867083449523929658269, 139817779731069757474363919267989, 187934212473014020097377836279580, 16644156403716211431012851936047, 295925080265587558000429677967562⟩,
⟨139748047828803430597972340627525, 139823962914015490095010101777744, 187934212473014020097377836279580, 16646486528885168833240905199269, 295944841348534159890788846209528⟩,
⟨139754223839428562688480736533506, 139830145485673306068145879327636, 187934212473014020097377836279580, 16648816889274816309826352767326, 295964604179652320401185821634859⟩,
⟨139760399240835029846494814355640, 139836327446136333079903773102270, 187934212473014020097377836279580, 16651147484885153943115349934666, 295984368758892245032565783827676⟩,
⟨139766574033115366395976501533246, 139842508795497682842450987346738, 187934212473014020097377836279580, 16653478315716181815457135405875, 296004135086204139285873912372100⟩,
⟨139772748216362090861259865456755, 139848689533850451095900374225533, 187934212473014020097377836279580, 16655809381767900009204031449623, 296023903161538208662055386852252⟩,
⟨139778921790667705968907417981666, 139854869661287717610221773948301, 187934212473014020097377836279580, 16658140683040308606711444052615, 296043672984844658662055386852253⟩,
⟨139785094756124698649566814422571, 139861049177902546187153729628044, 187934212473014020097377836279580, 16660472219533407690337863073556, 296063444556073694786819091956223⟩,
⟨139791267112825540039827946484986, 139867228083787984662115576337781, 187934212473014020097377836279580, 16662803991247197342444862397124, 296083217875175522537291681748284⟩,
⟨139797438860862685484080428593151, 139873406379037064906119903832097, 187934212473014020097377836279580, 16665135998181677645397100087953, 296102992942100347414418335812557⟩,
⟨139803610000328574536371477072365, 139879584063742802827685392400417, 187934212473014020097377836279580, 16667468240336848681562318544623, 296122769756798374919144233733162⟩,
⟨139809780531315630962264181644843, 139885761137998198374750021319241, 187934212473014020097377836279580, 16669800717712710533311344653666, 296142548319219810552414555094221⟩,
⟨139815950453916262740696168698484, 139891937601896235536584649371001, 187934212473014020097377836279580, 16672133430309263283018089943573, 296162328629314859815174479479855⟩,
⟨139822119768222862065838655788364, 139898113455529882345706966897588, 187934212473014020097377836279580, 16674466378126507013059550738818, 296182110687033728208369186474184⟩,
⟨139828288474327805348955896831168, 139904288698992090879795818857023, 187934212473014020097377836279580, 16676799561164441805815808313888, 296201894492326621232943855661330⟩,
⟨139834456572323453220265017453190, 139910463332375797263605898352148, 187934212473014020097377836279580, 16679132979423067743670029047324, 296221680045143744389843666625414⟩,
⟨139840624062302150530796239952951, 139916637355773921670882810100611, 187934212473014020097377836279580, 16681466632902384909008464575769, 296241467345435303180013798950556⟩,
⟨139846790944356226354253497339872, 139922810769279368326278503315843, 187934212473014020097377836279580, 16683800521602393384220451948030, 296261256393151503104399432220878⟩,
⟨139852957218577993988875435910882, 139928983572985025507267073469110, 187934212473014020097377836279580, 16686134645523093251698413779145, 296281047188242549663945746020500⟩,
⟨139859122885059750959296805827222, 139935155766983765546060932403155, 187934212473014020097377836279580, 16688469004664484593837858404463, 296300839730658648359597919933544⟩,
⟨139865287943893779018410239154127, 139941327351368444831527346268323, 187934212473014020097377836279580, 16690803599026567493037380033733, 296320634020350004692301133544131⟩]
def resourceChunk_079_9 : Array Row := #[⟨139871452395172344149228414826490, 139947498326231903811105340752491, 187934212473014020097377836279580, 16693138428609342031698658905201, 296340430057266824163000566436381⟩,
⟨139877616238987696566746610003996, 139953668691666966992722973076519, 187934212473014020097377836279580, 16695473493412808292226461439717, 296360227841359312272641398194416⟩,
⟨139883779475432070719805637279644, 139959838447766442946714970227340, 187934212473014020097377836279580, 16697808793436966357028640394855, 296380027372577674522168808402356⟩,
⟨139889942104597685292955167205977, 139966007594623124307740732901221, 187934212473014020097377836279580, 16700144328681816308516135019036, 296399828650872116412527976644322⟩,
⟨139896104126576743208317435603740, 139972176132329787776702704630127, 187934212473014020097377836279580, 16702480099147358229102971205669, 296419631676192843444664082504436⟩,
⟨139902265541461431627451335118113, 139978344060979194122665105564521, 187934212473014020097377836279580, 16704816104833592201206261647292, 296439436448490061119522305566818⟩,
⟨139908426349343921953216890488051, 139984511380664088184773030386341, 187934212473014020097377836279580, 16707152345740518307246205989733, 296459242967713974938047825415590⟩,
⟨139914586550316369831640116994689, 139990678091477198874171909826297, 187934212473014020097377836279580, 16709488821868136629646090986272, 296479051233814790401185821634872⟩,
⟨139920746144470915153778261555170, 139996844193511239175927335260035, 187934212473014020097377836279580, 16711825533216447250832290651816, 296498861246742713009881473808786⟩,
⟨139926905131899682057585425928655, 140003009686858906150945245858117, 187934212473014020097377836279580, 16714162479785450253234266417086, 296518673006447948265079961521452⟩,
⟨139933063512694778929778571501695, 140009174571612880937892477765166, 187934212473014020097377836279580, 16716499661575145719284567282809, 296538486512880701667726464356991⟩,
⟨139939221286948298407703905120535, 140015338847865828755117674783934, 187934212473014020097377836279580, 16718837078585533731418829973924, 296558301765991178718766161899525⟩,
⟨139945378454752317381203645438335, 140021502515710398902572560040449, 187934212473014020097377836279580, 16721174730816614372075779093792, 296578118765729584919144233733174⟩,
⟨139951535016198896994483169245704, 140027665575239224763733568106791, 187934212473014020097377836279580, 16723512618268387723697227278423, 296597937512046125769805859442059⟩,
⟨139957690971380082647978537253333, 140033828026544923807523837058468, 187934212473014020097377836279580, 16725850740940853868728075350707, 296617758004891006771696218610301⟩,
⟨139963846320387904000224398795930, 140039989869720097590235559943742, 187934212473014020097377836279580, 16728189098834012889616312474657, 296637580244214433425760490822022⟩,
⟨139970001063314374969722274927064, 140046151104857331757452695142672, 187934212473014020097377836279580, 16730527691947864868813016309659, 296657404229966611232943855661342⟩,
⟨139976155200251493736809219374922, 140052311732049196045974035094031, 187934212473014020097377836279580, 16732866520282409888772353164736, 296677229962097745694191492712382⟩,
⟨139982308731291242745526856829394, 140058471751388244285736632868662, 187934212473014020097377836279580, 16735205583837648031951578152819, 296697057440558042310448581559263⟩,
⟨139988461656525588705490798031306, 140064631162967014401739586068233, 187934212473014020097377836279580, 16737544882613579380811035345027, 296716886665297706582660301786107⟩,
⟨139994613976046482593760431135016, 140070789966878028415968177528750, 187934212473014020097377836279580, 16739884416610204017814157924958, 296736717636266944011771832977034⟩,
⟨140000765689945859656709088815999, 140076948163213792449318372308594, 187934212473014020097377836279580, 16742224185827522025427468342990, 296756550353415960098728354716165⟩,
⟨140006916798315639411894590595451, 140083105752066796723521670441231, 187934212473014020097377836279580, 16744564190265533486120578470589, 296776384816694960344475046587621⟩,
⟨140013067301247725649930159854330, 140089262733529515563070314933169, 187934212473014020097377836279580, 16746904429924238482366189754630, 296796221026054150249957088175523⟩,
⟨140019217198834006436355715009684, 140095419107694407397142854488097, 187934212473014020097377836279580, 16749244904803637096640093371725, 296816058981443735316119659063992⟩,
⟨140025366491166354113509534326479, 140101574874653914761530060438581, 187934212473014020097377836279580, 16751585614903729411421170382563, 296835898682813921043907938837149⟩,
⟨140031515178336625302400293838577, 140107730034500464300561197367057, 187934212473014020097377836279580, 16753926560224515509191391886257, 296855740130114912934267107079115⟩,
⟨140037663260436660904579477852895, 140113884587326466769030646898275, 187934212473014020097377836279580, 16756267740765995472435819174704, 296875583323296916488142343374012⟩,
⟨140043810737558286104014161511184, 140120038533224317034124884145737, 187934212473014020097377836279580, 16758609156528169383642603886950, 296895428262310137206478827305960⟩,
⟨140049957609793310368960164884266, 140126191872286394077349806295079, 187934212473014020097377836279580, 16760950807511037325302988163569, 296915274947104780590221738459080⟩,
⟨140056103877233527453835578073966, 140132344604605060996458412807734, 187934212473014020097377836279580, 16763292693714599379911304801050, 296935123377631052140316256417493⟩,
⟨140062249539970715401094656798388, 140138496730272665007378836728612, 187934212473014020097377836279580, 16765634815138855629964977406193, 296954973553839157357707560765320⟩,
⟨140068394598096636543102087936559, 140144648249381537446142726581929, 187934212473014020097377836279580, 16767977171783806157964520550514, 296974825475679301743340831086682⟩,
⟨140074539051703037504007624508897, 140150799162023993770813978339719, 187934212473014020097377836279580, 16770319763649451046413539924664, 296994679143101690798161246965700⟩,
⟨140080682900881649201621089570327, 140156949468292333563417816947949, 187934212473014020097377836279580, 16772662590735790377818732492852, 297014534556056530023113987986494⟩,
⟨140086826145724186849287748493295, 140163099168278840531870226895551, 187934212473014020097377836279580, 16775005653042824234689886647280, 297034391714494024919144233733186⟩,
⟨140092968786322349957764049118302, 140169248262075782511907731312100, 187934212473014020097377836279580, 16777348950570552699539882362589, 297054250618364380987197163789897⟩,
⟨140099110822767822337093729250012, 140175396749775411469017519080225, 187934212473014020097377836279580, 16779692483318975854884691350314, 297074111267617803728217957740748⟩,
⟨140105252255152272098484290977347, 140181544631469963500367919449280, 187934212473014020097377836279580, 16782036251288093783243377213345, 297093973662204498643151795169860⟩,
⟨140111393083567351656183841296413, 140187691907251658836739223637151, 187934212473014020097377836279580, 16784380254477906567138095600405, 297113837802074671232943855661354⟩,
⟨140117533308104697729358298515482, 140193838577212701844454852907499, 187934212473014020097377836279580, 16786724492888414289094094360530, 297133703687178526998539318799351⟩,
⟨140123672928855931343968963921654, 140199984641445281027312872610126, 187934212473014020097377836279580, 16789068966519617031639713697563, 297153571317466271440883364167972⟩,
⟨140129811945912657834650458189224, 140206130100041569028517851672533, 187934212473014020097377836279580, 16791413675371514877306386324657, 297173440692888110060921171351337⟩,
⟨140135950359366466846589022010172, 140212274953093722632613067031142, 187934212473014020097377836279580, 16793758619444107908628637618787, 297193311813394248359597919933568⟩,
⟨140142088169308932337401180427595, 140218419200693882767413052491050, 187934212473014020097377836279580, 16796103798737396208144085775273, 297213184678934891837858789498786⟩,
⟨140148225375831612579012770353286, 140224562842934174505936491503561, 187934212473014020097377836279580, 16798449213251379858393441962309, 297233059289460245996648959631112⟩,
⟨140154361979026050159538330751076, 140230705879906707068339453351148, 187934212473014020097377836279580, 16800794862986058941920510475508, 297252935644920516336913609914666⟩,
⟨140160497978983771985160854967939, 140236848311703573823848972229880, 187934212473014020097377836279580, 16803140747941433541272188892449, 297272813745265908359597919933570⟩,
⟨140166633375796289282011904695255, 140242990138416852292696968719748, 187934212473014020097377836279580, 16805486868117503738998468227240, 297292693590446627565647069271945⟩,
⟨140172768169555097598052085043034, 140249131360138604148054513133701, 187934212473014020097377836279580, 16807833223514269617652433085088, 297312575180412879456006237513911⟩,
⟨140178902360351676804951880210275, 140255271976960875217966430236612, 187934212473014020097377836279580, 16810179814131731259790261816878, 297332458515114869531620604243590⟩,
⟨140185035948277491099972849235058, 140261411988975695487286244825775, 187934212473014020097377836279580, 16812526639969888747971226673763, 297352343594502803293435349045103⟩,
⟨140191168933423989007849181308336, 140267551396275079099611467664918, 187934212473014020097377836279580, 16814873701028742164757693961764, 297372230418526886242395651502570⟩,
⟨140197301315882603382669610135798, 140273690198951024359219221264119, 187934212473014020097377836279580, 16817220997308291592715124196378, 297392118987137323879446691200113⟩,
⟨140203433095744751409759686832571, 140279828397095513733002204998397, 187934212473014020097377836279580, 16819568528808537114412072257196, 297412009300284321705533647721853⟩,
⟨140209564273101834607564410835913, 140285965990800513852404999058135, 187934212473014020097377836279580, 16821916295529478812420187542532, 297431901357918085221601700651910⟩,
⟨140215694848045238829531218321454, 140292102980157975515360706724886, 187934212473014020097377836279580, 16824264297471116769314214124060, 297451795159988819928596029574406⟩,
⟨140221824820666334265993327608918, 140298239365259833688227934466502, 187934212473014020097377836279580, 16826612534633451067671990901463, 297471690706446731327461814073461⟩,
⟨140227954191056475446053441043672, 140304375146198007507728109345908, 187934212473014020097377836279580, 16828961007016481790074451757088, 297491587997242024919144233733197⟩,
⟨140234082959307001239467802840817, 140310510323064400282883133238242, 187934212473014020097377836279580, 16831309714620209019105625710615, 297511487032324906204588468137734⟩,
⟨140240211125509234858530612378951, 140316644895950899496953373351462, 187934212473014020097377836279580, 16833658657444632837352637073732, 297531387811645580684739696871194⟩,
⟨140246338689754483859958792431105, 140322778864949376809375988545904, 187934212473014020097377836279580, 16836007835489753327405705604822, 297551290335154253860543099517697⟩,
⟨140252465652134040146777111820758, 140328912230151688057703590948678, 187934212473014020097377836279580, 16838357248755570571858146663657, 297571194602801131232943855661365⟩,
⟨140258592012739179970203661991225, 140335044991649673259543242359160, 187934212473014020097377836279580, 16840706897242084653306371366106, 297591100614536418302887144886318⟩,
⟨140264717771661163931535686977093, 140341177149535156614495784942235, 187934212473014020097377836279580, 16843056780949295654349886738849, 297611008370310320571318146776678⟩,
⟨140270842928991236984035766266788, 140347308703899946506095505706326, 187934212473014020097377836279580, 16845406899877203657591295874101, 297630917870073043539182040916565⟩,
⟨140276967484820628434818350045725, 140353439654835835503750134263635, 187934212473014020097377836279580, 16847757254025808745636298084346, 297650829113774792707424006890100⟩,
⟨140283091439240551946736646309907, 140359570002434600364681173370404, 187934212473014020097377836279580, 16850107843395111001093689057085, 297670742101365773576989224281405⟩,
⟨140289214792342205540269859340198, 140365699746788002035864561745392, 187934212473014020097377836279580, 16852458667985110506575361009585, 297690656832796191648822872674600⟩,
⟨140295337544216771595410779027922, 140371828887987785655971668665149, 187934212473014020097377836279580, 16854809727795807344696302843645, 297710573308016252423870131653807⟩,
⟨140301459694955416853553720542785, 140377957426125680557310619835054, 187934212473014020097377836279580, 16857161022827201598074600300368, 297730491526976161403076180803146⟩,
⟨140307581244649292419382813834550, 140384085361293400267767954035461, 187934212473014020097377836279580, 16859512553079293349331436114945, 297750411489626124087386199706738⟩,
⟨140313702193389533762760642460248, 140390212693582642512750610042695, 187934212473014020097377836279580, 16861864318552082681091090171446, 297770333195916345977745367948704⟩,
⟨140319822541267260720617231229115, 140396339423085089217128243325013, 187934212473014020097377836279580, 16864216319245569675980939657624, 297790256645797032575098865113166⟩,
⟨140325942288373577498839382157827, 140402465549892406507175872014035, 187934212473014020097377836279580, 16866568555159754416631459219725, 297810181839218389380391870784244⟩,
⟨140332061434799572674160358228991, 140408591074096244712516851652526, 187934212473014020097377836279580, 16868921026294636985676221117310, 297830108776130621894569564546059⟩,
⟨140338179980636319196049914446243, 140414715995788238368066178219805, 187934212473014020097377836279580, 16871273732650217465751895378087, 297850037456483935618577125982732⟩,
⟨140344297925974874388604675679687, 140420840315060006215974118936431, 187934212473014020097377836279580, 16873626674226495939498249952751, 297869967880228536053359734678385⟩,
⟨140350415270906279952438860795785, 140426964032003151207570170350196, 187934212473014020097377836279580, 16875979851023472489558150869835, 297889900047314628699862570217138⟩,
⟨140356532015521561966575352566222, 140433087146709260505307343205854, 187934212473014020097377836279580, 16878333263041147198577562390568, 297909833957692419059030812183112⟩,
⟨140362648159911730890337112850624, 140439209659269905484706773601374, 187934212473014020097377836279580, 16880686910279520149205547163748, 297929769611312112631809640160428⟩,
⟨140368763704167781565238942548415, 140445331569776641736302659933905, 187934212473014020097377836279580, 16883040792738591424094266380621, 297949707008123914919144233733207⟩,
⟨140374878648380693216879585815474, 140451452878321009067587525139016, 187934212473014020097377836279580, 16885394910418361105898979929768, 297969646148078031421979772485570⟩,
⟨140380992992641429456834178041643, 140457573584994531504957803727152, 187934212473014020097377836279580, 16887749263318829277278046552005, 297989587031124667641261436001639⟩,
⟨140387106737040938284547037085515, 140463693689888717295659753121637, 187934212473014020097377836279580, 16890103851439996020892923995293, 298009529657214029077934403865534⟩,
⟨140393219881670152089224797263328, 140469813193095058909735688802922, 187934212473014020097377836279580, 16892458674781861419408169169654, 298029474026296321232943855661376⟩,
⟨140399332426619987651729885589160, 140475932094705033041970542764174, 187934212473014020097377836279580, 16894813733344425555491438302101, 298049420138321749607234970973286⟩,
⟨140405444371981346146474339764014, 140482050394810100613838744783667, 187934212473014020097377836279580, 16897169027127688511813487091573, 298069367993240519701752929385385⟩,
⟨140411555717845113143313967411767, 140488168093501706775451426019820, 187934212473014020097377836279580, 16899524556131650371048170863886, 298089317591002837017442910481794⟩,
⟨140417666464302158609442846060331, 140494285190871280907503944435116, 187934212473014020097377836279580, 16901880320356311215872444726686, 298109268931558907055250093846634⟩,
⟨140423776611443336911288163366766, 140500401687010236623223731555502, 187934212473014020097377836279580, 16904236319801671128966363724418, 298129222014858935316119659064026⟩,
⟨140429886159359486816405397085463, 140506517582009971770318460072249, 187934212473014020097377836279580, 16906592554467730193013082993301, 298149176840853127300996785718091⟩,
⟨140435995108141431495373834278898, 140512632875961868432924531793652, 187934212473014020097377836279580, 16908949024354488490698857916316, 298169133409491688510826653392950⟩,
⟨140442103457879978523692429270850, 140518747568957292933555885454293, 187934212473014020097377836279580, 16911305729461946104713044278200, 298189091720724824446554441672724⟩,
⟨140448211208665919883675999842334, 140524861661087595835053123890002, 187934212473014020097377836279580, 16913662669790103117748098420452, 298209051774502740609125330141534⟩,
⟨140454318360590031966351761170911, 140530975152444111942532960087001, 187934212473014020097377836279580, 16916019845338959612499577396348, 298229013570775642499484498383500⟩,
⟨140460424913743075573356197014397, 140537088043118160305337981614119, 187934212473014020097377836279580, 16918377256108515671666139125965, 298248977109493735618577125982744⟩,
⟨140466530868215795918832267640387, 140543200333201044218986732947323, 187934212473014020097377836279580, 16920734902098771377949542551217, 298268942390607225467348392523387⟩,
⟨140472636224098922631326954003377, 140549312022784051227124115196197, 187934212473014020097377836279580, 16923092783309726814054647790897, 298288909414066317546743477589550⟩,
⟨140478740981483169755689137671669, 140555423111958453123472102742373, 187934212473014020097377836279580, 16925450899741382062689416295734, 298308878179821217357707560765354⟩]
def rows : Array (Array (Array Row)) := #[
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[#[], #[], #[], #[], #[], #[], #[], #[], #[], (Array.replicate 99 (default : Row)).push ⟨122193882108272462678373443015812, 122253552023031466215922378630777, 180533099611481676127601758661829, 5471484029454540857382965385158, 189935892494523506582660301781596⟩],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[],
#[#[], #[], #[], #[], #[], #[], #[], (Array.replicate 99 (default : Row)).push ⟨139245759220289171809804460239277, 139321136245760419529264810043548, 187934212473014020097377836279580, 16458508505228173256601029596606, 294349862115510171989087522958076⟩, resourceChunk_079_8, resourceChunk_079_9]
]
-- END D01 RESOURCE ROW DATA

def rowAt (k : ℕ) : Row :=
  if k = 0 then initialRow else ((rows[(k - 1) / 1000]!)[((k - 1) % 1000) / 100]!)[(k - 1) % 100]!

def stateAt (k : ℕ) : IntegerReplay.State := ⟨⟨(rowAt k).lo, (rowAt k).hi⟩, true⟩
def localIndex (k : ℕ) : ℕ := blockStart (k / 100) + k % 100

structure Estimate where
  nextState : IntegerReplay.State
  lowerPrice : Int
  upperPrice : Int
  targetPrice : Interval
  dollars : Interval
  compensatorSoldIncrement : Int
  targetSoldIncrement : Int
  pairedTurnoverIncrement : Int

def estimate (k : ℕ) : Estimate := Id.run do
  let s := segment (k / 100)
  let j := localIndex k
  let r := rowAt k
  let next := step s j (stateAt k)
  let motion := (multiply (lit (17 / 10)) (lit (1 / 2000))).hi
  let lb := min r.lo next.enclosure.lo - motion
  let hb := max r.hi next.enclosure.hi + motion
  let x₀ := plus s.x₀ (multiply s.velocity (lit ((j : ℚ) / 2000)))
  let x₁ := plus s.x₀ (multiply s.velocity (lit (((j + 1 : ℕ) : ℚ) / 2000)))
  let xx := Interval.mk (min x₀.lo x₁.lo) (max x₀.hi x₁.hi)
  let uu := multiply xx (plus s.velocity (multiply (lit (2 / 5)) (minus xx (lit 1))))
  let pos := Interval.mk (max 0 uu.hi) (max 0 uu.hi)
  let neg := Interval.mk (max 0 (-uu.lo)) (max 0 (-uu.lo))
  let absU := max |uu.lo| |uu.hi|
  let cs := (multiply (quotient (multiply (lit 9) pos) ⟨lb, lb⟩) (lit (1 / 2000))).hi
  let ts := (multiply (quotient neg ⟨xx.lo, xx.lo⟩) (lit (1 / 2000))).hi
  let turn := (multiply (multiply (lit 9) ⟨absU, absU⟩) (lit (1 / 2000))).hi
  return ⟨next, lb, hb, xx, uu, cs, ts, turn⟩

def checkRow (k : ℕ) : Bool := Id.run do
  let r := rowAt k
  let n := rowAt (k + 1)
  let c := estimate k
  let absU := max |c.dollars.lo| |c.dollars.hi|
  let band := if k < 40000 then
      decide (3 * Q / 4 < c.lowerPrice) && decide (c.upperPrice < 5 * Q / 4)
    else
      let reference := rowAt 40000
      decide (3 * reference.hi < 4 * c.lowerPrice) &&
        decide (4 * c.upperPrice < 5 * reference.lo)
  return c.nextState.valid &&
    decide (c.nextState.enclosure.lo = n.lo) && decide (c.nextState.enclosure.hi = n.hi) &&
    decide (0 < c.targetPrice.lo) && decide (0 < c.lowerPrice) &&
    decide (9 * absU * 1000000 < 284481 * c.lowerPrice) &&
    decide (absU * 1000000 < 284481 * c.targetPrice.lo) && band &&
    decide (n.compensatorSold = r.compensatorSold + c.compensatorSoldIncrement) &&
    decide (n.targetSold = r.targetSold + c.targetSoldIncrement) &&
    decide (n.pairedTurnover = r.pairedTurnover + c.pairedTurnoverIncrement)

def checkGroup (g : ℕ) : Bool := (List.range 1000).all (fun j => checkRow (1000 * g + j))

def checkChunk (g c : ℕ) : Bool := (List.range 100).all (fun j => checkRow (1000 * g + 100 * c + j))

def checkBudgets : Bool :=
  let r := rowAt 80000
  decide (r.compensatorSold < 188 * Q / 100) && decide (r.targetSold < 17 * Q / 100) &&
    decide (r.pairedTurnover < 2984 * Q / 1000)

-- BEGIN D01 RESOURCE KERNEL PROOFS
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem resource_probe_079_8 : checkChunk 79 8 = true := by decide +kernel
#print axioms resource_probe_079_8
set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem resource_probe_079_9 : checkChunk 79 9 = true := by decide +kernel
#print axioms resource_probe_079_9
-- END D01 RESOURCE KERNEL PROOFS

end ResourceCertificate

end OriginalCertificate
end MarketCrash
