import MarketCrash.ScalarSecondJet
import MarketCrash.CrisisQuantile

noncomputable section
namespace MarketCrash
open Set Filter
open scoped Topology

def twoPulseEndpoint (Phi R : ℝ → ℝ) (F r u h : ℝ) : ℝ :=
  R (Phi (F+r*(R (u*h)-F))-u*h)

theorem twoPulseEndpoint_second_jet (Phi R : ℝ → ℝ) (F A B r u : ℝ)
    (hA : A ≠ 0)
    (hR : ScalarSecondJet R 0 F A B)
    (hPhi : ScalarSecondJet Phi F 0 (1/A) (-B/A^3)) :
    ScalarSecondJet (twoPulseEndpoint Phi R F r u) 0 F
      (A*(r-1)*u) (B*(1-r)*u^2) := by
  have jlin : ScalarSecondJet (fun h => u*h) 0 0 u 0 := by
    simpa using scalarSecondJet_affine u 0 0
  have j1 : ScalarSecondJet (fun h => R (u*h)) 0 F (A*u) (B*u^2) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using hR.comp jlin
  have j2 : ScalarSecondJet (fun h => F+r*(R (u*h)-F)) 0 F (r*A*u) (r*B*u^2) := by
    convert (scalarSecondJet_const F 0).add ((j1.sub (scalarSecondJet_const F 0)).scale r) using 1 <;> ring
  have j3 := hPhi.comp j2
  have j4 := j3.sub jlin
  have j4' : ScalarSecondJet (fun h => Phi (F+r*(R (u*h)-F))-u*h) 0 0
      ((r-1)*u) ((B/A)*r*(1-r)*u^2) := by
    convert j4 using 1 <;> dsimp [Function.comp_def]
    · ring
    · field_simp [hA]
      ring
    · field_simp [hA]
      ring
  have j5 := hR.comp j4'
  convert j5 using 1 <;> dsimp [twoPulseEndpoint, Function.comp_def]
  · ring
  · field_simp [hA]
    ring

theorem twoPulseLoss_second_jet (Phi R : ℝ → ℝ) (F A B r u : ℝ)
    (hF : 0 < F) (hA : A ≠ 0)
    (hR : ScalarSecondJet R 0 F A B)
    (hPhi : ScalarSecondJet Phi F 0 (1/A) (-B/A^3)) :
    ScalarSecondJet (fun h => Real.log F-Real.log (twoPulseEndpoint Phi R F r u h)) 0 0
      (A/F*(1-r)*u)
      ((A^2/F^2)*(1-r)^2*u^2-(B/F)*(1-r)*u^2) := by
  have hh := (scalarSecondJet_log_loss F hF).comp
    (twoPulseEndpoint_second_jet Phi R F A B r u hA hR hPhi)
  convert hh using 1 <;> dsimp [Function.comp_def] <;> ring

theorem twoPulseLoss_genuine_second_jet (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y)
    (r u : ℝ) :
    ScalarSecondJet
      (fun h => Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r u h))
      0 0 (g.impact F/F^2*(1-r)*u)
      ((g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r)*u^2) := by
  let A := g.impact F/F
  let B := g.impact F*(F*deriv g.impact F-g.impact F)/F^3
  have hgF := (g.positive F hF).ne'
  have hA : A ≠ 0 := div_ne_zero hgF hF.ne'
  have hjet := local_response_inverse_jets F g hF hg R hR0 hp
  have hjR : ScalarSecondJet R 0 F A B :=
    ⟨hR0,hR3.of_le (by decide),hjet.1,hjet.2⟩
  have hjPhi : ScalarSecondJet (coordinate F g.impact) F 0 (1/A) (-B/A^3) := by
    refine ⟨coordinate_at_benchmark _ _, (coordinate_contDiffAt_four F g hF hg).of_le (by decide), ?_, ?_⟩
    · convert coordinate_hasDerivAt F g hF hF using 1
      dsimp [A]
      field_simp [hF.ne',hgF]
    · convert coordinate_second_derivative F g hF hg using 1
      dsimp [A,B]
      field_simp [hF.ne',hgF]
      ring
  have hh := twoPulseLoss_second_jet (coordinate F g.impact) R F A B r u hF hA hjR hjPhi
  have he1 : A/F*(1-r)*u = g.impact F/F^2*(1-r)*u := by
    dsimp [A]
    rw [div_div,pow_two]
  have he2 : (A^2/F^2)*(1-r)^2*u^2-(B/F)*(1-r)*u^2 =
      (g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r)*u^2 := by
    dsimp [A,B]
    field_simp [hF.ne',hgF]
    ring
  rw [he1,he2] at hh
  exact hh

theorem twoPulseLoss_contDiffAt (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0) (r u : ℝ) :
    ContDiffAt ℝ 3
      (fun h => Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r u h)) 0 := by
  have hlin : ContDiffAt ℝ 3 (fun h : ℝ => u*h) 0 := by fun_prop
  have h1 : ContDiffAt ℝ 3 (fun h => R (u*h)) 0 := by
    have hh : ContDiffAt ℝ 3 R (u*0) := by simpa using hR3
    exact hh.comp 0 hlin
  have h2 : ContDiffAt ℝ 3 (fun h => F+r*(R (u*h)-F)) 0 :=
    contDiffAt_const.add (contDiffAt_const.mul (h1.sub contDiffAt_const))
  have h3 : ContDiffAt ℝ 3 (fun h => coordinate F g.impact (F+r*(R (u*h)-F))) 0 := by
    have hh := (coordinate_contDiffAt_four F g hF hg).of_le (show (3 : WithTop ℕ∞) ≤ 4 by decide)
    have he : F+r*(R (u*(0 : ℝ))-F) = F := by simp [hR0]
    have hh' : ContDiffAt ℝ 3 (coordinate F g.impact) (F+r*(R (u*0)-F)) := by
      rw [he]
      exact hh
    exact hh'.comp 0 h2
  have h4 := h3.sub hlin
  have he : coordinate F g.impact (F+r*(R (u*(0 : ℝ))-F))-u*0 = 0 := by
    simp [hR0,coordinate_at_benchmark]
  have h5 : ContDiffAt ℝ 3 (twoPulseEndpoint (coordinate F g.impact) R F r u) 0 :=
    (he.symm ▸ hR3).comp 0 h4
  apply contDiffAt_const.sub (h5.log ?_)
  simpa [twoPulseEndpoint,hR0,coordinate_at_benchmark] using hF.ne'

theorem ScalarSecondJet.fintype_sum {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (a b c : ι → ℝ) (x : ℝ)
    (hf : ∀ i, ScalarSecondJet (f i) x (a i) (b i) (c i)) :
    ScalarSecondJet (fun t => ∑ i, f i t) x (∑ i,a i) (∑ i,b i) (∑ i,c i) := by
  refine ⟨Finset.sum_congr rfl (fun i _ => (hf i).value),
    ContDiffAt.sum (fun i _ => (hf i).smooth),
    HasDerivAt.sum (u := Finset.univ) (fun i _ => (hf i).first), ?_⟩
  have hev : ∀ᶠ t in nhds x, ∀ i, DifferentiableAt ℝ (f i) t := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hf i).smooth.eventually (by norm_num)).mono fun t ht => ht.differentiableAt (by decide)
  have he : deriv (fun t => ∑ i, f i t) =ᶠ[nhds x] fun t => ∑ i, deriv (f i) t := by
    filter_upwards [hev] with t ht
    exact deriv_sum (fun i _ => ht i)
  exact (HasDerivAt.sum (u := Finset.univ) (fun i _ => (hf i).second)).congr_of_eventuallyEq he

theorem twoPulseLoss_cubic_bound (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y)
    (r u : ℝ) : ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε,
      |(Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r u h)) -
        (g.impact F/F^2*(1-r)*u*h +
          ((g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r)*u^2)/2*h^2)| ≤ C*h^3 := by
  have hj := twoPulseLoss_genuine_second_jet F g hF hg R hR0 hR3 hp r u
  obtain ⟨ε,C,hε,hb⟩ := local_cubic_taylor_bound _ (twoPulseLoss_contDiffAt F g hF hg R hR0 hR3 r u)
  refine ⟨ε,C,hε,?_⟩
  intro h hh
  simpa only [Real.norm_eq_abs,hj.value,hj.first.deriv,hj.second.deriv,zero_add] using hb h hh

theorem twoPulseMean_second_jet {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (g : Response) (hF : 0 < F) (hg : ContDiffAt ℝ 3 g.impact F)
    (R : ℝ → ℝ) (hR0 : R 0 = F) (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y)
    (r : ℝ) (u : ι → ℝ) (hu : ∑ i,u i = 0) :
    ScalarSecondJet (fun h => (1/(Fintype.card ι : ℝ))*
      ∑ i, (Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r (u i) h))) 0 0 0
      (((g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r)) /
        (Fintype.card ι : ℝ) * ∑ i,(u i)^2) := by
  have hj := ScalarSecondJet.fintype_sum
    (fun i h => Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r (u i) h))
    (fun _ => 0) (fun i => g.impact F/F^2*(1-r)*u i)
    (fun i => (g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r)*(u i)^2) 0
    (fun i => twoPulseLoss_genuine_second_jet F g hF hg R hR0 hR3 hp r (u i))
  have hh := hj.scale (1/(Fintype.card ι : ℝ))
  have hlin : (∑ i, g.impact F/F^2*(1-r)*u i) = 0 := by
    rw [← Finset.mul_sum,hu,mul_zero]
  have hquad : (∑ i, (g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r)*(u i)^2) =
      ((g.impact F/F^2)^2*(1-r)*(2-F*deriv g.impact F/g.impact F-r))*(∑ i,(u i)^2) :=
    (Finset.mul_sum _ _ _).symm
  simp only [Finset.sum_const_zero,hlin,hquad,mul_zero] at hh
  convert hh using 1 <;> ring

theorem twoPulseMean_cubic_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (g : Response) (hF : 0 < F) (hg : ContDiffAt ℝ 3 g.impact F)
    (R : ℝ → ℝ) (hR0 : R 0 = F) (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y)
    (r : ℝ) (u : ι → ℝ) (hu : ∑ i,u i = 0) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε,
      |((1/(Fintype.card ι : ℝ))*∑ i,
          (Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r (u i) h))) -
        ((g.impact F/F^2)^2/(2*(Fintype.card ι : ℝ))*(1-r)*
          (2-F*deriv g.impact F/g.impact F-r)*(∑ i,(u i)^2)*h^2)| ≤ C*h^3 := by
  have hj := twoPulseMean_second_jet F g hF hg R hR0 hR3 hp r u hu
  have hc : ContDiffAt ℝ 3 (fun h => (1/(Fintype.card ι : ℝ))*∑ i,
      (Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F r (u i) h))) 0 :=
    contDiffAt_const.mul (ContDiffAt.sum (fun i _ => twoPulseLoss_contDiffAt F g hF hg R hR0 hR3 r (u i)))
  obtain ⟨ε,C,hε,hb⟩ := local_cubic_taylor_bound _ hc
  refine ⟨ε,C,hε,?_⟩
  intro h hh
  have ht := hb h hh
  simp only [hj.value,hj.first.deriv,hj.second.deriv,zero_mul,add_zero,zero_add,Real.norm_eq_abs] at ht
  convert ht using 1 <;> ring

theorem twoPulse_mean_coefficient_pos {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (g : Response) (hF : 0 < F) (r : ℝ) (hr : r < 1)
    (he : r < 2-F*deriv g.impact F/g.impact F)
    (u : ι → ℝ) (hu : ∃ i,u i ≠ 0) :
    0 < (g.impact F/F^2)^2/(2*(Fintype.card ι : ℝ))*(1-r)*
      (2-F*deriv g.impact F/g.impact F-r)*(∑ i,(u i)^2) := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs : 0 < ∑ i,(u i)^2 := by
    obtain ⟨i,hi⟩ := hu
    exact Finset.sum_pos' (fun j _ => sq_nonneg (u j)) ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩
  exact mul_pos (mul_pos (mul_pos (div_pos (sq_pos_of_pos (div_pos (g.positive F hF) (sq_pos_of_pos hF)))
    (mul_pos (by norm_num) hN)) (sub_pos.mpr hr)) (sub_pos.mpr he)) hs

theorem eventual_positive_of_positive_derivative (f : ℝ → ℝ) (L : ℝ)
    (h0 : f 0 = 0) (hd : HasDerivAt f L 0) (hL : 0 < L) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0), 0 < f h := by
  have he := hd.tendsto_slope_zero_right.eventually (Ioi_mem_nhds hL)
  filter_upwards [he,self_mem_nhdsWithin] with h hh hpos
  have hp : 0 < h := hpos
  have hh' : 0 < h⁻¹ * f h := by simpa only [zero_add,h0,sub_zero,smul_eq_mul] using hh
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hp)).mp hh'

theorem eventual_positive_of_cubic_remainder (f : ℝ → ℝ) (Q ε C : ℝ)
    (hQ : 0 < Q) (hε : 0 < ε)
    (hb : ∀ h ∈ Icc 0 ε, |f h-Q*h^2| ≤ C*h^3) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0), 0 < f h := by
  let δ := min ε (Q/(|C|+1))
  have hδ : 0 < δ := lt_min hε (div_pos hQ (by positivity))
  have he : Iio δ ∈ nhdsWithin 0 (Ioi 0) := nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  filter_upwards [he,self_mem_nhdsWithin] with h hh hp
  have hpos : 0 < h := hp
  have hbound : h < Q/(|C|+1) := hh.trans_le (min_le_right _ _)
  have hC : C*h < Q := by
    have hh' := (lt_div_iff₀ (show 0 < |C|+1 by positivity)).mp hbound
    have hc := mul_le_mul_of_nonneg_right (le_abs_self C) hpos.le
    nlinarith
  have hpoly : 0 < Q*h^2-C*h^3 := by
    have ht := mul_pos (sq_pos_of_pos hpos) (sub_pos.mpr hC)
    nlinarith only [ht]
  have ht := (abs_le.mp (hb h ⟨hpos.le,hh.le.trans (min_le_left _ _)⟩)).1
  linarith

theorem crisis_pos_of_mean_pos_and_positive_count {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → ℝ) (k : ℕ) (hk : 0 < k) (hkn : k ≤ Fintype.card ι)
    (hm : 0 < meanLogLoss q)
    (hc : k ≤ (Finset.univ.filter (fun i => 0 < -q i)).card) :
    0 < systemicCrisis q k := by
  classical
  let P := Finset.univ.filter (fun i => 0 < -q i)
  have hne : P.Nonempty := Finset.card_pos.mp (hk.trans_le hc)
  let d := P.inf' hne (fun i => -q i)
  have hd : 0 < d := (Finset.lt_inf'_iff hne).mpr (fun i hi => (Finset.mem_filter.mp hi).2)
  have hsub : P ⊆ Finset.univ.filter (fun i => d ≤ -q i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.inf'_le (f := fun j => -q j) hi⟩
  have hq := (coverageQuantile_threshold_iff q k hk hkn d).mpr (hc.trans (Finset.card_le_card hsub))
  exact lt_min hm (hd.trans_le hq)

def partialCoveragePulseVector {ι : Type*} [Fintype ι] [DecidableEq ι] (hub i : ι) : ℝ :=
  1-(if i = hub then (Fintype.card ι : ℝ) else 0)

theorem partialCoveragePulseVector_zero_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (hub : ι) :
    (∑ i, partialCoveragePulseVector hub i) = 0 := by
  simp [partialCoveragePulseVector,Finset.sum_sub_distrib]

theorem partialCoveragePulseVector_hub_negative {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (hN : 2 ≤ Fintype.card ι) : partialCoveragePulseVector hub hub < 0 := by
  have hh : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  simp only [partialCoveragePulseVector,ite_true]
  linarith

theorem twoPulse_scalar_crisis_positive_of_direction {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F : ℝ) (g : Response) (hF : 0 < F) (hg : ContDiffAt ℝ 3 g.impact F)
    (R : ℝ → ℝ) (hR0 : R 0 = F) (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y)
    (r : ℝ) (hr : r < 1) (he : r < 2-F*deriv g.impact F/g.impact F)
    (u : ι → ℝ) (hu : ∑ i,u i = 0) (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card ι)
    (hcount : k ≤ (Finset.univ.filter (fun i => 0 < u i)).card) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0),
      (∀ i, 0 < twoPulseEndpoint (coordinate F g.impact) R F r (u i) h) ∧
      0 < systemicCrisis (logPriceFromBenchmark F (fun i =>
        twoPulseEndpoint (coordinate F g.impact) R F r (u i) h)) k := by
  classical
  let P := fun h i => twoPulseEndpoint (coordinate F g.impact) R F r (u i) h
  let L := fun h i => Real.log F-Real.log (P h i)
  obtain ⟨ε,C,hε,hb⟩ := twoPulseMean_cubic_bound F g hF hg R hR0 hR3 hp r u hu
  have hnonzero : ∃ i,u i ≠ 0 := by
    obtain ⟨i,hi⟩ := Finset.card_pos.mp (hk.trans_le hcount)
    exact ⟨i,(Finset.mem_filter.mp hi).2.ne'⟩
  have hQ := twoPulse_mean_coefficient_pos F g hF r hr he u hnonzero
  have hm := eventual_positive_of_cubic_remainder _ _ ε C hQ hε hb
  have hi : ∀ᶠ h in nhdsWithin 0 (Ioi 0), ∀ i, 0 < u i → 0 < L h i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hih : 0 < u i
    · have hj := twoPulseLoss_genuine_second_jet F g hF hg R hR0 hR3 hp r (u i)
      have hc : 0 < g.impact F/F^2*(1-r)*u i := by
        exact mul_pos (mul_pos (div_pos (g.positive F hF) (sq_pos_of_pos hF)) (sub_pos.mpr hr)) hih
      exact (eventual_positive_of_positive_derivative _ _ hj.value hj.first hc).mono (fun _ hh _ => hh)
    · exact Filter.Eventually.of_forall (fun _ hn => False.elim (hih hn))
  have hprices : ∀ᶠ h in nhdsWithin 0 (Ioi 0), ∀ i, 0 < P h i := by
    apply Filter.eventually_all.mpr
    intro i
    have hlin : ContinuousAt (fun h : ℝ => u i*h) 0 := by fun_prop
    have h1 : ContinuousAt (fun h => R (u i*h)) 0 := by
      have hh : ContinuousAt R (u i*0) := by simpa using hR3.continuousAt
      exact hh.comp hlin
    have h2 : ContinuousAt (fun h => F+r*(R (u i*h)-F)) 0 :=
      continuousAt_const.add (continuousAt_const.mul (h1.sub continuousAt_const))
    have h3 : ContinuousAt (fun h => coordinate F g.impact (F+r*(R (u i*h)-F))) 0 := by
      have hh : ContinuousAt (coordinate F g.impact) (F+r*(R (u i*0)-F)) := by
        simpa only [mul_zero,hR0,sub_self,mul_zero,add_zero] using
          (coordinate_hasDerivAt F g hF hF).continuousAt
      exact hh.comp (f := fun h => F+r*(R (u i*h)-F)) h2
    have h4 := h3.sub hlin
    have hc : ContinuousAt (P · i) 0 := by
      have hh : ContinuousAt R (coordinate F g.impact (F+r*(R (u i*0)-F))-u i*0) := by
        simpa only [mul_zero,hR0,sub_self,mul_zero,add_zero,coordinate_at_benchmark,sub_zero] using hR3.continuousAt
      exact hh.comp (f := fun h => coordinate F g.impact (F+r*(R (u i*h)-F))-u i*h) h4
    have hv : P 0 i = F := by simp [P,twoPulseEndpoint,hR0,coordinate_at_benchmark]
    have hvpos : 0 < P 0 i := by rw [hv]; exact hF
    exact (hc.eventually (Ioi_mem_nhds hvpos)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hm,hi,hprices] with h hmean hind hpos
  refine ⟨hpos,?_⟩
  have hlog : ∀ i, -logPriceFromBenchmark F (P h) i = L h i := by
    intro i
    dsimp [L,logPriceFromBenchmark]
    rw [Real.log_div (hpos i).ne' hF.ne']
    ring
  have hm' : 0 < meanLogLoss (logPriceFromBenchmark F (P h)) := by
    have heq : meanLogLoss (logPriceFromBenchmark F (P h)) =
        (1/(Fintype.card ι : ℝ))*∑ i,L h i := by
      unfold meanLogLoss
      rw [← Finset.sum_neg_distrib]
      simp_rw [hlog]
      ring
    rw [heq]
    exact hmean
  apply crisis_pos_of_mean_pos_and_positive_count _ k hk hkn.le hm'
  have hsub : Finset.univ.filter (fun i => 0 < u i) ⊆ Finset.univ.filter (fun i => 0 < -logPriceFromBenchmark F (P h) i) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hlog]; exact hind i (Finset.mem_filter.mp hi).2⟩
  exact hcount.trans (Finset.card_le_card hsub)

end MarketCrash
