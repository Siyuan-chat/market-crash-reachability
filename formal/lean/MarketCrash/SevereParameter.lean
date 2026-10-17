import MarketCrash.SharpConstruction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
namespace MarketCrash
open Set MeasureTheory

def severeRadius (F rho n H t : ℝ) : ℝ :=
  F*(H+(Real.sqrt n-H)*Real.exp (-rho*t))

def severeRecoveryPrimitive (F rho n H b t : ℝ) : ℝ :=
  F^2*((b^2*H^2-b*H)*t+
    (2*b^2*H*(Real.sqrt n-H)-b*(Real.sqrt n-H))*(1-Real.exp (-rho*t))/rho+
    b^2*(Real.sqrt n-H)^2*(1-Real.exp (-2*rho*t))/(2*rho))

theorem severeRecoveryPrimitive_derivative (F rho n H b t : ℝ) (hr : rho ≠ 0) :
    HasDerivAt (severeRecoveryPrimitive F rho n H b)
      ((b*severeRadius F rho n H t)*(b*severeRadius F rho n H t-F)) t := by
  have he := (((hasDerivAt_id t).const_mul (-rho)).exp)
  have he2 := (((hasDerivAt_id t).const_mul (-2*rho)).exp)
  have hh := (((hasDerivAt_id t).const_mul (b^2*H^2-b*H)).add
    (((he.const_sub 1).const_mul (2*b^2*H*(Real.sqrt n-H)-b*(Real.sqrt n-H))).div_const rho) |>.add
    (((he2.const_sub 1).const_mul (b^2*(Real.sqrt n-H)^2)).div_const (2*rho))).const_mul (F^2)
  convert hh using 1
  dsimp [severeRadius]
  have hexp : Real.exp (-2*rho*t) = (Real.exp (-rho*t))^2 := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp]
  field_simp [hr]
  <;> ring

theorem severeRecoveryPrimitive_zero (F rho n H b : ℝ) :
    severeRecoveryPrimitive F rho n H b 0 = 0 := by
  simp [severeRecoveryPrimitive]

theorem severe_recovery_integral (F rho n H b T : ℝ) (hr : rho ≠ 0) :
    (∫ t in (0:ℝ)..T, (b*severeRadius F rho n H t)*(b*severeRadius F rho n H t-F)) =
      severeRecoveryPrimitive F rho n H b T := by
  have hc : Continuous (fun t => (b*severeRadius F rho n H t)*(b*severeRadius F rho n H t-F)) := by
    unfold severeRadius
    fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => severeRecoveryPrimitive_derivative F rho n H b t hr) (hc.intervalIntegrable 0 T)
  simpa only [severeRecoveryPrimitive_zero,sub_zero] using hh

def severeCompensatorLedger (F rho eta n H b T eps : ℝ) : ℝ :=
  ((severeRadius F rho n H T)^2-(n-1)*eps^2-F^2)/(2*eta)+
    (rho/eta)*severeRecoveryPrimitive F rho n H b T

theorem severe_compensator_continuous (F rho eta n T eps : ℝ) (H : ℝ → ℝ)
    (hH : Continuous H) : Continuous (fun b => severeCompensatorLedger F rho eta n (H b) b T eps) := by
  unfold severeCompensatorLedger severeRadius severeRecoveryPrimitive
  fun_prop

theorem severe_radius_bounds (F rho n H t : ℝ) (hF : 0 < F) (hr : 0 ≤ rho)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (ht : 0 ≤ t) :
    F*H ≤ severeRadius F rho n H t ∧ severeRadius F rho n H t ≤ F*Real.sqrt n := by
  have he0 := (Real.exp_pos (-rho*t)).le
  have he1 : Real.exp (-rho*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hD : 0 ≤ Real.sqrt n-H := sub_nonneg.mpr hHn
  have hlow := mul_nonneg hD he0
  have hhigh := mul_le_mul_of_nonneg_left he1 hD
  dsimp [severeRadius]
  constructor <;> nlinarith

set_option maxHeartbeats 800000 in
theorem severe_compensator_negative_eventually (F rho eta n H b : ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hn : 1 ≤ n)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (hb : 0 < b) (hbH : b*H < 1) :
    ∃ T0 : ℝ, 0 < T0 ∧ ∀ T : ℝ, T0 ≤ T → ∀ eps : ℝ,
      severeCompensatorLedger F rho eta n H b T eps < 0 := by
  let D := Real.sqrt n-H
  let c := b*H*(1-b*H)
  let K := n/2+2*b^2*H*D+b^2*D^2/2
  have hD : 0 ≤ D := sub_nonneg.mpr hHn
  have hc : 0 < c := mul_pos (mul_pos hb hH) (sub_pos.mpr hbH)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let T0 := 1+K/(rho*c)
  have hT0 : 0 < T0 := by dsimp [T0]; positivity
  refine ⟨T0,hT0,?_⟩
  intro T hT eps
  have ht : 0 ≤ T := hT0.le.trans hT
  let E := Real.exp (-rho*T)
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hE2 : E^2 ≤ 1 := by nlinarith
  have hA : (2*b^2*H*D-b*D)*(1-E) ≤ 2*b^2*H*D := by
    have ha : 0 ≤ 2*b^2*H*D := by positivity
    have h1 := mul_le_mul_of_nonneg_right (show 2*b^2*H*D-b*D ≤ 2*b^2*H*D by linarith [mul_nonneg hb.le hD])
      (sub_nonneg.mpr hE1)
    have h2 := mul_le_mul_of_nonneg_left (show 1-E ≤ 1 by linarith) ha
    nlinarith
  have hB : b^2*D^2*(1-E^2) ≤ b^2*D^2 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg b) (sq_nonneg D)) (sq_nonneg E)]
  have hRad := severe_radius_bounds F rho n H T hF hr.le hH hHn ht
  have hRp : 0 ≤ severeRadius F rho n H T := (mul_pos hF hH).le.trans hRad.1
  have hNs : (Real.sqrt n)^2 = n := Real.sq_sqrt (by linarith)
  have hRsq : (severeRadius F rho n H T)^2 ≤ F^2*n := by
    nlinarith [sq_nonneg (F*Real.sqrt n-severeRadius F rho n H T)]
  have hTbound : K-rho*c*T < 0 := by
    have hh : K/(rho*c)+1 ≤ T := by simpa only [T0,add_comm] using hT
    have hmul := mul_le_mul_of_nonneg_left hh (mul_pos hr hc).le
    have heq : (rho*c)*(K/(rho*c)+1) = K+rho*c := by field_simp <;> ring
    rw [heq] at hmul
    nlinarith [mul_pos hr hc]
  have hExp : Real.exp (-2*rho*T) = E^2 := by
    dsimp [E]; rw [← Real.exp_nat_mul]; congr 1; ring
  have hEq : severeCompensatorLedger F rho eta n H b T eps =
      ((severeRadius F rho n H T)^2-(n-1)*eps^2-F^2)/(2*eta)+
      (F^2/eta)*(-rho*c*T+(2*b^2*H*D-b*D)*(1-E)+b^2*D^2*(1-E^2)/2) := by
    dsimp [severeCompensatorLedger,severeRecoveryPrimitive,c,D,E]
    rw [hExp]
    dsimp [E]
    field_simp
    <;> ring
  rw [hEq]
  have hcost : 0 < F^2/eta := div_pos (sq_pos_of_pos hF) he
  have hnon : 0 ≤ (n-1)*eps^2 := mul_nonneg (by linarith) (sq_nonneg eps)
  have hledger : ((severeRadius F rho n H T)^2-(n-1)*eps^2-F^2)/(2*eta) ≤ (F^2/eta)*(n/2) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*eta)).mpr
    have hh : F^2/eta*(n/2)*(2*eta) = F^2*n := by field_simp;ring
    rw [hh]
    nlinarith [sq_nonneg F]
  have hsum : -rho*c*T+(2*b^2*H*D-b*D)*(1-E)+b^2*D^2*(1-E^2)/2 ≤
      -rho*c*T+2*b^2*H*D+b^2*D^2/2 :=
    add_le_add (add_le_add_left hA _) (div_le_div_of_nonneg_right hB (by norm_num))
  have hlast : n/2+(-rho*c*T+2*b^2*H*D+b^2*D^2/2) < 0 := by
    dsimp [K] at hTbound
    linarith
  calc
    _ ≤ (F^2/eta)*(n/2)+(F^2/eta)*(-rho*c*T+2*b^2*H*D+b^2*D^2/2) :=
      add_le_add hledger (mul_le_mul_of_nonneg_left hsum hcost.le)
    _ = (F^2/eta)*(n/2+(-rho*c*T+2*b^2*H*D+b^2*D^2/2)) := by ring
    _ < 0 := mul_neg_of_pos_of_neg hcost hlast

def severeHigh (n c b : ℝ) : ℝ := Real.sqrt (1-b^2-(n-2)*c^2)
def severeDirectionSum (n c b : ℝ) : ℝ := severeHigh n c b+(n-2)*c+b

set_option maxHeartbeats 800000 in
theorem severe_direction_geometry (n : ℝ) (hn : 2 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ c < 1/5 ∧ c*n = 1/100 ∧ c ≤ 1/200 ∧ ∀ b ∈ Icc (0:ℝ) (1/5),
      b < severeHigh n c b ∧
      (severeHigh n c b)^2+(n-2)*c^2+b^2 = 1 ∧
      0 < severeDirectionSum n c b ∧ severeDirectionSum n c b ≤ Real.sqrt n ∧
      b*severeDirectionSum n c b < 1 ∧
      (severeHigh n c b+c)*severeDirectionSum n c b > 1 := by
  let c := 1/(100*n)
  have hn0 : 0 < n := by linarith
  have hc : 0 < c := by dsimp [c]; positivity
  have hcn : c*n = 1/100 := by dsimp [c]; field_simp; ring
  have hcsmall : c ≤ 1/200 := by
    dsimp [c]
    apply (div_le_iff₀ (by positivity : 0 < 100*n)).mpr
    nlinarith
  have hD : 0 ≤ (n-2)*c := mul_nonneg (by linarith) hc.le
  have hDb : (n-2)*c ≤ 1/100 := by nlinarith
  refine ⟨c,hc,by linarith,hcn,hcsmall,?_⟩
  intro b hb
  have hb0 := hb.1
  have hb1 := hb.2
  have hbq : b^2 ≤ 1/25 := by nlinarith
  have hcq : 0 ≤ (n-2)*c^2 := mul_nonneg (by linarith) (sq_nonneg c)
  have hcqb : (n-2)*c^2 ≤ 1/20000 := by
    nlinarith only [mul_le_mul_of_nonneg_right hDb hc.le,hcsmall]
  have hp : 0 < 1-b^2-(n-2)*c^2 := by linarith
  have ha : 0 < severeHigh n c b := Real.sqrt_pos.mpr hp
  have haq : (severeHigh n c b)^2 = 1-b^2-(n-2)*c^2 := Real.sq_sqrt hp.le
  have ha1 : severeHigh n c b ≤ 1 := by nlinarith
  have ha9 : 9/10 < severeHigh n c b := by nlinarith
  have hH : 0 < severeDirectionSum n c b := by dsimp [severeDirectionSum]; linarith
  have hHq : (severeDirectionSum n c b)^2 ≤ n := by
    dsimp [severeDirectionSum]
    have hs := add_nonneg (add_nonneg (sq_nonneg (severeHigh n c b-b))
      (mul_nonneg (by linarith : 0 ≤ n-2) (sq_nonneg (severeHigh n c b-c))))
      (mul_nonneg (by linarith : 0 ≤ n-2) (sq_nonneg (b-c)))
    nlinarith only [hs,haq]
  have hHs : severeDirectionSum n c b ≤ Real.sqrt n := by
    have hs := Real.sq_sqrt hn0.le
    nlinarith [Real.sqrt_nonneg n]
  have hHb : severeDirectionSum n c b ≤ 121/100 := by
    dsimp [severeDirectionSum]; linarith
  have hprod : b*severeDirectionSum n c b < 1 := by
    nlinarith [mul_le_mul_of_nonneg_left hHb hb0]
  have hid : (severeHigh n c b+c)*severeDirectionSum n c b =
      1+b*(severeHigh n c b-b)+(n-1)*severeHigh n c b*c+b*c := by
    dsimp [severeDirectionSum]
    nlinarith only [haq]
  have hpos : 0 < (n-1)*severeHigh n c b*c :=
    mul_pos (mul_pos (by linarith) ha) hc
  have hbc : 0 ≤ b*(severeHigh n c b-b) := mul_nonneg hb0 (by linarith)
  exact ⟨by linarith,by linarith,hH,hHs,hprod,by nlinarith [mul_nonneg hb0 hc.le]⟩

theorem severe_directionSum_continuous (n c : ℝ) : Continuous (severeDirectionSum n c) := by
  unfold severeDirectionSum severeHigh
  fun_prop

theorem severe_radius_strict_at_zero (F rho n H T : ℝ) (hF : 0 < F)
    (hH : 1 ≤ H) (hHn : H < Real.sqrt n) : F < severeRadius F rho n H T := by
  have hp := mul_pos (sub_pos.mpr hHn) (Real.exp_pos (-rho*T))
  dsimp [severeRadius]
  nlinarith

set_option maxHeartbeats 500000 in
theorem severe_compensator_root (F rho eta n beta : ℝ) (H : ℝ → ℝ)
    (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) (hn : 2 ≤ n) (hbeta : 0 < beta)
    (hHC : Continuous H) (hH0 : 1 ≤ H 0) (hH0n : H 0 < Real.sqrt n)
    (hHb : 0 < H beta) (hHbn : H beta ≤ Real.sqrt n) (hprod : beta*H beta < 1) :
    ∃ T eps0 : ℝ, 0 < T ∧ 0 < eps0 ∧ ∀ eps : ℝ, 0 ≤ eps → eps < eps0 →
      ∃ b ∈ Ioo (0:ℝ) beta, severeCompensatorLedger F rho eta n (H b) b T eps = 0 := by
  obtain ⟨T,hT,hneg⟩ := severe_compensator_negative_eventually F rho eta n (H beta) beta
    hF hr he (by linarith) hHb hHbn hbeta hprod
  have hR := severe_radius_strict_at_zero F rho n (H 0) T hF hH0 hH0n
  let Q := (severeRadius F rho n (H 0) T)^2-F^2
  have hQ : 0 < Q := by dsimp [Q]; nlinarith
  let eps0 := min 1 (Q/(2*(n-1)))
  have hn1 : 0 < n-1 := by linarith
  have heps0 : 0 < eps0 := by dsimp [eps0]; positivity
  refine ⟨T,eps0,hT,heps0,?_⟩
  intro eps heps hepsb
  have heps1 : eps < 1 := (lt_min_iff.mp hepsb).1
  have hepsQ : eps < Q/(2*(n-1)) := (lt_min_iff.mp hepsb).2
  have hterm : (n-1)*eps^2 < Q := by
    have hh := (lt_div_iff₀ (by linarith : 0 < 2*(n-1))).mp hepsQ
    have hsq : eps^2 ≤ eps := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ n-1)]
  have hpos : 0 < severeCompensatorLedger F rho eta n (H 0) 0 T eps := by
    simp only [severeCompensatorLedger,severeRecoveryPrimitive,zero_pow (by decide : 2 ≠ 0),
      zero_mul,sub_zero,mul_zero,zero_div,add_zero,zero_add]
    apply div_pos _ (by positivity)
    dsimp [Q] at hterm
    linarith
  have hneg' := hneg T le_rfl eps
  have hcont : ContinuousOn (fun b => severeCompensatorLedger F rho eta n (H b) b T eps) (Icc 0 beta) :=
    (severe_compensator_continuous F rho eta n T eps H hHC).continuousOn
  have hbetween : (0:ℝ) ∈ Icc
      (severeCompensatorLedger F rho eta n (H beta) beta T eps)
      (severeCompensatorLedger F rho eta n (H 0) 0 T eps) := ⟨hneg'.le,hpos.le⟩
  obtain ⟨b,hb,hzero⟩ := intermediate_value_Icc' hbeta.le hcont hbetween
  refine ⟨b,⟨?_,?_⟩,hzero⟩
  · exact lt_of_le_of_ne hb.1 (by intro hz;subst b; linarith)
  · exact lt_of_le_of_ne hb.2 (by intro hz;subst b; linarith)

theorem severe_initial_direction_sum (n c : ℝ) (hn : 2 ≤ n) (hc : 0 < c)
    (hcsmall : c ≤ 1/200) (hcn : c*n = 1/100) :
    1 ≤ severeDirectionSum n c 0 ∧ severeDirectionSum n c 0 < Real.sqrt n := by
  have hD : 0 ≤ (n-2)*c := mul_nonneg (by linarith) hc.le
  have hDb : (n-2)*c ≤ 1/100 := by nlinarith
  have hcc : (n-2)*c^2 ≤ 1/20000 := by
    nlinarith only [mul_le_mul_of_nonneg_right hDb hc.le,hcsmall]
  have hp : 0 < 1-(n-2)*c^2 := by linarith
  have ha : 0 < severeHigh n c 0 := by simpa [severeHigh] using Real.sqrt_pos.mpr hp
  have haq : (severeHigh n c 0)^2 = 1-(n-2)*c^2 := by
    simpa [severeHigh] using Real.sq_sqrt hp.le
  have ha9 : 9/10 < severeHigh n c 0 := by nlinarith
  have ha1 : severeHigh n c 0 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ n-2) (sq_nonneg c)]
  have hH : 0 < severeDirectionSum n c 0 := by dsimp [severeDirectionSum]; linarith
  have hHs : severeDirectionSum n c 0 ≤ 101/100 := by dsimp [severeDirectionSum]; linarith
  have hHq : 1 ≤ (severeDirectionSum n c 0)^2 := by
    dsimp [severeDirectionSum]
    have hh : 0 ≤ (n-2)*c*(2*severeHigh n c 0-c) := mul_nonneg hD (by linarith)
    nlinarith only [haq,hh,sq_nonneg ((n-2)*c)]
  have hs : (Real.sqrt n)^2 = n := Real.sq_sqrt (by linarith)
  have hs0 := Real.sqrt_nonneg n
  exact ⟨by nlinarith,by nlinarith⟩

theorem severe_parameter_family (F rho eta n : ℝ) (hF : 0 < F) (hr : 0 < rho)
    (he : 0 < eta) (hn : 2 ≤ n) :
    ∃ c T eps0 : ℝ, 0 < c ∧ c*n = 1/100 ∧ c ≤ 1/200 ∧ 0 < T ∧ 0 < eps0 ∧
      ∀ eps : ℝ, 0 ≤ eps → eps < eps0 →
        ∃ b ∈ Ioo (0:ℝ) (1/5),
          severeCompensatorLedger F rho eta n (severeDirectionSum n c b) b T eps = 0 ∧
          b < severeHigh n c b ∧
          (severeHigh n c b)^2+(n-2)*c^2+b^2 = 1 ∧
          0 < severeDirectionSum n c b ∧ severeDirectionSum n c b ≤ Real.sqrt n ∧
          (severeHigh n c b+c)*severeDirectionSum n c b > 1 := by
  obtain ⟨c,hc,hcb,hcn,hcs,hgeom⟩ := severe_direction_geometry n hn
  obtain ⟨hH0,hH0n⟩ := severe_initial_direction_sum n c hn hc hcs hcn
  obtain ⟨_,_,hHb,hHbn,hbH,_⟩ := hgeom (1/5) ⟨by norm_num,le_rfl⟩
  obtain ⟨T,eps0,hT,heps,hroot⟩ := severe_compensator_root F rho eta n (1/5)
    (severeDirectionSum n c) hF hr he hn (by norm_num) (severe_directionSum_continuous n c)
    hH0 hH0n hHb hHbn hbH
  refine ⟨c,T,eps0,hc,hcn,hcs,hT,heps,?_⟩
  intro eps hep hepb
  obtain ⟨b,hb,hzero⟩ := hroot eps hep hepb
  obtain ⟨hab,hnorm,hH,hHn,hbH,hW⟩ := hgeom b ⟨hb.1.le,hb.2.le⟩
  exact ⟨b,hb,hzero,hab,hnorm,hH,hHn,hW⟩

end MarketCrash
