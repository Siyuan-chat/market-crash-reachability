import MarketCrash.ResponseFamilies
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace MarketCrash

def sharpHighDirection (n b : ℝ) : ℝ := Real.sqrt (1-(n-1)*b^2)
def sharpDirectionSum (n b : ℝ) : ℝ := sharpHighDirection n b+(n-1)*b
def sharpRadius (F rho n b t : ℝ) : ℝ :=
  F*(sharpDirectionSum n b+(Real.sqrt n-sharpDirectionSum n b)*Real.exp (-rho*t))

theorem sharp_direction_geometry (n b : ℝ) (hn : 2 ≤ n) (hb : 0 < b)
    (hnb : n*b^2 < 1) :
    b < sharpHighDirection n b ∧
    (sharpHighDirection n b)^2+(n-1)*b^2 = 1 ∧
    (sharpHighDirection n b+b)*sharpDirectionSum n b = 1+n*sharpHighDirection n b*b ∧
    1 < sharpDirectionSum n b ∧ sharpDirectionSum n b < Real.sqrt n := by
  have hp : 0 < 1-(n-1)*b^2 := by nlinarith [sq_nonneg b]
  have ha : 0 < sharpHighDirection n b := Real.sqrt_pos.mpr hp
  have hsq : (sharpHighDirection n b)^2 = 1-(n-1)*b^2 := Real.sq_sqrt hp.le
  have hab : b < sharpHighDirection n b := by nlinarith
  have hn1 : 0 < n-1 := by linarith
  have hn2 : 0 ≤ n-2 := by linarith
  have hH : 0 < sharpDirectionSum n b := by dsimp [sharpDirectionSum];positivity
  have hid : (sharpHighDirection n b+b)*sharpDirectionSum n b = 1+n*sharpHighDirection n b*b := by
    dsimp [sharpDirectionSum]
    nlinarith
  have hlo : 1 < sharpDirectionSum n b := by
    have hprod : 0 < 2*(n-1)*sharpHighDirection n b*b := by positivity
    have hrest : 0 ≤ (n-1)*(n-2)*b^2 := by positivity
    dsimp [sharpDirectionSum] at hH ⊢
    nlinarith
  have hhi : sharpDirectionSum n b < Real.sqrt n := by
    have hs : (Real.sqrt n)^2 = n := Real.sq_sqrt (by linarith)
    have hr : 0 ≤ Real.sqrt n := Real.sqrt_nonneg n
    have hgap : 0 < (n-1)*(sharpHighDirection n b-b)^2 :=
      mul_pos (by linarith) (sq_pos_of_pos (sub_pos.mpr hab))
    dsimp [sharpDirectionSum] at hH ⊢
    nlinarith
  exact ⟨hab,by linarith,hid,hlo,hhi⟩

theorem sharpRadius_derivative (F rho n b t : ℝ) :
    HasDerivAt (sharpRadius F rho n b)
      (-rho*(sharpRadius F rho n b t-F*sharpDirectionSum n b)) t := by
  have hh := ((((hasDerivAt_id t).const_mul (-rho)).exp).const_mul
    (Real.sqrt n-sharpDirectionSum n b) |>.const_add (sharpDirectionSum n b)).const_mul F
  convert hh using 1 <;> dsimp [sharpRadius] <;> ring

theorem radial_dollar_rate_sum_zero {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (H F rho eta R : ℝ) (hη : eta ≠ 0)
    (hnorm : ∑ i, (u i)^2 = 1) (hH : ∑ i, u i = H) :
    (∑ i, (u i*R)/eta*(u i*(-rho*(R-F*H))+rho*(u i*R-F))) = 0 := by
  have he : ∀ i, (u i*R)/eta*(u i*(-rho*(R-F*H))+rho*(u i*R-F)) =
      (rho*F*H*R/eta)*(u i)^2-(rho*F*R/eta)*u i := by intro i;ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.mul_sum,hnorm,hH]
  ring

theorem sharp_weight_positive (F rho n b t : ℝ) (hF : 0 < F) (hρ : 0 ≤ rho)
    (hn : 2 ≤ n) (hb : 0 < b) (hnb : n*b^2 < 1) (ht : 0 ≤ t) :
    0 < (sharpHighDirection n b-b)*sharpRadius F rho n b t*
      ((sharpHighDirection n b+b)*sharpRadius F rho n b t-F) := by
  obtain ⟨hab,hsq,hid,hH1,hHn⟩ := sharp_direction_geometry n b hn hb hnb
  have ha : 0 < sharpHighDirection n b := hb.trans hab
  have hR : F*sharpDirectionSum n b ≤ sharpRadius F rho n b t := by
    dsimp [sharpRadius]
    nlinarith [mul_nonneg (sub_pos.mpr hHn).le (Real.exp_pos (-rho*t)).le]
  have hRp : 0 < sharpRadius F rho n b t := lt_of_lt_of_le (mul_pos hF (by linarith)) hR
  have hmult : 1 < (sharpHighDirection n b+b)*sharpDirectionSum n b := by
    rw [hid]
    have hh : 0 < n*sharpHighDirection n b*b := by positivity
    linarith
  have hlast : 0 < (sharpHighDirection n b+b)*sharpRadius F rho n b t-F := by
    have hh := mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ sharpHighDirection n b+b)
    nlinarith [mul_pos hF (sub_pos.mpr hmult)]
  exact mul_pos (mul_pos (sub_pos.mpr hab) hRp) hlast

theorem sharpDirectionSum_surjective (n H : ℝ) (hn : 2 ≤ n)
    (hH0 : 1 < H) (hH1 : H < Real.sqrt n) :
    ∃ b : ℝ, 0 < b ∧ b < 1/Real.sqrt n ∧ sharpDirectionSum n b = H := by
  have hn0 : 0 < n := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hs2 : (Real.sqrt n)^2 = n := Real.sq_sqrt hn0.le
  have hb : 0 < 1/Real.sqrt n := one_div_pos.mpr hs
  have hc : ContinuousOn (sharpDirectionSum n) (Set.Icc 0 (1/Real.sqrt n)) := by
    change ContinuousOn (fun b : ℝ => Real.sqrt (1-(n-1)*b^2)+(n-1)*b) _
    fun_prop
  have hzero : sharpDirectionSum n 0 = 1 := by simp [sharpDirectionSum,sharpHighDirection]
  have hend : sharpDirectionSum n (1/Real.sqrt n) = Real.sqrt n := by
    have he : 1-(n-1)*(1/Real.sqrt n)^2 = (1/Real.sqrt n)^2 := by
      field_simp [hs.ne'] <;> nlinarith
    dsimp [sharpDirectionSum,sharpHighDirection]
    rw [he,Real.sqrt_sq hb.le]
    field_simp [hs.ne'] <;> nlinarith
  have hh := intermediate_value_Icc hb.le hc
  obtain ⟨b,hbmem,he⟩ := hh (by rw [hzero,hend];exact ⟨hH0.le,hH1.le⟩)
  refine ⟨b,?_,?_,he⟩
  · have hne : b ≠ 0 := by intro hz;subst b;rw [hzero] at he;linarith
    exact lt_of_le_of_ne hbmem.1 hne.symm
  · have hne : b ≠ 1/Real.sqrt n := by intro hz;subst b;rw [hend] at he;linarith
    exact lt_of_le_of_ne hbmem.2 hne

theorem sharp_common_ratio_parameter (n r q : ℝ) (hn : 2 ≤ n)
    (hr0 : 0 < r) (hr1 : r < 1)
    (hq0 : (1+(Real.sqrt n-1)*r)/Real.sqrt n < q) (hq1 : q < 1) :
    ∃ b : ℝ, 0 < b ∧ b < 1/Real.sqrt n ∧
      (sharpDirectionSum n b+(Real.sqrt n-sharpDirectionSum n b)*r)/Real.sqrt n = q := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hd : 0 < 1-r := sub_pos.mpr hr1
  let H := (Real.sqrt n*q-Real.sqrt n*r)/(1-r)
  have hH0 : 1 < H := by
    apply (lt_div_iff₀ hd).mpr
    have hh := (div_lt_iff₀ hs).mp hq0
    nlinarith
  have hH1 : H < Real.sqrt n := by
    apply (div_lt_iff₀ hd).mpr
    nlinarith [mul_lt_mul_of_pos_left hq1 hs]
  obtain ⟨b,hb0,hb1,hHb⟩ := sharpDirectionSum_surjective n H hn hH0 hH1
  refine ⟨b,hb0,hb1,?_⟩
  rw [hHb]
  dsimp [H]
  field_simp [hs.ne',hd.ne'] <;> ring

def sharpCriticalLoss (n rho T : ℝ) : ℝ :=
  Real.log (Real.sqrt n/(1+(Real.sqrt n-1)*Real.exp (-rho*T)))

theorem sharp_delta_parameter (n rho T delta : ℝ) (hn : 2 ≤ n)
    (hρ : 0 < rho) (hT : 0 < T) (hd : 0 < delta)
    (hcrit : delta < sharpCriticalLoss n rho T) :
    ∃ b : ℝ, 0 < b ∧ n*b^2 < 1 ∧
      (sharpDirectionSum n b+(Real.sqrt n-sharpDirectionSum n b)*Real.exp (-rho*T))/Real.sqrt n =
        Real.exp (-delta) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have hs2 : (Real.sqrt n)^2 = n := Real.sq_sqrt (by linarith)
  have hs1 : 1 < Real.sqrt n := by nlinarith
  let r := Real.exp (-rho*T)
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  let A := 1+(Real.sqrt n-1)*r
  have hsd : 0 < Real.sqrt n-1 := sub_pos.mpr hs1
  have hA : 0 < A := by dsimp [A];positivity
  have he : Real.exp delta < Real.sqrt n/A := by
    change delta < Real.log (Real.sqrt n/A) at hcrit
    have hh := Real.exp_lt_exp.mpr hcrit
    simpa only [Real.exp_log (div_pos hs hA)] using hh
  have hex : Real.exp delta*Real.exp (-delta) = 1 := by rw [← Real.exp_add];simp
  have hratio : A/Real.sqrt n < Real.exp (-delta) := by
    apply (div_lt_iff₀ hs).mpr
    have hh := mul_lt_mul_of_pos_right ((lt_div_iff₀ hA).mp he) (Real.exp_pos (-delta))
    calc
      A = (Real.exp delta*A)*Real.exp (-delta) := by rw [mul_assoc,mul_comm A,← mul_assoc,hex];ring
      _ < Real.sqrt n*Real.exp (-delta) := hh
      _ = Real.exp (-delta)*Real.sqrt n := by ring
  obtain ⟨b,hb0,hb1,hend⟩ := sharp_common_ratio_parameter n r (Real.exp (-delta)) hn hr0 hr1
    hratio (Real.exp_lt_one_iff.mpr (by linarith))
  refine ⟨b,hb0,?_,hend⟩
  have hh : b*Real.sqrt n < 1 := (lt_div_iff₀ hs).mp hb1
  have hp : 0 < b*Real.sqrt n := mul_pos hb0 hs
  have hsq : (b*Real.sqrt n)^2 < 1 := by nlinarith
  rw [mul_pow,hs2] at hsq
  simpa only [mul_comm] using hsq

end MarketCrash
