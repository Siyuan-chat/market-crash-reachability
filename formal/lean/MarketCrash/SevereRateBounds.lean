import MarketCrash.SevereRadial
import MarketCrash.SevereResources
import MarketCrash.SharpTransportResources

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

theorem severe_radial_signed_rate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hr : 0 ≤ rho) (he : 0 < eta)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (hun : ∑ i, (u i)^2 = 1) (huH : ∑ i, u i = H) (t : ℝ) (ht : t ∈ Icc 0 T) (i : ι) :
    tradingInput (pairedMatrix completePairedEdges) (severeRadialRates hub F rho eta n H T u t) i /
      (u i*severeRadius F rho n H t) = (rho*F/eta)*(H*u i-1) := by
  let z := fun j => u j*(H*u j-1)
  have hz := radial_direction_zero_sum u H hun huH
  have hcl : max 0 (min T t) = t := by rw [min_eq_right ht.2,max_eq_right ht.1]
  have hinput : tradingInput (pairedMatrix completePairedEdges) (severeRadialRates hub F rho eta n H T u t) i =
      ((rho*F/eta)*severeRadius F rho n H t)*z i := by
    unfold severeRadialRates
    rw [tradingInput_scaled,fullGraphVectorDollars_input hub z hz,hcl]
  have hRp : 0 < severeRadius F rho n H t := (mul_pos hF hH).trans_le
    (severe_radius_bounds F rho n H t hF hr hH hHn ht.1).1
  rw [hinput]
  dsimp [z]
  field_simp [(hu i).ne',hRp.ne']
  <;> ring

theorem severe_radial_holdings_increment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hr : 0 ≤ rho) (he : 0 < eta)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (hun : ∑ i, (u i)^2 = 1) (huH : ∑ i, u i = H) (H0 : ι → ℝ)
    (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (i : ι) :
    let theta := rateShares completePairedEdges (fun x j => u j*severeRadius F rho n H x)
      (severeRadialRates hub F rho eta n H T u) H0
    theta t i-theta s i = (rho*F/eta)*(H*u i-1)*(t-s) := by
  intro theta
  have hT : 0 ≤ T := hs.1.trans hs.2
  have heq (j : ι) : EqOn
      (fun x => tradingInput (pairedMatrix completePairedEdges) (severeRadialRates hub F rho eta n H T u x) j /
        (u j*severeRadius F rho n H x))
      (fun _ => (rho*F/eta)*(H*u j-1)) (Icc 0 T) :=
    fun x hx => severe_radial_signed_rate hub F rho eta n H T hF hr he hH hHn u hu hun huH x hx j
  have hi (j : ι) : IntervalIntegrable
      (fun x => tradingInput (pairedMatrix completePairedEdges) (severeRadialRates hub F rho eta n H T u x) j /
        (u j*severeRadius F rho n H x)) volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hT]
    exact continuousOn_const.congr (heq j)
  rw [rateShares_difference _ _ _ H0 T hT hi i s t hs ht]
  have hh := intervalIntegral.integral_congr (μ := volume) ((heq i).mono (uIcc_subset_Icc hs ht))
  rw [hh,intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem negativeVariation_of_constant_increment (f : ℝ → ℝ) (a b q : ℝ) (hab : a ≤ b)
    (hf : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, f t-f s = q*(t-s)) :
    actualNegativeVariation f a b = max (-q) 0*(b-a) := by
  by_cases hq : 0 ≤ q
  · have hm : MonotoneOn f (Icc a b) := by
      intro s hs t ht hst
      have hh := hf s hs t ht
      nlinarith only [hh,mul_nonneg hq (sub_nonneg.mpr hst)]
    rw [sharpTransport_monotone_negativeVariation f a b hab hm,max_eq_right (by linarith)]
    ring
  · have hq' : q ≤ 0 := (lt_of_not_ge hq).le
    have hm : AntitoneOn f (Icc a b) := by
      intro s hs t ht hst
      have hh := hf s hs t ht
      nlinarith only [hh,mul_nonpos_of_nonpos_of_nonneg hq' (sub_nonneg.mpr hst)]
    rw [sharpTransport_antitone_negativeVariation f a b hab hm,max_eq_left (by linarith)]
    have hh := hf a ⟨le_rfl,hab⟩ b ⟨hab,le_rfl⟩
    linarith

theorem positive_unit_coordinate_le_one {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i,(u i)^2 = 1) (i : ι) : u i ≤ 1 := by
  have hh := Finset.single_le_sum (s := Finset.univ) (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  rw [hun] at hh
  nlinarith [hu i]

theorem severe_radial_signed_rate_bound {ι : Type*} [Fintype ι]
    (F rho eta n H : ℝ) (hF : 0 < F) (hr : 0 ≤ rho) (he : 0 < eta)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (hun : ∑ i, (u i)^2 = 1) (i : ι) :
    |(rho*F/eta)*(H*u i-1)| ≤ (rho*F/eta)*(Real.sqrt n+1) := by
  have hfac : 0 ≤ rho*F/eta := by positivity
  have hui := positive_unit_coordinate_le_one u hu hun i
  have hprod : 0 ≤ H*u i := mul_nonneg hH.le (hu i).le
  have hprod1 : H*u i ≤ Real.sqrt n := (mul_le_of_le_one_right hH.le hui).trans hHn
  have hh := abs_sub (H*u i) 1
  rw [abs_of_nonneg hprod,abs_one] at hh
  rw [abs_mul,abs_of_nonneg hfac]
  exact mul_le_mul_of_nonneg_left (hh.trans (by linarith)) hfac

theorem severe_radial_share_sales_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hr : 0 ≤ rho) (he : 0 < eta)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (u : ι → ℝ) (hu : ∀ i, 0 < u i)
    (hun : ∑ i, (u i)^2 = 1) (huH : ∑ i, u i = H) (H0 : ι → ℝ)
    (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (hst : s ≤ t) (i : ι) :
    actualNegativeVariation
      (fun x => rateShares completePairedEdges (fun x j => u j*severeRadius F rho n H x)
        (severeRadialRates hub F rho eta n H T u) H0 x i) s t ≤
      ((rho*F/eta)*(Real.sqrt n+1))*(t-s) := by
  rw [negativeVariation_of_constant_increment _ s t ((rho*F/eta)*(H*u i-1)) hst (by
    intro a ha b hb
    exact severe_radial_holdings_increment hub F rho eta n H T hF hr he hH hHn u hu hun huH H0 a b
      ⟨hs.1.trans ha.1,ha.2.trans ht.2⟩ ⟨hs.1.trans hb.1,hb.2.trans ht.2⟩ i)]
  apply mul_le_mul_of_nonneg_right _ (sub_nonneg.mpr hst)
  exact (max_le (neg_le_abs _) (abs_nonneg _)).trans
    (severe_radial_signed_rate_bound F rho eta n H hF hr he hH hHn u hu hun i)

theorem fullGraphVectorDollars_total_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (z : ι → ℝ) (A : ℝ) (hA : 0 ≤ A) (hz : ∀ i, |z i| ≤ A) :
    (∑ e, fullGraphVectorDollars hub z e) ≤ 2*(Fintype.card ι : ℝ)*A := by
  classical
  rw [fullGraphVectorDollars,embedPairedDollars_turnover]
  have hh (e : {i : ι // i ≠ hub} × Bool) : starDollars z hub e ≤ A := by
    unfold starDollars
    split
    · exact max_le ((le_abs_self _).trans (hz e.1)) hA
    · exact max_le ((neg_le_abs _).trans (hz e.1)) hA
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hh e)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_prod,Fintype.card_bool,
    Nat.cast_mul,Nat.cast_ofNat] at hs
  have hcard : Fintype.card {i : ι // i ≠ hub} ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hc : (Fintype.card {i : ι // i ≠ hub} : ℝ) ≤ Fintype.card ι := by exact_mod_cast hcard
  nlinarith only [hs,mul_le_mul_of_nonneg_right hc hA]

theorem severe_radial_vector_bound {ι : Type*} [Fintype ι]
    (n H : ℝ) (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (u : ι → ℝ)
    (hu : ∀ i, 0 < u i) (hun : ∑ i, (u i)^2 = 1) (i : ι) :
    |u i*(H*u i-1)| ≤ Real.sqrt n+1 := by
  have h := severe_radial_signed_rate_bound 1 1 1 n H (by norm_num) (by norm_num) (by norm_num) hH hHn u hu hun i
  norm_num only [one_mul,div_one] at h
  rw [abs_mul,abs_of_pos (hu i)]
  exact (mul_le_of_le_one_left (abs_nonneg _) (positive_unit_coordinate_le_one u hu hun i)).trans h

theorem severe_radial_total_rate_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hr : 0 ≤ rho) (he : 0 < eta)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (hT : 0 ≤ T)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i,(u i)^2 = 1) (t : ℝ) :
    (∑ e, severeRadialRates hub F rho eta n H T u t e) ≤
      (rho*F/eta)*(F*Real.sqrt n)*(2*(Fintype.card ι : ℝ)*(Real.sqrt n+1)) := by
  have hcl : max 0 (min T t) ∈ Icc 0 T := ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hR := severe_radius_bounds F rho n H (max 0 (min T t)) hF hr hH hHn hcl.1
  have hRp : 0 ≤ severeRadius F rho n H (max 0 (min T t)) := (mul_pos hF hH).le.trans hR.1
  have hc : 0 ≤ rho*F/eta := by positivity
  have hd := fullGraphVectorDollars_total_bound hub (fun i => u i*(H*u i-1)) (Real.sqrt n+1)
    (by positivity) (severe_radial_vector_bound n H hH hHn u hu hun)
  simp only [severeRadialRates,←Finset.mul_sum]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hR.2 hc) hd
    (Finset.sum_nonneg (fun e _ => fullGraphVectorDollars_nonnegative hub _ e)) (by positivity)

def severeShareRateBudget (F rho eta n : ℝ) : ℝ := (rho*F/eta)*(Real.sqrt n+1)
def severeDollarRateBudget (F rho eta n : ℝ) (N : ℕ) : ℝ :=
  (rho*F/eta)*(F*Real.sqrt n)*(2*(N:ℝ)*(Real.sqrt n+1))

theorem severe_radial_piece_resources {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta)
    (hn : 2 ≤ n) (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i,(u i)^2 = 1) (huH : ∑ i,u i = H) :
    ∃ p : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)),
      p.a = 0 ∧ p.b = T ∧ p.F = (fun _ => F) ∧ p.rho = (fun _ => rho) ∧
      p.response = (fun _ => constantResponse eta he) ∧
      p.prices = (fun t i => u i*severeRadius F rho n H t) ∧
      p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 T)) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t →
        (∑ e, (p.execution.cumulative e t-p.execution.cumulative e s)) ≤
          severeDollarRateBudget F rho eta n (Fintype.card ι)*(t-s)) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → ∀ i,
        actualNegativeVariation (p.shares · i) s t ≤ severeShareRateBudget F rho eta n*(t-s)) ∧
      (∃ H0 : ι → ℝ, p.shares = rateShares completePairedEdges
        (fun t i => u i*severeRadius F rho n H t) (severeRadialRates hub F rho eta n H T u) H0) := by
  obtain ⟨p,hpa,hpb,hpF,hpr,hpg,hpS,hpL,hpBV,⟨H0,hshares⟩,hG⟩ :=
    severe_radial_physical_piece_with_rates hub F rho eta n H T hF hr he hn hH hHn hT u hu hun huH
  refine ⟨p,hpa,hpb,hpF,hpr,hpg,hpS,hpL,hpBV,?_,?_,⟨H0,hshares⟩⟩
  · intro s hs t ht hst
    have hc (e : CompleteEdgeIndex ι) : Continuous (fun x => severeRadialRates hub F rho eta n H T u x e) := by
      unfold severeRadialRates severeRadius
      fun_prop
    have hinc (e : CompleteEdgeIndex ι) : p.execution.cumulative e t-p.execution.cumulative e s =
        ∫ x in s..t, severeRadialRates hub F rho eta n H T u x e := by
      rw [hG e t,hG e s]
      have hh := intervalIntegral.integral_add_adjacent_intervals (μ := volume) ((hc e).intervalIntegrable 0 s)
        ((hc e).intervalIntegrable s t)
      linarith
    simp_rw [hinc]
    rw [←intervalIntegral.integral_finset_sum (fun e (_ : e ∈ Finset.univ) => (hc e).intervalIntegrable s t)]
    have hsumC : Continuous (fun x => ∑ e, severeRadialRates hub F rho eta n H T u x e) :=
      continuous_finset_sum Finset.univ (fun e _ => hc e)
    have hh := intervalIntegral.integral_mono_on (μ := volume) hst (hsumC.intervalIntegrable s t) intervalIntegrable_const
      (fun x _ => severe_radial_total_rate_bound hub F rho eta n H T hF hr.le he hH hHn hT.le u hu hun x)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,mul_comm,severeDollarRateBudget] using hh
  · intro s hs t ht hst i
    rw [hshares]
    exact severe_radial_share_sales_bound hub F rho eta n H T hF hr.le he hH hHn u hu hun huH H0 s t hs ht hst i

theorem severe_radial_uniform_inventory_piece {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta)
    (hn : 2 ≤ n) (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i,(u i)^2 = 1) (huH : ∑ i,u i = H) :
    ∃ p : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)),
      p.a = 0 ∧ p.b = T ∧ p.F = (fun _ => F) ∧ p.rho = (fun _ => rho) ∧
      p.response = (fun _ => constantResponse eta he) ∧
      p.prices = (fun t i => u i*severeRadius F rho n H t) ∧
      p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 T)) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t →
        (∑ e, (p.execution.cumulative e t-p.execution.cumulative e s)) ≤
          severeDollarRateBudget F rho eta n (Fintype.card ι)*(t-s)) ∧
      (∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, s ≤ t → ∀ i,
        actualNegativeVariation (p.shares · i) s t ≤ severeShareRateBudget F rho eta n*(t-s)) ∧
      (∀ t ∈ Icc 0 T, ∀ i, p.shares t i ≤ 1+2*severeShareRateBudget F rho eta n*T) := by
  obtain ⟨p,hpa,hpb,hpF,hpr,hpg,hpS,hpL,hpBV,hM,hS,⟨H0,hshares⟩⟩ :=
    severe_radial_piece_resources hub F rho eta n H T hF hr he hn hH hHn hT u hu hun huH
  let V := severeShareRateBudget F rho eta n
  let J := 1+V*T
  let q := fun i => (rho*F/eta)*(H*u i-1)
  let theta := fun t i => J+q i*t
  have hV : 0 ≤ V := by dsimp [V,severeShareRateBudget]; positivity
  have hq (i) : |q i| ≤ V := severe_radial_signed_rate_bound F rho eta n H hF hr.le he hH hHn u hu hun i
  have htheta (t) (ht : t ∈ Icc 0 T) (i) : 0 ≤ theta t i ∧ theta t i ≤ 1+2*V*T := by
    have hl := mul_le_mul_of_nonneg_right (neg_le_of_abs_le (hq i)) ht.1
    have hh := mul_le_mul_of_nonneg_right (le_of_abs_le (hq i)) ht.1
    have hvt := mul_le_mul_of_nonneg_left ht.2 hV
    dsimp [theta,J]
    constructor <;> nlinarith only [hl,hh,hvt]
  have hpinc (i) (s t : ℝ) (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) :
      p.shares t i-p.shares s i = q i*(t-s) := by
    rw [hshares]
    exact severe_radial_holdings_increment hub F rho eta n H T hF hr.le he hH hHn u hu hun huH H0 s t hs ht i
  let w : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)) := {
    p with
    shares := theta
    no_short_sales := by
      intro t ht i
      exact (htheta t (by simpa [hpa,hpb] using ht) i).1
    physical_share_primitive := by
      intro i s hs t ht
      have hs0 : s ∈ Icc 0 T := by simpa [hpa,hpb] using hs
      have ht0 : t ∈ Icc 0 T := by simpa [hpa,hpb] using ht
      calc
        theta t i-theta s i = q i*(t-s) := by dsimp [theta];ring
        _ = p.shares t i-p.shares s i := (hpinc i s t hs0 ht0).symm
        _ = _ := p.physical_share_primitive i s hs t ht }
  refine ⟨w,hpa,hpb,hpF,hpr,hpg,hpS,hpL,?_,hM,?_,?_⟩
  · intro i
    have hLip : LipschitzWith ⟨|q i|,abs_nonneg _⟩ (fun t => theta t i) := by
      rw [lipschitzWith_iff_dist_le_mul]
      intro a b
      change |J+q i*a-(J+q i*b)| ≤ |q i| * |a-b|
      rw [show J+q i*a-(J+q i*b) = q i*(a-b) by ring,abs_mul]
    have hh := hLip.lipschitzOnWith.locallyBoundedVariationOn 0 T
      (left_mem_Icc.mpr hT.le) (right_mem_Icc.mpr hT.le)
    simpa only [inter_self] using hh
  · intro s hs t ht hst i
    change actualNegativeVariation (fun x => theta x i) s t ≤ V*(t-s)
    rw [negativeVariation_of_constant_increment _ s t (q i) hst (by intros; dsimp [theta];ring)]
    exact mul_le_mul_of_nonneg_right (max_le ((neg_le_abs _).trans (hq i)) hV) (sub_nonneg.mpr hst)
  · intro t ht i
    exact (htheta t ht i).2

end MarketCrash
