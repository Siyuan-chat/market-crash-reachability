import MarketCrash.SharpRadialPiece
import MarketCrash.SevereParameter

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

theorem severeRadius_derivative (F rho n H t : ℝ) :
    HasDerivAt (severeRadius F rho n H) (-rho*(severeRadius F rho n H t-F*H)) t := by
  have hh := ((((hasDerivAt_id t).const_mul (-rho)).exp).const_mul
    (Real.sqrt n-H) |>.const_add H).const_mul F
  convert hh using 1 <;> dsimp [severeRadius] <;> ring

theorem severe_radial_price_lipschitz {ι : Type*}
    (F rho n H T : ℝ) (hF : 0 < F) (hρ : 0 < rho)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    ∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (fun t => u i*severeRadius F rho n H t) (Icc 0 T) := by
  intro i
  have hui := hu i
  let K : ℝ≥0 := ⟨u i*rho*F*Real.sqrt n,by positivity⟩
  refine ⟨K,(convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => ((severeRadius_derivative F rho n H t).const_mul (u i)).hasDerivWithinAt) ?_⟩
  intro t ht
  have hbound := severe_radius_bounds F rho n H t hF hρ.le hH hHn ht.1
  have hR : 0 ≤ severeRadius F rho n H t-F*H := by linarith [hbound.1]
  change |u i*(-rho*(severeRadius F rho n H t-F*H))| ≤ u i*rho*F*Real.sqrt n
  rw [abs_mul,abs_of_pos (hu i),abs_mul,abs_neg,abs_of_pos hρ,abs_of_nonneg hR]
  have hHF : 0 ≤ F*H := mul_nonneg hF.le hH.le
  have hh : severeRadius F rho n H t-F*H ≤ F*Real.sqrt n := by linarith [hbound.2]
  nlinarith only [mul_le_mul_of_nonneg_left hh (mul_pos (hu i) hρ).le]

theorem continuous_session_piece_with_execution {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (ha : m.a = 0)
    (B : κ → ℝ≥0) (G : κ → StieltjesFunction) (hGL : ∀ e, LipschitzWith (B e) (G e))
    (hd : ∀ e, ∀ᵐ t ∂volume, t ∈ Icc 0 m.b → HasDerivAt (G e) (m.rates t e) t)
    (hc : ∀ e, ContinuousOn (fun t => m.rates t e) (Icc 0 m.b)) :
    ∃ (p : PhysicalContinuousBVPiece edges) (H : ι → ℝ),
      p.a = 0 ∧ p.b = m.b ∧ p.F = m.F ∧ p.rho = m.rho ∧ p.response = m.response ∧
      p.prices = m.prices ∧ p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 m.b)) ∧
      p.execution.cumulative = G ∧ p.shares = rateShares edges m.prices m.rates H := by
  have hmc (e : κ) : ContinuousOn (fun t => m.rates t e) (Icc m.a m.b) := by
    simpa [ha] using hc e
  obtain ⟨v,hv⟩ := continuous_session_has_finite_cap m hmc
  have hT : 0 ≤ m.b := by simpa [ha] using m.time_order.le
  have hi := m.signed_share_integrable
  have hb := m.signed_share_bound v hv
  simp only [ha] at hi hb
  let H := fun _ : ι => v*m.b
  obtain ⟨hLip,hshort⟩ := rateShares_lipschitz_and_nonnegative edges m.prices m.rates H
    m.b v hT hv.1 hi hb (fun _ => le_rfl)
  let p := acSessionOriginalPiece m ha G B hGL hd H 0 hshort
  refine ⟨p,H,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,rfl,rfl⟩
  · funext i
    simp [p,acSessionOriginalPiece,tradingInput]
  · intro i
    have hh := (hLip i).locallyBoundedVariationOn 0 m.b
      (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT)
    simpa only [inter_self] using hh

set_option maxHeartbeats 800000 in
theorem severe_radial_physical_piece {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hρ : 0 < rho) (hη : 0 < eta)
    (hn : 2 ≤ n) (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i, (u i)^2 = 1)
    (huH : ∑ i, u i = H) :
    ∃ p : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)),
      p.a = 0 ∧ p.b = T ∧ p.F = (fun _ => F) ∧ p.rho = (fun _ => rho) ∧
      p.response = (fun _ => constantResponse eta hη) ∧
      p.prices = (fun t i => u i*severeRadius F rho n H t) ∧
      p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 T)) := by
  classical
  let R := severeRadius F rho n H
  let cl := fun t : ℝ => max 0 (min T t)
  have hclC : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl (t : ℝ) : cl t ∈ Icc 0 T := ⟨le_max_left _ _,max_le hT.le (min_le_left _ _)⟩
  have hclId (t : ℝ) (ht : t ∈ Icc 0 T) : cl t = t := by
    dsimp [cl]; rw [min_eq_right ht.2,max_eq_right ht.1]
  have hRC : Continuous R := continuous_iff_continuousAt.mpr (fun t =>
    (severeRadius_derivative F rho n H t).continuousAt)
  have hRP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < R t :=
    (mul_pos hF hH).trans_le
      (severe_radius_bounds F rho n H t hF hρ.le hH hHn ht.1).1
  let z := fun i => u i*(H*u i-1)
  have hz : ∑ i, z i = 0 := radial_direction_zero_sum u _ hun huH
  let d := fullGraphVectorDollars hub z
  have hd (e : CompleteEdgeIndex ι) : 0 ≤ d e := fullGraphVectorDollars_nonnegative hub z e
  let rate := fun t e => (rho*F/eta)*R (cl t)*d e
  let B := fun e => (rho*F/eta)*(F*Real.sqrt n)*d e
  have hB (e) : 0 ≤ B e := by
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hρ.le hF.le) hη.le)
      (mul_nonneg hF.le (Real.sqrt_nonneg n))) (hd e)
  have hrC (e) : Continuous (fun t => rate t e) :=
    ((continuous_const.mul (hRC.comp hclC)).mul continuous_const)
  have hr (e) (t) : 0 ≤ rate t e ∧ rate t e ≤ B e := by
    have hbR := (severe_radius_bounds F rho n H (cl t) hF hρ.le hH hHn (hcl t).1).2
    have hrp := hRP (cl t) (hcl t)
    have hfac : 0 ≤ rho*F/eta := by positivity
    exact ⟨mul_nonneg (mul_nonneg hfac hrp.le) (hd e),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbR hfac) (hd e)⟩
  choose G hG0 hGP hGL using fun e => exists_bounded_rate_stieltjes
    (fun t => rate t e) (B e) (hB e) (hrC e).measurable (fun t => (hr e t).1) (fun t => (hr e t).2)
  choose K hKL using severe_radial_price_lipschitz F rho n H T hF hρ hH hHn u hu
  have hSP (t) (ht : t ∈ Icc 0 T) (i) : 0 < u i*R t := mul_pos (hu i) (hRP t ht)
  have hODE (i) (t) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (fun s => u i*R s)
        (-rho*(u i*R t-F)+eta*(tradingInput (pairedMatrix completePairedEdges) (rate t) i/(u i*R t))) (Ici t) t := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1,ht.2.le⟩
    have hinput : tradingInput (pairedMatrix completePairedEdges) (rate t) i = (rho*F/eta)*R t*z i := by
      change tradingInput (pairedMatrix completePairedEdges) (fun e => ((rho*F/eta)*R (cl t))*d e) i = _
      rw [tradingInput_scaled,fullGraphVectorDollars_input hub z hz,hclId t ht']
    have hp := hRP t ht'
    convert ((severeRadius_derivative F rho n H t).const_mul (u i)).hasDerivWithinAt using 1
    rw [hinput]
    have hui := (hu i).ne'
    have hRn : severeRadius F rho n H t ≠ 0 := hp.ne'
    dsimp [z,R]
    field_simp [hui,hRn,hη.ne']
    <;> ring
  let m := rightODERateSession completePairedEdges (fun _ : ι => F) (fun _ => rho)
    (fun _ => constantResponse eta hη) (fun _ => hF) (fun _ => hρ.le) T hT
    (fun t i => u i*R t) K hKL hSP rate B hB (fun e => (hrC e).measurable)
    hr G hGL hGP (fun e t => (hrC e).continuousAt.continuousWithinAt) hODE
  obtain ⟨p,hpa,hpb,hpF,hpρ,hpg,hpS,hpL,hpBV⟩ :=
    continuous_session_physical_piece m rfl rate rfl B hB hrC hr G hGL hGP
  exact ⟨p,hpa,hpb,hpF,hpρ,hpg,hpS,hpL,hpBV⟩

def severeRadialRates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (u : ι → ℝ) (t : ℝ) (e : CompleteEdgeIndex ι) : ℝ :=
  (rho*F/eta)*severeRadius F rho n H (max 0 (min T t))*
    fullGraphVectorDollars hub (fun i => u i*(H*u i-1)) e

set_option maxHeartbeats 800000 in
theorem severe_radial_physical_piece_with_rates {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n H T : ℝ) (hF : 0 < F) (hρ : 0 < rho) (hη : 0 < eta)
    (hn : 2 ≤ n) (hH : 0 < H) (hHn : H ≤ Real.sqrt n) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i, (u i)^2 = 1)
    (huH : ∑ i, u i = H) :
    ∃ p : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)),
      p.a = 0 ∧ p.b = T ∧ p.F = (fun _ => F) ∧ p.rho = (fun _ => rho) ∧
      p.response = (fun _ => constantResponse eta hη) ∧
      p.prices = (fun t i => u i*severeRadius F rho n H t) ∧
      p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 T)) ∧
      (∃ H0 : ι → ℝ,
        p.shares = rateShares completePairedEdges (fun t i => u i*severeRadius F rho n H t)
          (severeRadialRates hub F rho eta n H T u) H0) ∧
      (∀ e t, p.execution.cumulative e t = ∫ s in (0:ℝ)..t,
        severeRadialRates hub F rho eta n H T u s e) := by
  classical
  let R := severeRadius F rho n H
  let cl := fun t : ℝ => max 0 (min T t)
  have hclC : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl (t : ℝ) : cl t ∈ Icc 0 T := ⟨le_max_left _ _,max_le hT.le (min_le_left _ _)⟩
  have hclId (t : ℝ) (ht : t ∈ Icc 0 T) : cl t = t := by
    dsimp [cl]; rw [min_eq_right ht.2,max_eq_right ht.1]
  have hRC : Continuous R := continuous_iff_continuousAt.mpr (fun t =>
    (severeRadius_derivative F rho n H t).continuousAt)
  have hRP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < R t :=
    (mul_pos hF hH).trans_le
      (severe_radius_bounds F rho n H t hF hρ.le hH hHn ht.1).1
  let z := fun i => u i*(H*u i-1)
  have hz : ∑ i, z i = 0 := radial_direction_zero_sum u _ hun huH
  let d := fullGraphVectorDollars hub z
  have hd (e : CompleteEdgeIndex ι) : 0 ≤ d e := fullGraphVectorDollars_nonnegative hub z e
  let rate := fun t e => (rho*F/eta)*R (cl t)*d e
  let B := fun e => (rho*F/eta)*(F*Real.sqrt n)*d e
  have hB (e) : 0 ≤ B e := by
    exact mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg hρ.le hF.le) hη.le)
      (mul_nonneg hF.le (Real.sqrt_nonneg n))) (hd e)
  have hrC (e) : Continuous (fun t => rate t e) :=
    ((continuous_const.mul (hRC.comp hclC)).mul continuous_const)
  have hr (e) (t) : 0 ≤ rate t e ∧ rate t e ≤ B e := by
    have hbR := (severe_radius_bounds F rho n H (cl t) hF hρ.le hH hHn (hcl t).1).2
    have hrp := hRP (cl t) (hcl t)
    have hfac : 0 ≤ rho*F/eta := by positivity
    exact ⟨mul_nonneg (mul_nonneg hfac hrp.le) (hd e),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbR hfac) (hd e)⟩
  choose G hG0 hGP hGL using fun e => exists_bounded_rate_stieltjes
    (fun t => rate t e) (B e) (hB e) (hrC e).measurable (fun t => (hr e t).1) (fun t => (hr e t).2)
  choose K hKL using severe_radial_price_lipschitz F rho n H T hF hρ hH hHn u hu
  have hSP (t) (ht : t ∈ Icc 0 T) (i) : 0 < u i*R t := mul_pos (hu i) (hRP t ht)
  have hODE (i) (t) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (fun s => u i*R s)
        (-rho*(u i*R t-F)+eta*(tradingInput (pairedMatrix completePairedEdges) (rate t) i/(u i*R t))) (Ici t) t := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1,ht.2.le⟩
    have hinput : tradingInput (pairedMatrix completePairedEdges) (rate t) i = (rho*F/eta)*R t*z i := by
      change tradingInput (pairedMatrix completePairedEdges) (fun e => ((rho*F/eta)*R (cl t))*d e) i = _
      rw [tradingInput_scaled,fullGraphVectorDollars_input hub z hz,hclId t ht']
    have hp := hRP t ht'
    convert ((severeRadius_derivative F rho n H t).const_mul (u i)).hasDerivWithinAt using 1
    rw [hinput]
    have hui := (hu i).ne'
    have hRn : severeRadius F rho n H t ≠ 0 := hp.ne'
    dsimp [z,R]
    field_simp [hui,hRn,hη.ne']
    <;> ring
  let m := rightODERateSession completePairedEdges (fun _ : ι => F) (fun _ => rho)
    (fun _ => constantResponse eta hη) (fun _ => hF) (fun _ => hρ.le) T hT
    (fun t i => u i*R t) K hKL hSP rate B hB (fun e => (hrC e).measurable)
    hr G hGL hGP (fun e t => (hrC e).continuousAt.continuousWithinAt) hODE
  have hdens (e) : ∀ᵐ t ∂volume, t ∈ Icc 0 m.b → HasDerivAt (G e) (m.rates t e) t := by
    exact rate_stieltjes_derivative_ae _ _ _ _ (hB e) (hGL e) (hGP e) (hrC e).measurable
      (fun t => by change ‖rate t e‖ ≤ B e; rw [Real.norm_eq_abs,abs_of_nonneg (hr e t).1]; exact (hr e t).2)
      (fun t => (hrC e).continuousAt.continuousWithinAt)
  obtain ⟨p,H0,hpa,hpb,hpF,hpρ,hpg,hpS,hpL,hpBV,hExec,hShares⟩ :=
    continuous_session_piece_with_execution m rfl (fun e => ⟨B e,hB e⟩) G hGL hdens
      (fun e => (hrC e).continuousOn)
  refine ⟨p,hpa,hpb,hpF,hpρ,hpg,hpS,hpL,hpBV,⟨H0,?_⟩,?_⟩
  · exact hShares
  · intro e t
    rw [hExec]
    exact hGP e t


end MarketCrash
