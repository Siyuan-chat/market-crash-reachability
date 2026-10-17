import MarketCrash.FiniteRateConstruction
import MarketCrash.SharpConstruction

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

theorem sharpRadius_bounds (F rho n b t : ℝ) (hF : 0 < F) (hρ : 0 ≤ rho)
    (hn : 2 ≤ n) (hb : 0 < b) (hnb : n*b^2 < 1) (ht : 0 ≤ t) :
    F*sharpDirectionSum n b ≤ sharpRadius F rho n b t ∧ sharpRadius F rho n b t ≤ F*Real.sqrt n := by
  obtain ⟨_,_,_,hH0,hH1⟩ := sharp_direction_geometry n b hn hb hnb
  have he0 := (Real.exp_pos (-rho*t)).le
  have he1 : Real.exp (-rho*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hdiff : 0 ≤ Real.sqrt n-sharpDirectionSum n b := by linarith
  have hlow := mul_nonneg hdiff he0
  have hhigh := mul_le_mul_of_nonneg_left he1 hdiff
  dsimp [sharpRadius]
  constructor <;> nlinarith

theorem radial_direction_zero_sum {ι : Type*} [Fintype ι]
    (u : ι → ℝ) (H : ℝ) (hn : ∑ i, (u i)^2 = 1) (hh : ∑ i, u i = H) :
    ∑ i, u i*(H*u i-1) = 0 := by
  have he : ∀ i, u i*(H*u i-1) = H*(u i)^2-u i := by intro i;ring
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum,hn,hh]
  ring

theorem tradingInput_scaled {ι κ : Type*} [Fintype κ]
    (B : ι → κ → ℝ) (d : κ → ℝ) (c : ℝ) (i : ι) :
    tradingInput B (fun e => c*d e) i = c*tradingInput B d i := by
  dsimp [tradingInput]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem sharp_radial_price_lipschitz {ι : Type*}
    (F rho n b T : ℝ) (hF : 0 < F) (hρ : 0 < rho) (hn : 2 ≤ n)
    (hb : 0 < b) (hnb : n*b^2 < 1) (u : ι → ℝ) (hu : ∀ i, 0 < u i) :
    ∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (fun t => u i*sharpRadius F rho n b t) (Icc 0 T) := by
  intro i
  have hui := hu i
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  let K : ℝ≥0 := ⟨u i*rho*F*Real.sqrt n,by positivity⟩
  refine ⟨K,(convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => ((sharpRadius_derivative F rho n b t).const_mul (u i)).hasDerivWithinAt) ?_⟩
  intro t ht
  have hbound := sharpRadius_bounds F rho n b t hF hρ.le hn hb hnb ht.1
  have hR : 0 ≤ sharpRadius F rho n b t-F*sharpDirectionSum n b := by linarith [hbound.1]
  change |u i*(-rho*(sharpRadius F rho n b t-F*sharpDirectionSum n b))| ≤ u i*rho*F*Real.sqrt n
  rw [abs_mul,abs_of_pos (hu i),abs_mul,abs_neg,abs_of_pos hρ,abs_of_nonneg hR]
  obtain ⟨_,_,_,hH0,_⟩ := sharp_direction_geometry n b hn hb hnb
  have hHF : 0 ≤ F*sharpDirectionSum n b := mul_nonneg hF.le (by linarith)
  have hh : sharpRadius F rho n b t-F*sharpDirectionSum n b ≤ F*Real.sqrt n := by linarith [hbound.2]
  nlinarith [mul_le_mul_of_nonneg_left hh (mul_pos (hu i) hρ).le]

theorem continuous_session_has_finite_cap {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (hr : ∀ e, ContinuousOn (fun t => m.rates t e) (Icc m.a m.b)) :
    ∃ v : ℝ, m.RateBounded v := by
  classical
  have hc (i : ι) : ContinuousOn (fun t => m.gross t i) (Icc m.a m.b) := by
    exact (continuousOn_finset_sum Finset.univ (fun e _ => continuousOn_const.mul (hr e))).div
      (m.continuous_prices i) (fun t ht => (m.positive_prices t ht i).ne')
  have he : (Icc m.a m.b).Nonempty := ⟨m.a,le_rfl,m.time_order.le⟩
  choose t ht hmax using fun i => isCompact_Icc.exists_isMaxOn he (hc i)
  let v := ∑ i, max 0 (m.gross (t i) i)
  have hv : 0 ≤ v := Finset.sum_nonneg (fun i _ => le_max_left _ _)
  refine ⟨v,hv,Filter.Eventually.of_forall (fun s hs i => ?_)⟩
  exact ((hmax i hs).trans (le_max_right _ _)).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (m.gross (t j) j)) (Finset.mem_univ i))

theorem continuous_session_physical_piece {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges) (ha : m.a = 0)
    (rate : ℝ → κ → ℝ) (hmr : m.rates = rate)
    (B : κ → ℝ) (hB : ∀ e, 0 ≤ B e)
    (hc : ∀ e, Continuous (fun t => rate t e))
    (hr : ∀ e t, 0 ≤ rate t e ∧ rate t e ≤ B e)
    (G : κ → StieltjesFunction) (hGL : ∀ e, LipschitzWith ⟨B e,hB e⟩ (G e))
    (hGP : ∀ e t, G e t = ∫ u in (0:ℝ)..t, rate u e) :
    ∃ p : PhysicalContinuousBVPiece edges,
      p.a = 0 ∧ p.b = m.b ∧ p.F = m.F ∧ p.rho = m.rho ∧ p.response = m.response ∧
      p.prices = m.prices ∧ p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 m.b)) := by
  have hmC (e : κ) : ContinuousOn (fun t => m.rates t e) (Icc m.a m.b) := by
    rw [hmr]; exact (hc e).continuousOn
  obtain ⟨v,hv⟩ := continuous_session_has_finite_cap m hmC
  have hd (e : κ) : ∀ᵐ t ∂volume, t ∈ Icc 0 m.b → HasDerivAt (G e) (m.rates t e) t := by
    rw [hmr]
    exact rate_stieltjes_derivative_ae _ _ _ _ (hB e) (hGL e) (hGP e) (hc e).measurable
      (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (hr e t).1]; exact (hr e t).2)
      (fun t => (hc e).continuousAt.continuousWithinAt)
  obtain ⟨p,hpa,hpb,hpF,hpρ,hpg,hpS,_,_,hpL,hpLip⟩ :=
    acSession_original_piece_of_rateBounded m ha G (fun e => ⟨B e,hB e⟩) hGL hd
      (fun _ => v*m.b) (fun _ => 0) v hv (fun _ => le_rfl)
  refine ⟨p,hpa,hpb,hpF,hpρ,hpg,hpS,hpL,?_⟩
  intro i
  have hT : 0 ≤ m.b := by simpa [ha] using m.time_order.le
  have hh := (hpLip i).locallyBoundedVariationOn 0 m.b
    (left_mem_Icc.mpr hT) (right_mem_Icc.mpr hT)
  simpa only [inter_self] using hh

set_option maxHeartbeats 800000 in
theorem sharp_radial_physical_piece {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho eta n b T : ℝ) (hF : 0 < F) (hρ : 0 < rho) (hη : 0 < eta)
    (hn : 2 ≤ n) (hb : 0 < b) (hnb : n*b^2 < 1) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i, 0 < u i) (hun : ∑ i, (u i)^2 = 1)
    (huH : ∑ i, u i = sharpDirectionSum n b) :
    ∃ p : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)),
      p.a = 0 ∧ p.b = T ∧ p.F = (fun _ => F) ∧ p.rho = (fun _ => rho) ∧
      p.response = (fun _ => constantResponse eta hη) ∧
      p.prices = (fun t i => u i*sharpRadius F rho n b t) ∧
      p.dollarLedger 0 = (fun _ => 0) ∧
      (∀ i, BoundedVariationOn (p.shares · i) (Icc 0 T)) := by
  classical
  let R := sharpRadius F rho n b
  let cl := fun t : ℝ => max 0 (min T t)
  have hclC : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl (t : ℝ) : cl t ∈ Icc 0 T := ⟨le_max_left _ _,max_le hT.le (min_le_left _ _)⟩
  have hclId (t : ℝ) (ht : t ∈ Icc 0 T) : cl t = t := by
    dsimp [cl]; rw [min_eq_right ht.2,max_eq_right ht.1]
  have hRC : Continuous R := continuous_iff_continuousAt.mpr (fun t =>
    (sharpRadius_derivative F rho n b t).continuousAt)
  obtain ⟨_,_,_,hH,_⟩ := sharp_direction_geometry n b hn hb hnb
  have hRP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < R t :=
    (mul_pos hF (by linarith : 0 < sharpDirectionSum n b)).trans_le
      (sharpRadius_bounds F rho n b t hF hρ.le hn hb hnb ht.1).1
  let z := fun i => u i*(sharpDirectionSum n b*u i-1)
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
    have hbR := (sharpRadius_bounds F rho n b (cl t) hF hρ.le hn hb hnb (hcl t).1).2
    have hrp := hRP (cl t) (hcl t)
    have hfac : 0 ≤ rho*F/eta := by positivity
    exact ⟨mul_nonneg (mul_nonneg hfac hrp.le) (hd e),
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbR hfac) (hd e)⟩
  choose G hG0 hGP hGL using fun e => exists_bounded_rate_stieltjes
    (fun t => rate t e) (B e) (hB e) (hrC e).measurable (fun t => (hr e t).1) (fun t => (hr e t).2)
  choose K hKL using sharp_radial_price_lipschitz F rho n b T hF hρ hn hb hnb u hu
  have hSP (t) (ht : t ∈ Icc 0 T) (i) : 0 < u i*R t := mul_pos (hu i) (hRP t ht)
  have hODE (i) (t) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (fun s => u i*R s)
        (-rho*(u i*R t-F)+eta*(tradingInput (pairedMatrix completePairedEdges) (rate t) i/(u i*R t))) (Ici t) t := by
    have ht' : t ∈ Icc 0 T := ⟨ht.1,ht.2.le⟩
    have hinput : tradingInput (pairedMatrix completePairedEdges) (rate t) i = (rho*F/eta)*R t*z i := by
      change tradingInput (pairedMatrix completePairedEdges) (fun e => ((rho*F/eta)*R (cl t))*d e) i = _
      rw [tradingInput_scaled,fullGraphVectorDollars_input hub z hz,hclId t ht']
    have hp := hRP t ht'
    convert ((sharpRadius_derivative F rho n b t).const_mul (u i)).hasDerivWithinAt using 1
    rw [hinput]
    have hui := (hu i).ne'
    have hRn : sharpRadius F rho n b t ≠ 0 := hp.ne'
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

end MarketCrash
