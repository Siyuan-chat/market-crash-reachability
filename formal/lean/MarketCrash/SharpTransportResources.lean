import MarketCrash.SquareTransportation
import MarketCrash.SevereResources
import MarketCrash.OriginalResources
noncomputable section
namespace MarketCrash
open Set

theorem sharpTransport_eVariation_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  unfold eVariationOn
  congr 1
  funext p
  apply Finset.sum_congr rfl
  intro i hi
  simp only [edist_dist, Real.dist_eq, neg_sub_neg, abs_sub_comm]

theorem sharpTransport_monotone_negativeVariation (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : MonotoneOn f (Icc a b)) :
    actualNegativeVariation f a b = 0 := by
  have he := hf.eVariationOn_le (show a ∈ Icc a b from ⟨le_rfl,hab⟩)
    (show b ∈ Icc a b from ⟨hab,le_rfl⟩)
  rw [inter_self] at he
  have hv : BoundedVariationOn f (Icc a b) := (he.trans_lt ENNReal.ofReal_lt_top).ne
  have hr := ENNReal.toReal_mono (by simp) he
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (hf ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab))] at hr
  have hn := actualNegativeVariation_nonnegative f a b hab hv
  unfold actualNegativeVariation at *
  rw [variationOnFromTo.eq_of_le _ _ hab,inter_self] at hn ⊢
  linarith

theorem sharpTransport_antitone_negativeVariation (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : AntitoneOn f (Icc a b)) :
    actualNegativeVariation f a b = f a-f b := by
  have hm : MonotoneOn (fun x => -f x) (Icc a b) :=
    fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  have hh := sharpTransport_monotone_negativeVariation (fun x => -f x) a b hab hm
  unfold actualNegativeVariation at *
  rw [variationOnFromTo.eq_of_le _ _ hab,inter_self,sharpTransport_eVariation_neg] at hh
  rw [variationOnFromTo.eq_of_le _ _ hab,inter_self]
  linarith

theorem sharpTransport_constantPulse_monotone (P eta B z : ℝ) (heta : 0 ≤ eta)
    (hB : 0 ≤ B) (hz : 0 ≤ z) : Monotone (fun a => constantPulsePrice P eta B (a*z)) := by
  intro a b hab
  unfold constantPulsePrice
  apply Real.sqrt_le_sqrt
  gcongr

theorem sharpTransport_constantPulse_antitone (P eta B z : ℝ) (heta : 0 ≤ eta)
    (hB : B ≤ 0) (hz : 0 ≤ z) : Antitone (fun a => constantPulsePrice P eta B (a*z)) := by
  intro a b hab
  unfold constantPulsePrice
  apply Real.sqrt_le_sqrt
  have h : b*z*B ≤ a*z*B := mul_le_mul_of_nonpos_right (mul_le_mul_of_nonneg_right hab hz) hB
  nlinarith

theorem sharpTransport_constantPulse_shareSales {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta) (P H L : ι → ℝ)
    (hp : ∀ a ∈ Icc 0 z, ∀ i, 0 < (P i)^2+2*eta*a*pairedMatrix edges i e)
    (hH : ∀ i, P i/eta ≤ H i) (i : ι) :
    let p := constantOriginalEdgePulse edges e z hz t F eta hF hη P H L hp hH
    actualNegativeVariation (fun a => p.normalize.shares a i) 0 1 =
      max ((p.prices 0 i-p.prices z i)/eta) 0 := by
  intro p
  have he (a : ℝ) : p.normalize.shares a i =
      H i+(constantPulsePrice (P i) eta (pairedMatrix edges i e) (a*z)-P i)/eta := by
    change H i+(constantPulsePrice (P i) eta (pairedMatrix edges i e) (z*a)-P i)/eta = _
    rw [mul_comm z a]
  have hstart : p.normalize.shares 0 i = H i+(p.prices 0 i-P i)/eta := by
    rw [he];simp only [zero_mul];rfl
  have hend : p.normalize.shares 1 i = H i+(p.prices z i-P i)/eta := by
    rw [he];simp only [one_mul];rfl
  by_cases hB : 0 ≤ pairedMatrix edges i e
  · have hm : Monotone (fun a => p.normalize.shares a i) := by
      intro a b hab
      dsimp only
      rw [he,he]
      gcongr
      exact sharpTransport_constantPulse_monotone _ _ _ _ hη.le hB hz.le hab
    rw [sharpTransport_monotone_negativeVariation _ _ _ (by norm_num) (hm.monotoneOn _)]
    apply (max_eq_right _).symm
    have hh := hm (show (0:ℝ) ≤ 1 by norm_num)
    dsimp only at hh
    rw [hstart,hend] at hh
    have hn : p.prices 0 i-p.prices z i ≤ 0 := by
      have := (div_le_div_iff_of_pos_right hη).mp (show (p.prices 0 i-P i)/eta ≤ (p.prices z i-P i)/eta by linarith)
      linarith
    exact div_nonpos_of_nonpos_of_nonneg hn hη.le
  · have hm : Antitone (fun a => p.normalize.shares a i) := by
      intro a b hab
      dsimp only
      rw [he,he]
      gcongr
      exact sharpTransport_constantPulse_antitone _ _ _ _ hη.le (le_of_not_ge hB) hz.le hab
    rw [sharpTransport_antitone_negativeVariation _ _ _ (by norm_num) (hm.antitoneOn _),hstart,hend]
    have hh := hm (show (0:ℝ) ≤ 1 by norm_num)
    dsimp only at hh
    rw [hstart,hend] at hh
    have hn : 0 ≤ (p.prices 0 i-p.prices z i)/eta := by
      have heq : (p.prices 0 i-P i)/eta-(p.prices z i-P i)/eta = (p.prices 0 i-p.prices z i)/eta := by ring
      linarith
    rw [max_eq_left hn]
    ring

theorem sharpTransport_singlePulse_turnover {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (p : OriginalDollarParameterPulse edges) :
    (∑ e, p.normalize.dollars e) = p.z := by
  classical
  simp [OriginalDollarParameterPulse.normalize,OriginalDollarParameterPulse.normalizedDollars]

theorem sharpTransport_constantPulse_shareSales_bound {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta) (P H L : ι → ℝ)
    (hp : ∀ a ∈ Icc 0 z, ∀ i, 0 < (P i)^2+2*eta*a*pairedMatrix edges i e)
    (hH : ∀ i, P i/eta ≤ H i) (R : ℝ) (hR : 0 ≤ R) (i : ι)
    (hcap : |P i| ≤ R) :
    let p := constantOriginalEdgePulse edges e z hz t F eta hF hη P H L hp hH
    actualNegativeVariation (fun a => p.normalize.shares a i) 0 1 ≤ R/eta := by
  intro p
  rw [sharpTransport_constantPulse_shareSales edges e z hz t F eta hF hη P H L hp hH i]
  apply max_le
  · apply (div_le_div_iff_of_pos_right hη).mpr
    have hzero : p.prices 0 i = |P i| := by
      change Real.sqrt ((P i)^2+2*eta*0*pairedMatrix edges i e) = _
      simp [Real.sqrt_sq_eq_abs]
    have hend := p.positive_prices z ⟨hz.le,le_rfl⟩ i
    rw [hzero]
    linarith
  · exact div_nonneg hR hη.le

theorem sharpTransport_step_turnover_heq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t s' t' : PhysicalMarketState ι}
    (h : OriginalPhysicalStep F rho g edges s t) (h' : OriginalPhysicalStep F rho g edges s' t')
    (hs : s = s') (ht : t = t') (he : HEq h h') : h.pairedTurnover = h'.pairedTurnover := by
  subst s';subst t'
  cases he
  rfl

theorem sharpTransport_step_shareSales_heq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t s' t' : PhysicalMarketState ι}
    (h : OriginalPhysicalStep F rho g edges s t) (h' : OriginalPhysicalStep F rho g edges s' t')
    (hs : s = s') (ht : t = t') (he : HEq h h') (i : ι) : h.shareSales i = h'.shareSales i := by
  subst s';subst t'
  cases he
  rfl

theorem sharpTransport_step_turnover {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (p : OriginalDollarParameterPulse edges) (rho : ι → ℝ) :
    (p.toOriginalStep rho).pairedTurnover = p.z := by
  have he : HEq (p.toOriginalStep rho)
      (OriginalPhysicalStep.pulse (rho := rho) p.normalize rfl rfl p.normalized_shares_bv) := by
    unfold OriginalDollarParameterPulse.toOriginalStep
    exact cast_heq _ _
  rw [sharpTransport_step_turnover_heq _ _ (by simp [OriginalDollarParameterPulse.normalize]) (by simp [OriginalDollarParameterPulse.normalize]) he]
  exact sharpTransport_singlePulse_turnover p

theorem sharpTransport_step_shareSales {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (p : OriginalDollarParameterPulse edges) (rho : ι → ℝ) (i : ι) :
    (p.toOriginalStep rho).shareSales i = actualNegativeVariation (fun a => p.normalize.shares a i) 0 1 := by
  have he : HEq (p.toOriginalStep rho)
      (OriginalPhysicalStep.pulse (rho := rho) p.normalize rfl rfl p.normalized_shares_bv) := by
    unfold OriginalDollarParameterPulse.toOriginalStep
    exact cast_heq _ _
  exact sharpTransport_step_shareSales_heq _ _ (by simp [OriginalDollarParameterPulse.normalize]) (by simp [OriginalDollarParameterPulse.normalize]) he i

theorem sharpTransport_resources_state_congr {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t s' t' : PhysicalMarketState ι} (hs : s = s') (ht : t = t') (M V : ℝ) :
    (∃ p : OriginalPhysicalReachable F rho g edges s t,
      p.pairedTurnover = M ∧ ∀ i, p.shareSales i ≤ V) →
    (∃ p : OriginalPhysicalReachable F rho g edges s' t',
      p.pairedTurnover = M ∧ ∀ i, p.shareSales i ≤ V) := by
  subst s';subst t'
  exact id
theorem sharpTransport_single_edge_resources {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta) (rho H L x : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) (hx : ∀ i, 0 < x i)
    (hx' : ∀ i, 0 < x i+z*pairedMatrix edges i e)
    (R : ℝ) (hR : 0 ≤ R) (hcap : ∀ i, Real.sqrt (2*eta*x i) ≤ R) :
    ∃ path : OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) edges
      (squarePhysicalState t eta H L x)
      (squarePhysicalState t eta H L (fun i => x i+z*pairedMatrix edges i e)),
      path.pairedTurnover = z ∧ ∀ i, path.shareSales i ≤ R/eta := by
  let P := fun i => Real.sqrt (2*eta*x i)
  have hP : ∀ i, 0 < P i := fun i => Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) hη) (hx i))
  have hP2 : ∀ i, (P i)^2 = 2*eta*x i := fun i => Real.sq_sqrt (mul_pos (mul_pos (by norm_num) hη) (hx i)).le
  have hend : ∀ i, 0 < (P i)^2+2*eta*z*pairedMatrix edges i e := by
    intro i
    rw [hP2]
    nlinarith [mul_pos hη (hx' i)]
  let p := constantOriginalEdgePulse edges e z hz t F eta hF hη P
    (fun i => H i+P i/eta) (fun i => L i+x i)
    (fun a ha i => constantPulsePrice_positive_between _ _ _ _ (hP i) (hend i) a ha)
    (fun i => le_add_of_nonneg_left (hH i))
  have he : ∀ a i, p.prices a i = Real.sqrt (2*eta*(x i+a*pairedMatrix edges i e)) := by
    intro a i
    change constantPulsePrice (P i) eta (pairedMatrix edges i e) a = _
    rw [constantPulsePrice,hP2]
    congr 1
    ring
  have hS : ∀ a i, p.shares a i = H i+Real.sqrt (2*eta*(x i+a*pairedMatrix edges i e))/eta := by
    intro a i
    change H i+P i/eta+(p.prices a i-P i)/eta = _
    rw [he]
    ring
  have hstart : (⟨p.physicalTime,p.prices 0,p.shares 0,p.dollarLedger 0⟩ : PhysicalMarketState ι) =
      squarePhysicalState t eta H L x := by
    simp only [squarePhysicalState]
    congr 1
    · funext i;simpa only [zero_mul,add_zero] using he 0 i
    · funext i;simpa only [zero_mul,add_zero] using hS 0 i
    · funext i;change L i+x i+0*pairedMatrix edges i e = L i+x i;ring
  have hfinish : (⟨p.physicalTime,p.prices p.z,p.shares p.z,p.dollarLedger p.z⟩ : PhysicalMarketState ι) =
      squarePhysicalState t eta H L (fun i => x i+z*pairedMatrix edges i e) := by
    simp only [squarePhysicalState]
    congr 1
    · funext i;exact he z i
    · funext i;exact hS z i
    · funext i;change L i+x i+z*pairedMatrix edges i e = L i+(x i+z*pairedMatrix edges i e);ring
  have hex : ∃ path : OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) edges
      ⟨p.physicalTime,p.prices 0,p.shares 0,p.dollarLedger 0⟩
      ⟨p.physicalTime,p.prices p.z,p.shares p.z,p.dollarLedger p.z⟩,
      path.pairedTurnover = z ∧ ∀ i, path.shareSales i ≤ R/eta := by
    refine ⟨.append (.refl _) (p.toOriginalStep rho),?_,?_⟩
    · change 0+(p.toOriginalStep rho).pairedTurnover = z
      rw [sharpTransport_step_turnover,zero_add]
      rfl
    · intro i
      change 0+(p.toOriginalStep rho).shareSales i ≤ R/eta
      rw [zero_add,sharpTransport_step_shareSales]
      exact sharpTransport_constantPulse_shareSales_bound edges e z hz t F eta hF hη P
        (fun i => H i+P i/eta) (fun i => L i+x i) _ _ R hR i
        (by rw [abs_of_pos (hP i)];exact hcap i)
  exact sharpTransport_resources_state_congr hstart hfinish z (R/eta) hex

theorem sharpTransport_exists_short_schedule {ι : Type*} [Fintype ι] [DecidableEq ι] (hub : ι) (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hsum : ∑ i, x i = ∑ i, y i) :
    ∃ cs : List (CompleteEdgeIndex ι × ℝ),
      squareSchedulePositive completePairedEdges x cs ∧ chartControlEndpoint completePairedEdges x cs = y ∧ cs.length ≤ 2*Fintype.card ι := by
  classical
  let a := fun i => max (x i-y i) 0
  let b := fun i => max (y i-x i) 0
  have ha : ∀ i, 0 ≤ a i := fun i => le_max_right _ _
  have hb : ∀ i, 0 ≤ b i := fun i => le_max_right _ _
  have hab : ∀ i, a i-b i = x i-y i := by
    intro i
    dsimp [a,b]
    rcases le_total (x i) (y i) with hh | hh
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)];ring
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)];ring
  let D : Finset {i : ι // i ≠ hub} := Finset.univ.filter (fun i => 0 < a i)
  let R : Finset {i : ι // i ≠ hub} := Finset.univ.filter (fun i => 0 < b i)
  let ds := squareDonorSchedule hub a D.toList
  let xd := chartControlEndpoint completePairedEdges x ds
  have hd : squareSchedulePositive completePairedEdges x ds := by
    apply square_donor_schedule_positive hub a x D.toList D.nodup_toList hx
    intro i hi
    have hai : 0 < a i := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    refine ⟨hai,?_⟩
    exact max_lt_iff.mpr ⟨by linarith [hy i],hx i⟩
  have hxd : ∀ i, 0 < xd i := squareSchedulePositive_end completePairedEdges x ds hd
  have haD : ∀ i : {i : ι // i ≠ hub}, (if i ∈ D then a i else 0) = a i := by
    intro i
    by_cases hi : 0 < a i
    · simp [D,hi]
    · have hz : a i = 0 := le_antisymm (not_lt.mp hi) (ha i)
      simp [D,hz]
  have hbR : ∀ i : {i : ι // i ≠ hub}, (if i ∈ R then b i else 0) = b i := by
    intro i
    by_cases hi : 0 < b i
    · simp [R,hi]
    · have hz : b i = 0 := le_antisymm (not_lt.mp hi) (hb i)
      simp [R,hz]
  have hdh : xd hub = x hub+∑ i : {i : ι // i ≠ hub}, a i := by
    rw [show xd hub = chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a D.toList) hub from rfl,
      square_donor_endpoint_hub]
    rw [positive_entries_sum (fun i : {i : ι // i ≠ hub} => a i) (fun i => ha i)]
  have hbal : x hub+(∑ i : {i : ι // i ≠ hub}, a i) =
      y hub+(∑ i : {i : ι // i ≠ hub}, b i) := by
    have hh := hsum
    rw [Fintype.sum_eq_add_sum_subtype_ne x hub,Fintype.sum_eq_add_sum_subtype_ne y hub] at hh
    have he : (∑ i : {i : ι // i ≠ hub}, a i)-(∑ i : {i : ι // i ≠ hub}, b i) =
        (∑ i : {i : ι // i ≠ hub}, x i)-(∑ i : {i : ι // i ≠ hub}, y i) := by
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hab i)
    linarith
  have hRsum : (R.toList.map (fun i : {i : ι // i ≠ hub} => b i)).sum =
      ∑ i : {i : ι // i ≠ hub}, b i := by
    rw [← List.sum_toFinset _ R.nodup_toList]
    rw [Finset.toList_toFinset]
    exact positive_entries_sum (fun i : {i : ι // i ≠ hub} => b i) (fun i => hb i)
  have hrcap : (R.toList.map (fun i : {i : ι // i ≠ hub} => b i)).sum < xd hub := by
    rw [hRsum,hdh]
    linarith [hy hub]
  let rs := squareReceiverSchedule hub b R.toList
  have hr : squareSchedulePositive completePairedEdges xd rs :=
    square_receiver_schedule_positive hub b xd R.toList hxd (by
      intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2) hrcap
  have hend : chartControlEndpoint completePairedEdges x (ds++rs) = y := by
    rw [chartControlEndpoint_append]
    funext i
    by_cases hi : i = hub
    · subst i
      rw [square_receiver_endpoint_hub]
      change xd hub-(∑ i ∈ R, b i) = y hub
      rw [show (∑ i ∈ R, b i) = ∑ i : {i : ι // i ≠ hub}, b i from
        positive_entries_sum (fun i : {i : ι // i ≠ hub} => b i) (fun i => hb i),hdh]
      linarith
    · change chartControlEndpoint completePairedEdges xd (squareReceiverSchedule hub b R.toList) (⟨i,hi⟩ : {i : ι // i ≠ hub}) = y i
      rw [square_receiver_endpoint_nonhub,hbR]
      change xd i+b i = y i
      rw [show xd i = x i-a i by
        change chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a D.toList) (⟨i,hi⟩ : {i : ι // i ≠ hub}) = _
        rw [square_donor_endpoint_nonhub,haD]]
      linarith [hab i]
  refine ⟨ds++rs,squareSchedulePositive_append _ x ds rs hd hr,hend,?_⟩
  have hD : D.card ≤ Fintype.card ι := (Finset.card_le_univ D).trans (Fintype.card_subtype_le _)
  have hR : R.card ≤ Fintype.card ι := (Finset.card_le_univ R).trans (Fintype.card_subtype_le _)
  simp only [List.length_append,ds,rs,squareDonorSchedule,squareReceiverSchedule,List.length_map,Finset.length_toList]
  omega

theorem sharpTransport_schedule_resources {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta)
    (rho H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) (X : ℝ) (hX : 0 ≤ X)
    (cs : List (κ × ℝ)) (x : ι → ℝ) (hc : squareSchedulePositive edges x cs)
    (hcap : ∑ i, x i ≤ X) :
    ∃ path : OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) edges
      (squarePhysicalState t eta H L x)
      (squarePhysicalState t eta H L (chartControlEndpoint edges x cs)),
      path.pairedTurnover ≤ cs.length*X ∧
      ∀ i, path.shareSales i ≤ cs.length*(Real.sqrt (2*eta*X)/eta) := by
  induction cs generalizing x with
  | nil => exact ⟨.refl _,by simp [OriginalPhysicalReachable.pairedTurnover],by intro i;simp [OriginalPhysicalReachable.shareSales]⟩
  | cons c cs ih =>
    obtain ⟨hx,hz,hrest⟩ := hc
    let x' := fun i => x i+c.2*pairedMatrix edges i c.1
    have hx' : ∀ i, 0 < x' i := squareSchedulePositive_start edges _ cs hrest
    have hxi (i : ι) : x i ≤ X := by
      exact (Finset.single_le_sum (fun j _ => (hx j).le) (Finset.mem_univ i)).trans hcap
    have hcap' : ∑ i, x' i ≤ X := by
      simpa only [x',Finset.sum_add_distrib,← Finset.mul_sum,paired_column_sum,mul_zero,add_zero] using hcap
    have hzc : c.2 ≤ X := by
      have hh := hx' (edges c.1).seller
      have hb : pairedMatrix edges (edges c.1).seller c.1 = -1 := by
        simp [pairedMatrix,(edges c.1).distinct]
      dsimp [x'] at hh
      rw [hb] at hh
      linarith [hxi (edges c.1).seller]
    obtain ⟨first,hfirstT,hfirstS⟩ := sharpTransport_single_edge_resources edges c.1 c.2 hz t F eta hF hη
      rho H L x hH hx hx' (Real.sqrt (2*eta*X)) (Real.sqrt_nonneg _) (by
        intro i
        apply Real.sqrt_le_sqrt
        gcongr
        exact hxi i)
    obtain ⟨rest,hrestT,hrestS⟩ := ih x' hrest hcap'
    refine ⟨original_reachable_trans first rest,?_,?_⟩
    · rw [original_reachable_trans_turnover,hfirstT]
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith
    · intro i
      rw [original_reachable_trans_sales]
      have ha := hfirstS i
      have hb := hrestS i
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith

theorem sharpTransport_resource_bounds_state_congr {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t s' t' : PhysicalMarketState ι} (hs : s = s') (ht : t = t') (M V : ℝ) :
    (∃ p : OriginalPhysicalReachable F rho g edges s t,
      p.pairedTurnover ≤ M ∧ ∀ i, p.shareSales i ≤ V) →
    (∃ p : OriginalPhysicalReachable F rho g edges s' t',
      p.pairedTurnover ≤ M ∧ ∀ i, p.shareSales i ≤ V) := by
  subst s';subst t'
  exact id

theorem sharpTransport_uniform_resources {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta) (rho H L x y : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hsum : ∑ i, x i = ∑ i, y i) (X : ℝ) (hX : 0 ≤ X) (hcap : ∑ i, x i ≤ X) :
    ∃ path : OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) completePairedEdges
      (squarePhysicalState t eta H L x) (squarePhysicalState t eta H L y),
      path.pairedTurnover ≤ (2*Fintype.card ι)*X ∧
      ∀ i, path.shareSales i ≤ (2*Fintype.card ι)*(Real.sqrt (2*eta*X)/eta) := by
  obtain ⟨cs,hc,he,hlen⟩ := sharpTransport_exists_short_schedule hub x y hx hy hsum
  obtain ⟨path,hM,hV⟩ := sharpTransport_schedule_resources completePairedEdges t F eta hF hη rho H L hH X hX cs x hc hcap
  have hex : ∃ path : OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) completePairedEdges
      (squarePhysicalState t eta H L x) (squarePhysicalState t eta H L (chartControlEndpoint completePairedEdges x cs)),
      path.pairedTurnover ≤ (2*Fintype.card ι)*X ∧
      ∀ i, path.shareSales i ≤ (2*Fintype.card ι)*(Real.sqrt (2*eta*X)/eta) := by
    refine ⟨path,hM.trans ?_,fun i => (hV i).trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hX
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (div_nonneg (Real.sqrt_nonneg _) hη.le)
  exact sharpTransport_resource_bounds_state_congr rfl (congrArg (squarePhysicalState t eta H L) he) _ _ hex

def sharpTransport_stepEdgeDollars {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t : PhysicalMarketState ι} (p : OriginalPhysicalStep F rho g edges s t) (e : κ) : ℝ :=
  match p with
  | .continuous m _ _ _ _ => m.execution.cumulative e m.b-m.execution.cumulative e m.a
  | .pulse p _ _ _ => p.dollars e

def sharpTransport_traceEdgeDollars {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s : PhysicalMarketState ι} : {t : PhysicalMarketState ι} →
    OriginalPhysicalReachable F rho g edges s t → κ → ℝ
  | _, .refl _, _ => 0
  | _, .append previous step, e => sharpTransport_traceEdgeDollars previous e+sharpTransport_stepEdgeDollars step e

theorem sharpTransport_stepEdgeDollars_bounds {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t : PhysicalMarketState ι} (p : OriginalPhysicalStep F rho g edges s t) (e : κ) :
    0 ≤ sharpTransport_stepEdgeDollars p e ∧ sharpTransport_stepEdgeDollars p e ≤ p.pairedTurnover := by
  cases p with
  | continuous m _ _ _ _ =>
    have hn (e : κ) : 0 ≤ m.execution.cumulative e m.b-m.execution.cumulative e m.a :=
      sub_nonneg.mpr ((m.execution.cumulative e).mono m.time_order)
    exact ⟨hn e,Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ e)⟩
  | pulse p _ _ _ =>
    exact ⟨p.nonnegative_dollars e,Finset.single_le_sum (fun j _ => p.nonnegative_dollars j) (Finset.mem_univ e)⟩

theorem sharpTransport_traceEdgeDollars_bounds {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
    {s t : PhysicalMarketState ι} (p : OriginalPhysicalReachable F rho g edges s t) (e : κ) :
    0 ≤ sharpTransport_traceEdgeDollars p e ∧ sharpTransport_traceEdgeDollars p e ≤ p.pairedTurnover := by
  induction p with
  | refl => exact ⟨le_rfl,le_rfl⟩
  | append previous step ih =>
    have hh := sharpTransport_stepEdgeDollars_bounds step e
    exact ⟨add_nonneg ih.1 hh.1,add_le_add ih.2 hh.2⟩

end MarketCrash








