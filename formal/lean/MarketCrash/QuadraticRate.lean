import MarketCrash.RateBand

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

theorem quadratic_rate_log_bound (b y : ℝ) (hb0 : 0 ≤ b) (hb : b < 1) (hy : |y| ≤ b) :
    -Real.log (1+y) ≤ -y+y^2/(2*(1-b)^2) := by
  let f := fun x : ℝ => Real.log (1+x)-x+x^2/(2*(1-b)^2)
  let d := fun x : ℝ => x*(1+x-(1-b)^2)/((1+x)*(1-b)^2)
  have hbpos : 0 < 1-b := sub_pos.mpr hb
  have hpos : ∀ x ∈ Icc (-b) b, 0 < 1+x := by intro x hx; linarith [hx.1]
  have hd : ∀ x ∈ Icc (-b) b, HasDerivAt f (d x) x := by
    intro x hx
    have hh := (((hasDerivAt_id x).const_add 1).log (hpos x hx).ne').sub (hasDerivAt_id x)
    have hj := hh.add ((hasDerivAt_pow 2 x).div_const (2*(1-b)^2))
    convert hj using 1 <;> dsimp [f,d]
    · field_simp [(hpos x hx).ne',hbpos.ne']
      ring
  have hc : ContinuousOn f (Icc (-b) b) := fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hfactor : ∀ x ∈ Icc (-b) b, 0 ≤ 1+x-(1-b)^2 := by
    intro x hx
    have hh := mul_nonneg hb0 hbpos.le
    nlinarith [hx.1]
  have hzero : f 0 = 0 := by simp [f]
  have hy' := abs_le.mp hy
  have hnonneg : 0 ≤ f y := by
    rcases le_total 0 y with h0y | hy0
    · have hm : MonotoneOn f (Icc 0 b) := by
        have hsub : Icc 0 b ⊆ Icc (-b) b := fun x hx => ⟨by linarith [hx.1],hx.2⟩
        apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := d) (convex_Icc _ _) (hc.mono hsub)
        · intro x hx
          exact (hd x ⟨by linarith [(interior_subset hx).1],(interior_subset hx).2⟩).hasDerivWithinAt
        · intro x hx
          exact div_nonneg (mul_nonneg (interior_subset hx).1
            (hfactor x ⟨by linarith [(interior_subset hx).1],(interior_subset hx).2⟩))
            (mul_pos (hpos x ⟨by linarith [(interior_subset hx).1],(interior_subset hx).2⟩) (sq_pos_of_pos hbpos)).le
      simpa only [hzero] using hm ⟨le_rfl,hb0⟩ ⟨h0y,hy'.2⟩ h0y
    · have hm : AntitoneOn f (Icc (-b) 0) := by
        have hsub : Icc (-b) 0 ⊆ Icc (-b) b := fun x hx => ⟨hx.1,hx.2.trans hb0⟩
        apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := d) (convex_Icc _ _) (hc.mono hsub)
        · intro x hx
          exact (hd x ⟨(interior_subset hx).1,(interior_subset hx).2.trans hb0⟩).hasDerivWithinAt
        · intro x hx
          exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (interior_subset hx).2
            (hfactor x ⟨(interior_subset hx).1,(interior_subset hx).2.trans hb0⟩))
            (mul_pos (hpos x ⟨(interior_subset hx).1,(interior_subset hx).2.trans hb0⟩) (sq_pos_of_pos hbpos)).le
      simpa only [hzero] using hm ⟨hy'.1,hy0⟩ ⟨by linarith,le_rfl⟩ hy0
  dsimp [f] at hnonneg
  linarith

theorem quadratic_rate_scalar_deviation {S w : ℝ → ℝ} {C : ℝ≥0}
    (F rho A t : ℝ) (hρ : 0 < rho) (ht : 0 ≤ t)
    (hS : LipschitzOnWith C S (Icc 0 t)) (hzero : S 0 = F)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo 0 t → HasDerivAt S (w x) x)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc 0 t → |w x+rho*(S x-F)| ≤ A) :
    |S t-F| ≤ A/rho*(1-Real.exp (-rho*t)) := by
  have hl := rateBand_scalar_floor F rho A t hρ ht hS hzero hd (by
    filter_upwards [hb] with x hx hmem
    have hh := (abs_le.mp (hx hmem)).1
    linarith)
  have hL : LipschitzOnWith C (fun x => 2*F-S x) (Icc 0 t) := by
    simpa only [zero_add] using ((LipschitzWith.const (2*F)).lipschitzOnWith.sub hS)
  have hD : ∀ᵐ x ∂volume, x ∈ Ioo 0 t → HasDerivAt (fun x => 2*F-S x) (-w x) x := by
    filter_upwards [hd] with x hx hmem
    simpa only [zero_sub] using (hasDerivAt_const x (2*F)).sub (hx hmem)
  have hu := rateBand_scalar_floor F rho A t hρ ht hL (by rw [hzero];ring) hD (by
    filter_upwards [hb] with x hx hmem
    have hh := (abs_le.mp (hx hmem)).2
    nlinarith)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

def quadraticMeanEnvelope (rho B t : ℝ) : ℝ :=
  B/rho*(1-Real.exp (-rho*t)-rho*t*Real.exp (-rho*t))

theorem quadraticMeanEnvelope_derivative (rho B t : ℝ) (hρ : rho ≠ 0) :
    HasDerivAt (quadraticMeanEnvelope rho B) (B*rho*t*Real.exp (-rho*t)) t := by
  have he := ((hasDerivAt_id t).const_mul (-rho)).exp
  have hh := (((hasDerivAt_const t 1).sub he).sub
    (((hasDerivAt_id t).const_mul rho).mul he)).const_mul (B/rho)
  convert hh using 1 <;> dsimp [quadraticMeanEnvelope]
  field_simp [hρ]
  ring

theorem quadraticMeanEnvelope_lipschitz (rho B t : ℝ) (hρ : rho ≠ 0) :
    ∃ C : ℝ≥0, LipschitzOnWith C (quadraticMeanEnvelope rho B) (Icc 0 t) := by
  have hc : ContinuousOn (fun x => ‖B*rho*x*Real.exp (-rho*x)‖) (Icc 0 t) := by fun_prop
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image hc
  let C : ℝ≥0 := ⟨max D 0,le_max_right _ _⟩
  refine ⟨C,(convex_Icc 0 t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun x _ => (quadraticMeanEnvelope_derivative rho B x hρ).hasDerivWithinAt) ?_⟩
  intro x hx
  exact (hD (mem_image_of_mem _ hx)).trans (le_max_left _ _)

theorem quadratic_mean_upper_of_forcing {m w : ℝ → ℝ} {C : ℝ≥0}
    (rho B t : ℝ) (hρ : 0 < rho) (ht : 0 ≤ t)
    (hm : LipschitzOnWith C m (Icc 0 t)) (h0 : m 0 = 0)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo 0 t → HasDerivAt m (w x) x)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc 0 t → w x+rho*m x ≤ B*(1-Real.exp (-rho*x))) :
    m t ≤ quadraticMeanEnvelope rho B t := by
  obtain ⟨D,hD⟩ := quadraticMeanEnvelope_lipschitz rho B t hρ.ne'
  have hh := rateBand_nonnegative_of_derivative_ge_linear (rho := rho) ht (hD.sub hm) (by
    filter_upwards [hd] with x hx hmem
    exact (quadraticMeanEnvelope_derivative rho B x hρ.ne').sub (hx hmem)) (by
    filter_upwards [hb] with x hx hmem
    have he : B*rho*x*Real.exp (-rho*x)+rho*quadraticMeanEnvelope rho B x =
        B*(1-Real.exp (-rho*x)) := by dsimp [quadraticMeanEnvelope];field_simp [hρ.ne'];ring
    have hb' := hx hmem
    linarith) (by simp [quadraticMeanEnvelope,h0])
  exact sub_nonneg.mp hh

theorem quadratic_mean_abs_of_forcing {m w : ℝ → ℝ} {C : ℝ≥0}
    (rho B t : ℝ) (hρ : 0 < rho) (ht : 0 ≤ t)
    (hm : LipschitzOnWith C m (Icc 0 t)) (h0 : m 0 = 0)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo 0 t → HasDerivAt m (w x) x)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc 0 t → |w x+rho*m x| ≤ B*(1-Real.exp (-rho*x))) :
    |m t| ≤ quadraticMeanEnvelope rho B t := by
  have hu := quadratic_mean_upper_of_forcing rho B t hρ ht hm h0 hd (by
    filter_upwards [hb] with x hx hmem
    exact (abs_le.mp (hx hmem)).2)
  have hl := quadratic_mean_upper_of_forcing (m := fun x => -m x) (w := fun x => -w x)
    rho B t hρ ht hm.neg (by simp [h0]) (by
      filter_upwards [hd] with x hx hmem
      exact (hx hmem).neg) (by
      filter_upwards [hb] with x hx hmem
      have hh := (abs_le.mp (hx hmem)).1
      linarith)
  change -m t ≤ quadraticMeanEnvelope rho B t at hl
  exact abs_le.mpr ⟨by linarith,hu⟩

theorem quadratic_paired_mean_forcing {ι : Type*} [Fintype ι]
    (S q : ι → ℝ) (F eta v D : ℝ) (hF : 0 < F) (hη : 0 ≤ eta)
    (hv : 0 ≤ v) (hD : 0 ≤ D) (hpair : ∑ i, S i*q i = 0)
    (hdev : ∀ i, |S i-F| ≤ D) (hq : ∀ i, |q i| ≤ v) :
    |eta*∑ i, q i| ≤ (Fintype.card ι : ℝ)*eta*D*v/F := by
  have hid : F*(∑ i, q i) = -∑ i, (S i-F)*q i := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hpair]
    ring
  have hb : |F*(∑ i, q i)| ≤ (Fintype.card ι : ℝ)*D*v := by
    rw [hid, abs_neg]
    calc
      |∑ i, (S i-F)*q i| ≤ ∑ i, |(S i-F)*q i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, D*v := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul (hdev i) (hq i) (abs_nonneg _) hD
      _ = (Fintype.card ι : ℝ)*D*v := by simp;ring
  have hb' : |∑ i, q i| ≤ (Fintype.card ι : ℝ)*D*v/F := by
    rw [le_div_iff₀ hF]
    simpa only [abs_mul,abs_of_pos hF,mul_comm] using hb
  rw [abs_mul,abs_of_nonneg hη]
  calc
    eta*|∑ i, q i| ≤ eta*((Fintype.card ι : ℝ)*D*v/F) := mul_le_mul_of_nonneg_left hb' hη
    _ = _ := by ring

theorem ACPhysicalSession.net_share_rate_bound {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] {edges : κ → PairedEdge ι}
    (m : ACPhysicalSession edges) (v : ℝ) (hv : m.RateBounded v) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → ∀ i,
      |tradingInput (pairedMatrix edges) (m.rates t) i / m.prices t i| ≤ v := by
  filter_upwards [m.local_capacity,hv.2] with t ht hc hmem i
  have hp := m.positive_prices t hmem i
  rw [abs_div,abs_of_pos hp,div_le_iff₀ hp]
  exact (ht hmem i).2.trans (by nlinarith [hc hmem i])

theorem ACPhysicalSession.constant_impact_deviation {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] {edges : κ → PairedEdge ι}
    (m : ACPhysicalSession edges) (F rho eta v : ℝ)
    (hρ : 0 < rho) (hη : 0 ≤ eta) (hv : m.RateBounded v)
    (ha : m.a = 0) (hF : ∀ i, m.F i = F) (hr : ∀ i, m.rho i = rho)
    (hg : ∀ i x, 0 < x → (m.response i).impact x = eta)
    (h0 : ∀ i, m.prices 0 i = F) :
    ∀ t ∈ Icc 0 m.b, ∀ i,
      |m.prices t i-F| ≤ eta*v/rho*(1-Real.exp (-rho*t)) := by
  intro t ht i
  obtain ⟨C,hC⟩ := m.prices_lipschitz v hv i
  have hsub : Icc 0 t ⊆ Icc m.a m.b := by
    intro x hx
    rw [ha]
    exact ⟨hx.1,hx.2.trans ht.2⟩
  let w := fun x => -rho*(m.prices x i-F)+eta*
    (tradingInput (pairedMatrix edges) (m.rates x) i/m.prices x i)
  apply quadratic_rate_scalar_deviation F rho (eta*v) t hρ ht.1 (hC.mono hsub) (h0 i)
  · filter_upwards [m.physical_derivative] with x hx hmem
    have hm := hsub (Ioo_subset_Icc_self hmem)
    simpa only [w,hr i,hF i,hg i _ (m.positive_prices x hm i)] using hx hm i
  · filter_upwards [m.net_share_rate_bound v hv] with x hx hmem
    have hm := hsub hmem
    have he : w x+rho*(m.prices x i-F) = eta*
        (tradingInput (pairedMatrix edges) (m.rates x) i/m.prices x i) := by dsimp [w];ring
    rw [he,abs_mul,abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left (hx hm i) hη

theorem quadratic_mean_log_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (y : ι → ℝ) (b M : ℝ) (hb0 : 0 ≤ b) (hb : b < 1)
    (hy : ∀ i, |y i| ≤ b) (hm : |∑ i, y i| ≤ (Fintype.card ι : ℝ)*M) :
    meanLogLoss (fun i => Real.log (1+y i)) ≤ M+b^2/(2*(1-b)^2) := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hden : 0 < 2*(1-b)^2 := mul_pos (by norm_num) (sq_pos_of_pos (sub_pos.mpr hb))
  have hs : ∑ i, -Real.log (1+y i) ≤
      -(∑ i, y i)+(Fintype.card ι : ℝ)*(b^2/(2*(1-b)^2)) := by
    calc
      ∑ i, -Real.log (1+y i) ≤ ∑ i, (-y i+b^2/(2*(1-b)^2)) := by
        apply Finset.sum_le_sum
        intro i _
        have hi := quadratic_rate_log_bound b (y i) hb0 hb (hy i)
        have hsq : (y i)^2 ≤ b^2 := by nlinarith [abs_le.mp (hy i),sq_abs (y i)]
        exact hi.trans (add_le_add_left (div_le_div_of_nonneg_right hsq hden.le) _)
      _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_neg_distrib]
  have hm' := (abs_le.mp hm).1
  unfold meanLogLoss
  rw [div_le_iff₀ hn]
  rw [← Finset.sum_neg_distrib]
  nlinarith

theorem finite_price_deviation_lipschitz {ι : Type*} [Fintype ι]
    (S : ℝ → ι → ℝ) (F : ℝ) (a b : ℝ)
    (hS : ∀ i, ∃ C : ℝ≥0, LipschitzOnWith C (fun t => S t i) (Icc a b)) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun t => ∑ i, (S t i-F)) (Icc a b) := by
  classical
  choose C hC using hS
  have hs : ∀ J : Finset ι, LipschitzOnWith (∑ i ∈ J, C i)
      (fun t => ∑ i ∈ J, (S t i-F)) (Icc a b) := by
    intro J
    induction J using Finset.induction_on with
    | empty => simpa using (LipschitzWith.const (0 : ℝ)).lipschitzOnWith (s := Icc a b)
    | @insert i J hi ih =>
      simpa only [Finset.sum_insert hi,add_zero] using
        ((hC i).sub (LipschitzWith.const F).lipschitzOnWith).add ih
  exact ⟨∑ i, C i,by simpa using hs Finset.univ⟩

theorem quadratic_mean_deviation_of_paired_rates {ι : Type*} [Fintype ι]
    (S q : ℝ → ι → ℝ) (F rho eta v T : ℝ)
    (hF : 0 < F) (hρ : 0 < rho) (hη : 0 ≤ eta) (hv : 0 ≤ v) (hT : 0 ≤ T)
    (hLip : ∀ i, ∃ C : ℝ≥0, LipschitzOnWith C (fun t => S t i) (Icc 0 T))
    (h0 : ∀ i, S 0 i = F)
    (hd : ∀ᵐ t ∂volume, t ∈ Ioo 0 T → ∀ i,
      HasDerivAt (fun t => S t i) (-rho*(S t i-F)+eta*q t i) t)
    (hq : ∀ᵐ t ∂volume, t ∈ Icc 0 T → ∀ i, |q t i| ≤ v)
    (hpair : ∀ᵐ t ∂volume, t ∈ Icc 0 T → ∑ i, S t i*q t i = 0)
    (hdev : ∀ t ∈ Icc 0 T, ∀ i, |S t i-F| ≤ eta*v/rho*(1-Real.exp (-rho*t))) :
    |∑ i, (S T i-F)| ≤ quadraticMeanEnvelope rho
      ((Fintype.card ι : ℝ)*eta^2*v^2/(F*rho)) T := by
  obtain ⟨C,hC⟩ := finite_price_deviation_lipschitz S F 0 T hLip
  apply quadratic_mean_abs_of_forcing rho _ T hρ hT hC
    (by simp [h0])
  · filter_upwards [hd] with t ht hm
    exact HasDerivAt.sum (u := Finset.univ) (fun i _ => (ht hm i).sub_const F)
  · filter_upwards [hq,hpair] with t ht hp hm
    have hd0 : 0 ≤ eta*v/rho*(1-Real.exp (-rho*t)) :=
      mul_nonneg (div_nonneg (mul_nonneg hη hv) hρ.le)
        (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith [hm.1])))
    have hb := quadratic_paired_mean_forcing (S t) (q t) F eta v
      (eta*v/rho*(1-Real.exp (-rho*t))) hF hη hv hd0 (hp hm) (hdev t hm) (ht hm)
    have he : (∑ i, (-rho*(S t i-F)+eta*q t i))+rho*(∑ i, (S t i-F)) =
        eta*∑ i, q t i := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    rw [he]
    convert hb using 1 <;> ring

theorem quadratic_crisis_from_price_deviations {ι : Type*} [Fintype ι] [Nonempty ι]
    (S : ι → ℝ) (F b M : ℝ) (hF : 0 < F) (hb0 : 0 ≤ b) (hb : b < 1)
    (hdev : ∀ i, |S i-F| ≤ F*b)
    (hmean : |∑ i, (S i-F)| ≤ (Fintype.card ι : ℝ)*F*M) (k : ℕ) :
    systemicCrisis (logPriceFromBenchmark F S) k ≤ M+b^2/(2*(1-b)^2) := by
  let y := fun i => (S i-F)/F
  have hy : ∀ i, |y i| ≤ b := by
    intro i
    dsimp [y]
    rw [abs_div,abs_of_pos hF,div_le_iff₀ hF]
    simpa only [mul_comm] using hdev i
  have hm : |∑ i, y i| ≤ (Fintype.card ι : ℝ)*M := by
    dsimp [y]
    rw [← Finset.sum_div,abs_div,abs_of_pos hF,div_le_iff₀ hF]
    nlinarith
  have he : logPriceFromBenchmark F S = fun i => Real.log (1+y i) := by
    funext i
    dsimp only [logPriceFromBenchmark]
    congr 1
    dsimp [y]
    field_simp [hF.ne']
  rw [he]
  exact (systemicCrisis_le_meanLogLoss _ k).trans (quadratic_mean_log_bound y b M hb0 hb hy hm)

/-- The universal upper-bound clause of Theorem 6.2; attained order is separate. -/
theorem theorem_6_2_original_upper {ι κ : Type*}
    [Fintype ι] [Nonempty ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (F rho eta v : ℝ) (hF : 0 < F) (hρ : 0 < rho) (hη : 0 ≤ eta)
    (hv : m.RateBounded v) (ha : m.a = 0)
    (hFi : ∀ i, m.F i = F) (hri : ∀ i, m.rho i = rho)
    (hg : ∀ i x, 0 < x → (m.response i).impact x = eta)
    (h0 : ∀ i, m.prices 0 i = F)
    (hb : eta*v/(F*rho)*(1-Real.exp (-rho*m.b)) < 1) (k : ℕ) :
    systemicCrisis (logPriceFromBenchmark F (m.prices m.b)) k ≤
      (eta*v/(F*rho))^2 * ((1-Real.exp (-rho*m.b))-
        rho*m.b*Real.exp (-rho*m.b)+
        (1-Real.exp (-rho*m.b))^2/
          (2*(1-eta*v/(F*rho)*(1-Real.exp (-rho*m.b)))^2)) := by
  have hT : 0 < m.b := by linarith [m.time_order]
  let d := 1-Real.exp (-rho*m.b)
  let b := eta*v/(F*rho)*d
  let M := (eta*v/(F*rho))^2*(d-rho*m.b*Real.exp (-rho*m.b))
  let q := fun t i => tradingInput (pairedMatrix edges) (m.rates t) i/m.prices t i
  have hdev := m.constant_impact_deviation F rho eta v hρ hη hv ha hFi hri hg h0
  have hm := quadratic_mean_deviation_of_paired_rates m.prices q F rho eta v m.b
    hF hρ hη hv.1 hT.le (by simpa only [ha] using fun i => m.prices_lipschitz v hv i)
    h0 (by
      filter_upwards [m.physical_derivative] with t ht hmem i
      have hm : t ∈ Icc m.a m.b := by rw [ha];exact Ioo_subset_Icc_self hmem
      simpa only [q,hri i,hFi i,hg i _ (m.positive_prices t hm i)] using ht hm i)
    (by simpa only [ha] using m.net_share_rate_bound v hv)
    (by
      filter_upwards [] with t hmem
      have hm : t ∈ Icc m.a m.b := by simpa only [ha] using hmem
      have he : ∑ i, m.prices t i*q t i = ∑ i, tradingInput (pairedMatrix edges) (m.rates t) i := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp [q]
        field_simp [(m.positive_prices t hm i).ne']
      rw [he]
      exact paired_trading_sum_zero edges (m.rates t)) hdev
  have he : quadraticMeanEnvelope rho ((Fintype.card ι : ℝ)*eta^2*v^2/(F*rho)) m.b =
      (Fintype.card ι : ℝ)*F*M := by
    dsimp [quadraticMeanEnvelope,M,d]
    field_simp [hF.ne',hρ.ne']
    ring
  rw [he] at hm
  have hd : 0 ≤ d := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by nlinarith))
  have hb0 : 0 ≤ b := mul_nonneg (div_nonneg (mul_nonneg hη hv.1) (mul_pos hF hρ).le) hd
  have hu := quadratic_crisis_from_price_deviations (m.prices m.b) F b M hF hb0 hb (by
    intro i
    have hi := hdev m.b ⟨hT.le,le_rfl⟩ i
    have he : F*b = eta*v/rho*d := by dsimp [b];field_simp [hF.ne',hρ.ne'];ring
    rw [he]
    exact hi) hm k
  convert hu using 1 <;> dsimp [M,b,d] <;> ring

theorem quadratic_coefficient_uniform (A v d z : ℝ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (hz : 0 ≤ z) (hb : A*v*d ≤ 1/2) :
    (A*v)^2*(d-z+d^2/(2*(1-A*v*d)^2)) ≤ 3*A^2*v^2 := by
  have hpos : 0 < 1-A*v*d := by linarith
  have hp : 0 < 2*(1-A*v*d)^2 := mul_pos (by norm_num) (sq_pos_of_pos hpos)
  have hl : (1:ℝ)/2 ≤ 2*(1-A*v*d)^2 := by nlinarith [sq_nonneg (1-A*v*d-1/2)]
  have hs : d^2 ≤ 1 := by nlinarith
  have hf : d^2/(2*(1-A*v*d)^2) ≤ 2 := by
    rw [div_le_iff₀ hp]
    linarith
  have hsum : d-z+d^2/(2*(1-A*v*d)^2) ≤ 3 := by linarith
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (A*v))
  nlinarith

end MarketCrash
