import MarketCrash.RateBand

noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace MarketCrash

theorem rollingRate_single_session_algebra (F rho eta v s tau beta S : ℝ)
    (hrho : 0 < rho) (heta : 0 < eta) (htau : 0 < tau) (hv : 0 ≤ v)
    (hfloor : F + (s - F) * Real.exp (-rho * tau) -
      eta * v / rho * (1 - Real.exp (-rho * tau)) ≤ S)
    (hclose : S ≤ (1 - beta) * s) :
    max 0 (rho / eta * (F - s + beta * s / (1 - Real.exp (-rho * tau)))) ≤ v := by
  apply max_le hv
  have hd : 0 < 1 - Real.exp (-rho * tau) := by
    have := Real.exp_lt_one_iff.mpr (show -rho * tau < 0 by nlinarith)
    linarith
  have hh := hfloor.trans hclose
  have hmul := mul_le_mul_of_nonneg_right hh hrho.le
  have he : eta * v / rho * rho = eta * v := div_mul_cancel₀ _ hrho.ne'
  apply (mul_le_mul_right heta).mp
  have hdv : beta * s / (1 - Real.exp (-rho * tau)) * (1 - Real.exp (-rho * tau)) = beta * s :=
    div_mul_cancel₀ _ hd.ne'
  have ht : (rho / eta * (F - s + beta * s / (1 - Real.exp (-rho * tau)))) * eta =
      rho * (F - s + beta * s / (1 - Real.exp (-rho * tau))) := by field_simp
  rw [ht]
  apply (mul_le_mul_right hd).mp
  nlinarith

theorem rollingRate_scalar_floor_from {S w : ℝ → ℝ} {C : ℝ≥0}
    (F rho A s a t : ℝ) (hrho : 0 < rho) (ht : a ≤ t)
    (hS : LipschitzOnWith C S (Icc a t)) (hzero : S a = s)
    (hd : ∀ᵐ x ∂volume, x ∈ Ioo a t → HasDerivAt S (w x) x)
    (hb : ∀ᵐ x ∂volume, x ∈ Icc a t → -rho * (S x - F) - A ≤ w x) :
    F + (s - F) * Real.exp (-rho * (t - a)) -
      A / rho * (1 - Real.exp (-rho * (t - a))) ≤ S t := by
  let B := s - F + A / rho
  let e := fun x => Real.exp (-rho * (x - a))
  let H := fun x => S x - (F - A / rho) - B * e x
  obtain ⟨D, hD⟩ := rateBand_exp_lipschitz (-rho) a t
  have hc : LipschitzOnWith 0 (fun _ : ℝ => B * Real.exp (rho * a)) (Icc a t) :=
    (LipschitzWith.const _).lipschitzOnWith
  obtain ⟨E, hE⟩ := rateBand_lipschitz_mul hc hD
  have heq : (fun x => B * Real.exp (rho * a) * Real.exp (-rho * x)) = fun x => B * e x := by
    funext x
    dsimp [e]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at hE
  have hH : LipschitzOnWith (C + E) H (Icc a t) := by
    have hc' : LipschitzOnWith 0 (fun _ : ℝ => F - A / rho) (Icc a t) :=
      (LipschitzWith.const (F - A / rho)).lipschitzOnWith
    simpa [H] using (hS.sub hc').sub hE
  let W := fun x => w x + B * rho * e x
  have hHd : ∀ᵐ x ∂volume, x ∈ Ioo a t → HasDerivAt H (W x) x := by
    filter_upwards [hd] with x hx hmem
    convert ((hx hmem).sub_const (F - A / rho)).sub
      (((((hasDerivAt_id x).sub_const a).const_mul (-rho)).exp).const_mul B) using 1 <;> dsimp [H, W, e] <;> ring
  have hHb : ∀ᵐ x ∂volume, x ∈ Icc a t → -rho * H x ≤ W x := by
    filter_upwards [hb] with x hx hmem
    have hAr : A / rho * rho = A := div_mul_cancel₀ A hrho.ne'
    dsimp [H, W]
    nlinarith [hx hmem]
  have hH0 : 0 ≤ H a := by simp [H, B, e, hzero]; ring_nf; exact le_refl _
  have hh := rateBand_nonnegative_of_derivative_ge_linear ht hH hHd hHb hH0
  dsimp [H, B, e] at hh
  nlinarith

theorem ACPhysicalSession.rolling_rate_floor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v eta : ℝ) (hv : m.RateBounded v) (heta : 0 < eta)
    (i : ι) (hrho : 0 < m.rho i)
    (himpact : ∀ x ∈ Icc m.a m.b, (m.response i).impact (m.prices x i) = eta) :
    m.F i + (m.prices m.a i - m.F i) * Real.exp (-m.rho i * (m.b - m.a)) -
      eta * v / m.rho i * (1 - Real.exp (-m.rho i * (m.b - m.a))) ≤ m.prices m.b i := by
  obtain ⟨C, hC⟩ := m.prices_lipschitz v hv i
  apply rollingRate_scalar_floor_from (m.F i) (m.rho i) (eta * v) (m.prices m.a i)
    m.a m.b hrho m.time_order.le hC rfl
  · filter_upwards [m.physical_derivative] with x hx hmem
    exact hx ⟨hmem.1.le, hmem.2.le⟩ i
  · filter_upwards [m.local_capacity, hv.2] with x hx hcap hmem
    have hp := m.positive_prices x hmem i
    have hn : -v ≤ tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i := by
      have habs : |tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i| ≤ v := by
        rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
        exact (hx hmem i).2.trans (by nlinarith [hcap hmem i])
      exact (abs_le.mp habs).1
    rw [himpact x hmem]
    nlinarith [mul_le_mul_of_nonneg_left hn heta.le]

theorem proposition_7_2_single_session
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v eta beta : ℝ) (hv : m.RateBounded v) (heta : 0 < eta)
    (i : ι) (hrho : 0 < m.rho i)
    (himpact : ∀ x ∈ Icc m.a m.b, (m.response i).impact (m.prices x i) = eta)
    (hclose : m.prices m.b i ≤ (1 - beta) * m.prices m.a i) :
    max 0 (m.rho i / eta * (m.F i - m.prices m.a i +
      beta * m.prices m.a i / (1 - Real.exp (-m.rho i * (m.b - m.a))))) ≤ v := by
  exact rollingRate_single_session_algebra _ _ _ _ _ _ _ _ hrho heta
    (sub_pos.mpr m.time_order) hv.1 (m.rolling_rate_floor v eta hv heta i hrho himpact) hclose

theorem rollingRate_streak_algebra (F rho eta tau q v : ℝ) (d : ℕ)
    (_heta : 0 < eta)
    (h : max 0 (rho / eta * (F - F * q ^ (d - 1) +
      (1 - q) * (F * q ^ (d - 1)) / (1 - Real.exp (-rho * tau)))) ≤ v) :
    rho * F / eta * (1 + q ^ (d - 1) * ((1 - q) / (1 - Real.exp (-rho * tau)) - 1)) ≤ v := by
  have hh := (le_max_right 0 _).trans h
  have he : rho * F / eta * (1 + q ^ (d - 1) * ((1 - q) / (1 - Real.exp (-rho * tau)) - 1)) =
      rho / eta * (F - F * q ^ (d - 1) + (1 - q) * (F * q ^ (d - 1)) /
        (1 - Real.exp (-rho * tau))) := by ring
  rw [he]
  exact hh

theorem rollingRate_streak_max (F rho eta tau q v : ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hday : ∀ d ∈ Finset.Icc 1 D,
      rho * F / eta * (1 + q ^ (d - 1) * ((1 - q) / (1 - Real.exp (-rho * tau)) - 1)) ≤ v) :
    rho * F / eta * (Finset.Icc 1 D).sup' ⟨1, by simp [hD]⟩
      (fun d => 1 + q ^ (d - 1) * ((1 - q) / (1 - Real.exp (-rho * tau)) - 1)) ≤ v := by
  obtain ⟨d, hd, heq⟩ := Finset.exists_mem_eq_sup' (s := Finset.Icc 1 D)
    ⟨1, by simp [hD]⟩ (fun d => 1 + q ^ (d - 1) * ((1 - q) / (1 - Real.exp (-rho * tau)) - 1))
  rw [heq]
  exact hday d hd

theorem ACPhysicalSession.perpetual_rate_floor
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v eta : ℝ) (hv : m.RateBounded v) (heta : 0 < eta)
    (i : ι) (hrho : 0 < m.rho i) (hstart : m.prices m.a i = m.F i)
    (himpact : ∀ x ∈ Icc m.a m.b, (m.response i).impact (m.prices x i) = eta) :
    m.F i - eta * v / m.rho i ≤ m.prices m.b i := by
  have hh := m.rolling_rate_floor v eta hv heta i hrho himpact
  rw [hstart, sub_self, zero_mul, add_zero] at hh
  have hn : 0 ≤ eta * v / m.rho i := div_nonneg (mul_nonneg heta.le hv.1) hrho.le
  nlinarith [Real.exp_pos (-m.rho i * (m.b - m.a))]

theorem rollingRate_integer_streak_bound (F rho eta v q : ℝ) (D : ℕ)
    (hF : 0 < F) (hrho : 0 < rho) (hq : 0 < q) (hq1 : q < 1)
    (hcap : eta * v < rho * F)
    (hfloor : F - eta * v / rho ≤ F * q ^ D) :
    (D : ℝ) ≤ Real.log (1 - eta * v / (rho * F)) / Real.log q := by
  have hden : 0 < rho * F := mul_pos hrho hF
  have hp : 0 < 1 - eta * v / (rho * F) := by
    have := (div_lt_one hden).mpr hcap
    linarith
  have heq : (F - eta * v / rho) / F = 1 - eta * v / (rho * F) := by field_simp; ring
  have hh : 1 - eta * v / (rho * F) ≤ q ^ D := by
    rw [← heq]
    apply (div_le_iff₀ hF).mpr
    simpa [mul_comm] using hfloor
  have hl := Real.log_le_log hp hh
  rw [Real.log_pow] at hl
  exact (le_div_iff_of_neg (Real.log_neg hq hq1)).mpr (by simpa [mul_comm] using hl)

/-- The D-session maximum is necessary for the actual finite family of physical sessions. -/
theorem proposition_7_2_rolling_streak
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (sessions : ℕ → ACPhysicalSession edges)
    (F rho eta tau q v : ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hrho : 0 < rho) (heta : 0 < eta) (i : ι)
    (hF : ∀ d ∈ Finset.Icc 1 D, (sessions d).F i = F)
    (hri : ∀ d ∈ Finset.Icc 1 D, (sessions d).rho i = rho)
    (htau : ∀ d ∈ Finset.Icc 1 D, (sessions d).b - (sessions d).a = tau)
    (hcap : ∀ d ∈ Finset.Icc 1 D, (sessions d).RateBounded v)
    (himpact : ∀ d ∈ Finset.Icc 1 D, ∀ x ∈ Icc (sessions d).a (sessions d).b,
      ((sessions d).response i).impact ((sessions d).prices x i) = eta)
    (hstart : ∀ d ∈ Finset.Icc 1 D, (sessions d).prices (sessions d).a i = F * q ^ (d - 1))
    (hclose : ∀ d ∈ Finset.Icc 1 D,
      (sessions d).prices (sessions d).b i ≤ q * (sessions d).prices (sessions d).a i) :
    rho * F / eta * (Finset.Icc 1 D).sup' ⟨1, by simp [hD]⟩
      (fun d => 1 + q ^ (d - 1) * ((1 - q) / (1 - Real.exp (-rho * tau)) - 1)) ≤ v := by
  apply rollingRate_streak_max F rho eta tau q v D hD
  intro d hd
  have hh := proposition_7_2_single_session (sessions d) v eta (1 - q)
    (hcap d hd) heta i (by rw [hri d hd]; exact hrho) (himpact d hd)
    (by simpa using hclose d hd)
  rw [hF d hd, hri d hd, htau d hd, hstart d hd] at hh
  exact rollingRate_streak_algebra F rho eta tau q v d heta hh

theorem ACPhysicalSession.perpetual_rate_floor_at
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v eta : ℝ) (hv : m.RateBounded v) (heta : 0 < eta)
    (i : ι) (hrho : 0 < m.rho i) (hstart : m.prices m.a i = m.F i)
    (himpact : ∀ x ∈ Icc m.a m.b, (m.response i).impact (m.prices x i) = eta)
    (t : ℝ) (ht : t ∈ Icc m.a m.b) :
    m.F i - eta * v / m.rho i ≤ m.prices t i := by
  obtain ⟨C, hC⟩ := m.prices_lipschitz v hv i
  have hsub : Icc m.a t ⊆ Icc m.a m.b := fun x hx => ⟨hx.1, hx.2.trans ht.2⟩
  have hd : ∀ᵐ x ∂volume, x ∈ Ioo m.a t → HasDerivAt (fun x => m.prices x i)
      (-m.rho i * (m.prices x i - m.F i) + (m.response i).impact (m.prices x i) *
        (tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i)) x := by
    filter_upwards [m.physical_derivative] with x hx hmem
    exact hx (hsub ⟨hmem.1.le, hmem.2.le⟩) i
  have hb : ∀ᵐ x ∂volume, x ∈ Icc m.a t →
      -m.rho i * (m.prices x i - m.F i) - eta * v ≤
      -m.rho i * (m.prices x i - m.F i) + (m.response i).impact (m.prices x i) *
        (tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i) := by
    filter_upwards [m.local_capacity, hv.2] with x hx hcap hmem
    have hm := hsub hmem
    have hp := m.positive_prices x hm i
    have hn : -v ≤ tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i := by
      have habs : |tradingInput (pairedMatrix edges) (m.rates x) i / m.prices x i| ≤ v := by
        rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
        exact (hx hm i).2.trans (by nlinarith [hcap hm i])
      exact (abs_le.mp habs).1
    rw [himpact x hm]
    nlinarith [mul_le_mul_of_nonneg_left hn heta.le]
  have hh := rollingRate_scalar_floor_from (m.F i) (m.rho i) (eta * v) (m.F i)
    m.a t hrho ht.1 (hC.mono hsub) hstart hd hb
  simp only [sub_self, zero_mul, add_zero] at hh
  have hn : 0 ≤ eta * v / m.rho i := div_nonneg (mul_nonneg heta.le hv.1) hrho.le
  nlinarith [Real.exp_pos (-m.rho i * (t - m.a))]

/-- The perpetual floor and integer streak exclusion come from actual
physical execution; the cap condition is used only for the logarithmic bound. -/
theorem proposition_7_2_perpetual_and_integer
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι} (m : ACPhysicalSession edges)
    (v eta q : ℝ) (D : ℕ) (hv : m.RateBounded v) (heta : 0 < eta)
    (i : ι) (hrho : 0 < m.rho i) (hq : 0 < q) (hq1 : q < 1)
    (hstart : m.prices m.a i = m.F i)
    (himpact : ∀ x ∈ Icc m.a m.b, (m.response i).impact (m.prices x i) = eta)
    (hclose : m.prices m.b i ≤ m.F i * q ^ D)
    (hcap : eta * v < m.rho i * m.F i) :
    (∀ t ∈ Icc m.a m.b, m.F i - eta * v / m.rho i ≤ m.prices t i) ∧
    (D : ℝ) ≤ Real.log (1 - eta * v / (m.rho i * m.F i)) / Real.log q := by
  have hh := m.perpetual_rate_floor v eta hv heta i hrho hstart himpact
  exact ⟨m.perpetual_rate_floor_at v eta hv heta i hrho hstart himpact,
    rollingRate_integer_streak_bound (m.F i) (m.rho i) eta v q D
    (m.benchmark_positive i) hrho hq hq1 hcap (hh.trans hclose)⟩

end MarketCrash
