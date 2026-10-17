import MarketCrash.ACPhysicalSession
import MarketCrash.LipschitzFTC
import MarketCrash.MarketCutSpecialization

noncomputable section
namespace MarketCrash
open MeasureTheory Set Finset
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

theorem ACPhysicalSession.flow_integrable (m : ACPhysicalSession edges) (i : ι) :
    IntervalIntegrable (fun t => tradingInput (pairedMatrix edges) (m.rates t) i)
      volume m.a m.b := by
  simpa only [Finset.sum_fn, tradingInput] using IntervalIntegrable.sum Finset.univ
    (f := fun e t => pairedMatrix edges i e * m.rates t e)
    (fun e _ => (m.rates_integrable e).const_mul _)

theorem ACPhysicalSession.ledger_endpoint (m : ACPhysicalSession edges) (i : ι) :
    m.ledger m.b i = ∫ t in m.a..m.b,
      tradingInput (pairedMatrix edges) (m.rates t) i := by
  simp only [ACPhysicalSession.ledger, tradingInput]
  rw [intervalIntegral.integral_finset_sum (fun e _ => (m.rates_integrable e).const_mul _)]
  apply sum_congr rfl
  intro e _
  rw [intervalIntegral.integral_const_mul, m.edge_primitive e m.b ⟨m.time_order.le, le_rfl⟩]

def ACPhysicalSession.recovery (m : ACPhysicalSession edges) (t : ℝ) (i : ι) : ℝ :=
  m.rho i * (m.prices t i * (m.prices t i - m.F i) /
    (m.response i).impact (m.prices t i))

theorem ACPhysicalSession.recovery_continuous (m : ACPhysicalSession edges) (i : ι) :
    ContinuousOn (fun t => m.recovery t i) (Icc m.a m.b) := by
  apply continuousOn_const.mul
  apply ((m.continuous_prices i).mul ((m.continuous_prices i).sub continuousOn_const)).div
  · exact (m.response i).continuousOn_positive.comp (m.continuous_prices i)
      (fun t ht => m.positive_prices t ht i)
  · intro t ht
    exact ((m.response i).positive _ (m.positive_prices t ht i)).ne'

/-- The integrated price-response law is derived from the original
physical primitive and a.e. ODE, using the proved Lipschitz FTC. -/
theorem ACPhysicalSession.coordinate_endpoint (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (i : ι) :
    m.ledger m.b i =
      coordinate (m.F i) (m.response i).impact (m.prices m.b i) -
      coordinate (m.F i) (m.response i).impact (m.prices m.a i) +
      ∫ t in m.a..m.b, m.recovery t i := by
  obtain ⟨C, hC⟩ := m.coordinate_lipschitz v hv i
  have hd := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hC m.time_order.le (by
    filter_upwards [m.coordinate_derivative] with t ht hmem
    exact ht ⟨hmem.1.le, hmem.2.le⟩ i)
  have hi : IntervalIntegrable (fun t => m.recovery t i) volume m.a m.b :=
    ((m.recovery_continuous i).mono (by rw [uIcc_of_le m.time_order.le])).intervalIntegrable
  change IntervalIntegrable (fun t => tradingInput (pairedMatrix edges) (m.rates t) i -
      m.recovery t i) volume m.a m.b ∧
    (∫ t in m.a..m.b, tradingInput (pairedMatrix edges) (m.rates t) i - m.recovery t i) = _ at hd
  rw [intervalIntegral.integral_sub (m.flow_integrable i) hi] at hd
  rw [m.ledger_endpoint i]
  linarith [hd.2]

def ACPhysicalSession.cutRequirement (m : ACPhysicalSession edges) (J : Finset ι) : ℝ :=
  ∑ i ∈ J, (coordinate (m.F i) (m.response i).impact (m.prices m.a i) -
    coordinate (m.F i) (m.response i).impact (m.prices m.b i))

theorem ACPhysicalSession.cutRequirement_positive (m : ACPhysicalSession edges)
    (J : Finset ι) (hne : J.Nonempty)
    (hdecline : ∀ i ∈ J, m.prices m.b i < m.prices m.a i) :
    0 < m.cutRequirement J := by
  apply Finset.sum_pos
  · intro i hi
    exact sub_pos.mpr ((coordinate_strictMonoOn _ _ (m.benchmark_positive i))
      (m.positive_prices m.b ⟨m.time_order.le, le_rfl⟩ i)
      (m.positive_prices m.a ⟨le_rfl, m.time_order.le⟩ i) (hdecline i hi))
  · exact hne

/-- Net RECEIVED dollars on the complement, with the physical recovery
sign retained. The conclusion does not require terminal closure. -/
theorem ACPhysicalSession.cut_funding (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι)
    (hbelow : ∀ t ∈ Icc m.a m.b, ∀ i ∈ J, m.prices t i ≤ m.F i) :
    m.cutRequirement J ≤ ∑ i ∈ univ \ J, m.ledger m.b i := by
  have hlocal (i : ι) (hi : i ∈ J) : m.ledger m.b i ≤
      coordinate (m.F i) (m.response i).impact (m.prices m.b i) -
      coordinate (m.F i) (m.response i).impact (m.prices m.a i) := by
    rw [m.coordinate_endpoint v hv i]
    have hn : (∫ t in m.a..m.b, m.recovery t i) ≤ 0 := by
      have hint : IntervalIntegrable (fun t => m.recovery t i) volume m.a m.b :=
        ((m.recovery_continuous i).mono (by rw [uIcc_of_le m.time_order.le])).intervalIntegrable
      have hn' := intervalIntegral.integral_mono_on m.time_order.le hint
        (intervalIntegrable_const (c := (0 : ℝ))) (fun t ht => show m.recovery t i ≤ 0 from
          mul_nonpos_of_nonneg_of_nonpos (m.resilience_nonnegative i)
            (div_nonpos_of_nonpos_of_nonneg
              (mul_nonpos_of_nonneg_of_nonpos (m.positive_prices t ht i).le
                (sub_nonpos.mpr (hbelow t ht i hi)))
              ((m.response i).positive _ (m.positive_prices t ht i)).le))
      simpa using hn'
    linarith
  have hs := Finset.sum_le_sum hlocal
  have hz : (∑ i, m.ledger m.b i) = 0 := paired_trading_sum_zero edges _
  have hsplit := Finset.sum_sdiff (f := fun i => m.ledger m.b i) (Finset.subset_univ J)
  have hneg : (∑ i ∈ J, (coordinate (m.F i) (m.response i).impact (m.prices m.b i) -
      coordinate (m.F i) (m.response i).impact (m.prices m.a i))) = -m.cutRequirement J := by
    simp only [ACPhysicalSession.cutRequirement, sum_sub_distrib]
    ring
  rw [hneg] at hs
  linarith

theorem paired_cut_coefficient_le_one (J : Finset ι) (e : κ) :
    (∑ i ∈ J, pairedMatrix edges i e) ≤ 1 := by
  classical
  simp only [pairedMatrix, sum_sub_distrib]
  by_cases hb : (edges e).buyer ∈ J <;>
    by_cases hs : (edges e).seller ∈ J <;> simp [hb, hs]

theorem ACPhysicalSession.cut_turnover_bound (m : ACPhysicalSession edges) (J : Finset ι) :
    (∑ i ∈ J, m.ledger m.b i) ≤ m.turnover := by
  have hc : IntervalIntegrable
      (fun t => ∑ i ∈ J, tradingInput (pairedMatrix edges) (m.rates t) i)
      volume m.a m.b := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum J
      (f := fun i t => tradingInput (pairedMatrix edges) (m.rates t) i)
      (fun i _ => m.flow_integrable i)
  have hr : IntervalIntegrable (fun t => ∑ e, m.rates t e) volume m.a m.b := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum Finset.univ
      (f := fun e t => m.rates t e) (fun e _ => m.rates_integrable e)
  have hm : (∫ t in m.a..m.b, ∑ i ∈ J, tradingInput (pairedMatrix edges) (m.rates t) i)
      ≤ m.turnover := by
    apply intervalIntegral.integral_mono_ae_restrict m.time_order.le hc hr
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [m.nonnegative_rates] with t ht hmem
    simp only [tradingInput]
    rw [sum_comm]
    apply sum_le_sum
    intro e _
    rw [← sum_mul]
    exact mul_le_of_le_one_left (ht hmem e) (paired_cut_coefficient_le_one J e)
  simpa only [intervalIntegral.integral_finset_sum (fun i _ => m.flow_integrable i),
    ← m.ledger_endpoint] using hm

/-- The receiving-side cap integrates to tau times upper price capacity. -/
theorem ACPhysicalSession.cut_capacity_bound (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι) (U : ι → ℝ)
    (hupper : ∀ t ∈ Icc m.a m.b, ∀ i ∈ J, m.prices t i ≤ U i) :
    (∑ i ∈ J, m.ledger m.b i) ≤ v * ((m.b - m.a) * ∑ i ∈ J, U i) := by
  have hc : IntervalIntegrable
      (fun t => ∑ i ∈ J, tradingInput (pairedMatrix edges) (m.rates t) i)
      volume m.a m.b := by
    simpa only [Finset.sum_fn] using IntervalIntegrable.sum J
      (f := fun i t => tradingInput (pairedMatrix edges) (m.rates t) i)
      (fun i _ => m.flow_integrable i)
  have hm : (∫ t in m.a..m.b, ∑ i ∈ J, tradingInput (pairedMatrix edges) (m.rates t) i)
      ≤ ∫ _t in m.a..m.b, v * ∑ i ∈ J, U i := by
    apply intervalIntegral.integral_mono_ae_restrict m.time_order.le hc intervalIntegrable_const
    apply (ae_restrict_iff' measurableSet_Icc).mpr
    filter_upwards [m.local_capacity, hv.2] with t ht hcap hmem
    calc
      (∑ i ∈ J, tradingInput (pairedMatrix edges) (m.rates t) i) ≤
          ∑ i ∈ J, |tradingInput (pairedMatrix edges) (m.rates t) i| :=
        sum_le_sum fun i _ => le_abs_self _
      _ ≤ ∑ i ∈ J, v * U i := by
        apply sum_le_sum
        intro i hi
        exact (ht hmem i).2.trans (by
          calc m.prices t i * m.gross t i ≤ m.prices t i * v :=
                 mul_le_mul_of_nonneg_left (hcap hmem i) (m.positive_prices t hmem i).le
               _ ≤ v * U i := by nlinarith [hupper t hmem i hi, hv.1])
      _ = v * ∑ i ∈ J, U i := (mul_sum _ _ _).symm
  rw [intervalIntegral.integral_finset_sum (fun i _ => m.flow_integrable i)] at hm
  simp only [← m.ledger_endpoint, intervalIntegral.integral_const, smul_eq_mul] at hm
  nlinarith [hm]

/-- Proposition 7.5, complete general market-cut conclusion (user-authorized
nonempty-J / nonzero-capacity boundary clarification, 2026-10-17).
It covers arbitrary asset-specific positive responses and benchmarks,
original physical AC primitives, actual ledgers, and turnover counted once.
The constant-impact rolling specialization is proved separately. -/
theorem proposition_7_5_market_cut (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι) (hne : J.Nonempty)
    (hbelow : ∀ t ∈ Icc m.a m.b, ∀ i ∈ J, m.prices t i ≤ m.F i)
    (hdecline : ∀ i ∈ J, m.prices m.b i < m.prices m.a i)
    (U : ι → ℝ)
    (hupper : ∀ t ∈ Icc m.a m.b, ∀ i ∈ Finset.univ \ J, m.prices t i ≤ U i) :
    0 < m.cutRequirement J ∧
    m.cutRequirement J ≤ (∑ i ∈ univ \ J, m.ledger m.b i) ∧
    m.cutRequirement J ≤ m.turnover ∧
    (Finset.univ \ J).Nonempty ∧
    0 < (m.b - m.a) * (∑ i ∈ univ \ J, U i) ∧
    m.cutRequirement J / ((m.b - m.a) * (∑ i ∈ univ \ J, U i)) ≤ v := by
  have hK := m.cutRequirement_positive J hne hdecline
  have hfund := m.cut_funding v hv J hbelow
  have hneC : (Finset.univ \ J).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he, sum_empty] at hfund
    linarith
  have hU : 0 < ∑ i ∈ univ \ J, U i := by
    apply Finset.sum_pos
    · intro i hi
      exact (m.positive_prices m.a ⟨le_rfl, m.time_order.le⟩ i).trans_le
        (hupper m.a ⟨le_rfl, m.time_order.le⟩ i hi)
    · exact hneC
  have hden := mul_pos (sub_pos.mpr m.time_order) hU
  refine ⟨hK, hfund, hfund.trans (m.cut_turnover_bound _), hneC, hden, ?_⟩
  apply (div_le_iff₀ hden).mpr
  exact hfund.trans (m.cut_capacity_bound v hv _ U hupper)

/-- Empty receiving side: impossible strict descent below benchmarks. -/
theorem proposition_7_5_empty_complement (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι) (hne : J.Nonempty)
    (hbelow : ∀ t ∈ Icc m.a m.b, ∀ i ∈ J, m.prices t i ≤ m.F i)
    (hdecline : ∀ i ∈ J, m.prices m.b i < m.prices m.a i)
    (hempty : Finset.univ \ J = ∅) : False := by
  have hK := m.cutRequirement_positive J hne hdecline
  have hfund := m.cut_funding v hv J hbelow
  simp only [hempty, sum_empty] at hfund
  linarith

/-- Instantaneous bound expressed in derivatives of genuine ledgers. -/
theorem proposition_7_5_ledger_derivative_bound (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b →
      |∑ i ∈ J, deriv (fun u => m.ledger u i) t| ≤
        v * min (∑ i ∈ J, m.prices t i)
          (∑ i ∈ Finset.univ \ J, m.prices t i) := by
  filter_upwards [m.ledger_derivative, m.cut_rate_ae v hv J] with t hd hc hmem
  simpa only [(hd hmem _).deriv] using hc hmem

/-- The k/m formula for a genuine physical session, with K and receiving
capacity derived by the preceding theorem and the rolling reference bands. -/
theorem proposition_7_5_rolling_constant_impact (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι) (hne : J.Nonempty)
    (F η β q : ℝ) (hF : 0 < F) (hη : 0 < η) (hβ : 0 ≤ β)
    (hq : 0 < q) (hq1 : q < 1) (d : ℕ) (hd : 2 ≤ d)
    (hFi : ∀ i ∈ J, m.F i = F)
    (hgi : ∀ i ∈ J, (m.response i).impact = fun _ => η)
    (hstart : ∀ i ∈ J, m.prices m.a i = F * q ^ (d - 1))
    (hend : ∀ i ∈ J, m.prices m.b i = F * q ^ d)
    (hbelow : ∀ t ∈ Icc m.a m.b, ∀ i ∈ J, m.prices t i ≤ m.F i)
    (reference : ι → ℕ → ℝ)
    (href0 : ∀ i ∈ Finset.univ \ J, reference i 0 ≤ F)
    (hrefstep : ∀ i ∈ Finset.univ \ J, ∀ n < d,
      reference i (n + 1) ≤ (1 + β) * reference i n)
    (hband : ∀ t ∈ Icc m.a m.b, ∀ i ∈ Finset.univ \ J,
      m.prices t i ≤ (1 + β) * reference i (d - 1)) :
    (J.card : ℝ) / (Finset.univ \ J).card * F *
      (q ^ (2 * (d - 1)) - q ^ (2 * d)) /
      (2 * η * (m.b - m.a) * (1 + β) ^ d) ≤ v := by
  have hds : d - 1 + 1 = d := by omega
  have hdecline : ∀ i ∈ J, m.prices m.b i < m.prices m.a i := by
    intro i hi
    have heq : q ^ d = q ^ (d - 1) * q := by
      calc q ^ d = q ^ (d - 1 + 1) := congrArg (fun n => q ^ n) hds.symm
           _ = _ := pow_succ _ _
    rw [hend i hi, hstart i hi, heq]
    have hpow := pow_pos hq (d - 1)
    exact mul_lt_mul_of_pos_left (by nlinarith) hF
  have hu : ∀ t ∈ Icc m.a m.b, ∀ i ∈ Finset.univ \ J,
      m.prices t i ≤ F * (1 + β) ^ d := by
    intro t ht i hi
    have hh := rolling_upper_reference_bound_finite F β hβ (reference i)
      (href0 i hi) (d - 1) (fun n hn => hrefstep i hi n (by omega))
    calc
      m.prices t i ≤ (1 + β) * reference i (d - 1) := hband t ht i hi
      _ ≤ (1 + β) * (F * (1 + β) ^ (d - 1)) :=
        mul_le_mul_of_nonneg_left hh (by linarith)
      _ = F * (1 + β) ^ (d - 1 + 1) := by rw [pow_succ]; ring
      _ = F * (1 + β) ^ d := by rw [hds]
  have hmain := proposition_7_5_market_cut m v hv J hne hbelow hdecline
    (fun _ => F * (1 + β) ^ d) hu
  have hK : m.cutRequirement J = J.card *
      (coordinate F (fun _ => η) (F * q ^ (d - 1)) -
        coordinate F (fun _ => η) (F * q ^ d)) := by
    unfold ACPhysicalSession.cutRequirement
    calc
      _ = ∑ _i ∈ J, (coordinate F (fun _ => η) (F * q ^ (d - 1)) -
          coordinate F (fun _ => η) (F * q ^ d)) := by
        apply sum_congr rfl
        intro i hi
        rw [hFi i hi, hgi i hi, hstart i hi, hend i hi]
      _ = _ := by simp; ring
  have hcap : (∑ _i ∈ Finset.univ \ J, F * (1 + β) ^ d) =
      (Finset.univ \ J).card * F * (1 + β) ^ d := by simp; ring
  have hr := hmain.2.2.2.2.2
  rw [hcap] at hr
  exact market_cut_constant_impact_specialization J.card (Finset.univ \ J).card
    F η (m.b - m.a) β q (m.cutRequirement J) v d
    (Finset.card_pos.mpr hmain.2.2.2.1) hF hη (sub_pos.mpr m.time_order)
    hβ hq hd hK hr

end MarketCrash
