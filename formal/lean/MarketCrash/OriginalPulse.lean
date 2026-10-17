import MarketCrash.Coordinates
import MarketCrash.Conservation

/-! One original finite-dollar flow-completed pulse at fixed physical time.
Only the internal interpolation parameter ranges over [0,1]. No endpoint
two-sided derivatives or response-coordinate endpoint equation are assumed. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace MarketCrash

structure OriginalFlowCompletedPulse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) where
  physicalTime : ℝ
  F : ι → ℝ
  response : ι → Response
  benchmark_positive : ∀ i, 0 < F i
  dollars : κ → ℝ
  nonnegative_dollars : ∀ e, 0 ≤ dollars e
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  continuous_prices : ∀ i, ContinuousOn (fun a => prices a i) (Icc 0 1)
  positive_prices : ∀ a ∈ Icc (0 : ℝ) 1, ∀ i, 0 < prices a i
  no_short_sales : ∀ a ∈ Icc (0 : ℝ) 1, ∀ i, 0 ≤ shares a i
  physical_price_primitive : ∀ i, ∀ a ∈ Icc (0 : ℝ) 1,
    prices a i - prices 0 i = ∫ u in (0 : ℝ)..a,
      (response i).impact (prices u i) / prices u i * tradingInput (pairedMatrix edges) dollars i
  physical_share_primitive : ∀ i, ∀ a ∈ Icc (0 : ℝ) 1,
    shares a i - shares 0 i = ∫ u in (0 : ℝ)..a,
      tradingInput (pairedMatrix edges) dollars i / prices u i
  marginal_dollar_primitive : ∀ i, ∀ a ∈ Icc (0 : ℝ) 1,
    dollarLedger a i - dollarLedger 0 i =
      ∫ _u in (0 : ℝ)..a, tradingInput (pairedMatrix edges) dollars i

theorem unit_interval_primitive_hasDerivAt (f w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc 0 1))
    (hprim : ∀ a ∈ Icc (0 : ℝ) 1, f a - f 0 = ∫ u in (0 : ℝ)..a, w u)
    (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) : HasDerivAt f (w a) a := by
  have hi : IntervalIntegrable w volume 0 a :=
    ContinuousOn.intervalIntegrable_of_Icc ha.1.le
      (hw.mono (fun x hx => ⟨hx.1, hx.2.trans ha.2.le⟩))
  have hm : StronglyMeasurableAtFilter w (nhds a) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hw.mono Ioo_subset_Icc_self) a ha
  have hd := (intervalIntegral.integral_hasDerivAt_right hi hm
    (hw.continuousAt (Icc_mem_nhds ha.1 ha.2))).const_add (f 0)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ha.1 ha.2] with x hx
  have hh := hprim x ⟨hx.1.le, hx.2.le⟩
  linarith

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

theorem OriginalFlowCompletedPulse.price_flow_interior
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (i : ι) :
    HasDerivAt (fun u => p.prices u i)
      ((p.response i).impact (p.prices a i) / p.prices a i *
        tradingInput (pairedMatrix edges) p.dollars i) a := by
  apply unit_interval_primitive_hasDerivAt _ _ _ (p.physical_price_primitive i) a ha
  exact (((p.response i).continuousOn_positive.comp (p.continuous_prices i)
    (fun u hu => p.positive_prices u hu i)).div (p.continuous_prices i)
    (fun u hu => (p.positive_prices u hu i).ne')).mul continuousOn_const

theorem OriginalFlowCompletedPulse.coordinate_flow_interior
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (i : ι) :
    HasDerivAt (fun u => coordinate (p.F i) (p.response i).impact (p.prices u i))
      (tradingInput (pairedMatrix edges) p.dollars i) a := by
  have hp := p.positive_prices a ⟨ha.1.le, ha.2.le⟩ i
  have hg := (p.response i).positive _ hp
  have hd := (coordinate_hasDerivAt (p.F i) (p.response i) (p.benchmark_positive i) hp).comp a
    (p.price_flow_interior a ha i)
  convert hd using 1 <;> dsimp [Function.comp] <;> field_simp [hp.ne', hg.ne'] <;> ring

theorem OriginalFlowCompletedPulse.coordinate_endpoint
    (p : OriginalFlowCompletedPulse edges) (i : ι) :
    coordinate (p.F i) (p.response i).impact (p.prices 1 i) =
      coordinate (p.F i) (p.response i).impact (p.prices 0 i) +
        tradingInput (pairedMatrix edges) p.dollars i := by
  have hc : ContinuousOn (coordinate (p.F i) (p.response i).impact) positivePrices := by
    intro s hs
    exact (coordinate_hasDerivAt (p.F i) (p.response i) (p.benchmark_positive i) hs).continuousAt.continuousWithinAt
  have hcp := hc.comp (p.continuous_prices i) (fun a ha => p.positive_prices a ha i)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (a := (0 : ℝ)) (b := 1) (by norm_num) hcp
    (fun a ha => p.coordinate_flow_interior a ha i) intervalIntegrable_const
  simp only [intervalIntegral.integral_const, sub_zero, one_smul, Function.comp_apply] at hftc
  linarith

theorem OriginalFlowCompletedPulse.ledger_endpoint
    (p : OriginalFlowCompletedPulse edges) (i : ι) :
    p.dollarLedger 1 i = p.dollarLedger 0 i + tradingInput (pairedMatrix edges) p.dollars i := by
  have hh := p.marginal_dollar_primitive i 1 ⟨by norm_num, le_rfl⟩
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at hh
  linarith

theorem OriginalFlowCompletedPulse.potential_preserved
    (p : OriginalFlowCompletedPulse edges) :
    potential (fun i => coordinate (p.F i) (p.response i).impact (p.prices 1 i)) =
      potential (fun i => coordinate (p.F i) (p.response i).impact (p.prices 0 i)) := by
  unfold potential
  simp_rw [p.coordinate_endpoint]
  rw [Finset.sum_add_distrib, paired_trading_sum_zero, add_zero]

theorem OriginalFlowCompletedPulse.coordinate_at_parameter
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (i : ι) :
    coordinate (p.F i) (p.response i).impact (p.prices a i) =
      coordinate (p.F i) (p.response i).impact (p.prices 0 i) +
        a * tradingInput (pairedMatrix edges) p.dollars i := by
  have hc : ContinuousOn (coordinate (p.F i) (p.response i).impact) positivePrices := by
    intro s hs
    exact (coordinate_hasDerivAt (p.F i) (p.response i) (p.benchmark_positive i) hs).continuousAt.continuousWithinAt
  have hcp := hc.comp (p.continuous_prices i) (fun u hu => p.positive_prices u hu i)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1
    (hcont := hcp.mono (fun u hu => ⟨hu.1, hu.2.trans ha.2⟩))
    (hderiv := fun u hu => p.coordinate_flow_interior u ⟨hu.1, hu.2.trans_le ha.2⟩ i)
    (hint := intervalIntegrable_const)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, Function.comp_apply] at hftc
  linarith

theorem OriginalFlowCompletedPulse.potential_at_parameter
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    potential (fun i => coordinate (p.F i) (p.response i).impact (p.prices a i)) =
      potential (fun i => coordinate (p.F i) (p.response i).impact (p.prices 0 i)) := by
  unfold potential
  simp_rw [p.coordinate_at_parameter a ha]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, paired_trading_sum_zero, mul_zero, add_zero]

end MarketCrash
