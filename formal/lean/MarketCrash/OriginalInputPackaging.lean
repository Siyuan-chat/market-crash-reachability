import MarketCrash.OriginalPulse
import MarketCrash.OriginalPhysicalTrace
import MarketCrash.ACPhysicalSession
import Mathlib.Topology.Order.ProjIcc

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

/-- Constant extension of a finite-interval continuous monotone cumulative.
No global continuity or values outside the actual interval are required. -/
def finiteContinuousStieltjesExtension (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hm : MonotoneOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) : StieltjesFunction where
  toFun := fun t => f (projIcc a b hab t)
  mono' := fun s t hst => hm (projIcc _ _ _ s).property (projIcc _ _ _ t).property
    (monotone_projIcc hab hst)
  right_continuous' := fun _ => (hc.restrict.comp continuous_projIcc).continuousAt.continuousWithinAt

theorem finiteContinuousStieltjesExtension_eq (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hm : MonotoneOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) (t : ℝ) (ht : t ∈ Icc a b) :
    finiteContinuousStieltjesExtension a b hab f hm hc t = f t := by
  simp only [finiteContinuousStieltjesExtension, projIcc_of_mem hab ht]

theorem finiteContinuousStieltjesExtension_continuous (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hm : MonotoneOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    Continuous (finiteContinuousStieltjesExtension a b hab f hm hc) :=
  hc.restrict.comp continuous_projIcc

theorem finiteContinuousStieltjesExtension_tails (a b : ℝ) (hab : a ≤ b) (f : ℝ → ℝ)
    (hm : MonotoneOn f (Icc a b)) (hc : ContinuousOn f (Icc a b)) :
    (∀ t ≤ a, finiteContinuousStieltjesExtension a b hab f hm hc t = f a) ∧
    (∀ t, b ≤ t → finiteContinuousStieltjesExtension a b hab f hm hc t = f b) := by
  constructor
  · intro t ht
    simp only [finiteContinuousStieltjesExtension, projIcc_of_le_left hab ht]
  · intro t ht
    simp only [finiteContinuousStieltjesExtension, projIcc_of_right_le hab ht]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

def finiteContinuousPairedExecution (edges : κ → PairedEdge ι)
    (a b : ℝ) (hab : a ≤ b) (Z : κ → ℝ → ℝ)
    (hm : ∀ e, MonotoneOn (Z e) (Icc a b))
    (hc : ∀ e, ContinuousOn (Z e) (Icc a b)) : StieltjesPairedExecution edges where
  cumulative := fun e => finiteContinuousStieltjesExtension a b hab (Z e) (hm e) (hc e)

/-- Literal single-directed-edge dollar-parameter pulse from paper equation pulse-flow.
The parameter is a in [0,z], rather than a normalized or response coordinate. -/
structure OriginalDollarParameterPulse (edges : κ → PairedEdge ι) where
  physicalTime : ℝ
  edge : κ
  z : ℝ
  z_positive : 0 < z
  F : ι → ℝ
  response : ι → Response
  benchmark_positive : ∀ i, 0 < F i
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  continuous_prices : ∀ i, ContinuousOn (fun a => prices a i) (Icc 0 z)
  continuous_shares : ∀ i, ContinuousOn (fun a => shares a i) (Icc 0 z)
  continuous_ledgers : ∀ i, ContinuousOn (fun a => dollarLedger a i) (Icc 0 z)
  positive_prices : ∀ a ∈ Icc 0 z, ∀ i, 0 < prices a i
  no_short_sales : ∀ a ∈ Icc 0 z, ∀ i, 0 ≤ shares a i
  price_flow : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (fun u => prices u i)
    ((response i).impact (prices a i) / prices a i * pairedMatrix edges i edge) a
  share_flow : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (fun u => shares u i)
    (pairedMatrix edges i edge / prices a i) a
  ledger_flow : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (fun u => dollarLedger u i)
    (pairedMatrix edges i edge) a

theorem dollar_parameter_normalization_primitive
    (z : ℝ) (hz : 0 < z) (y w : ℝ → ℝ)
    (hy : ContinuousOn y (Icc 0 z)) (hw : ContinuousOn w (Icc 0 z))
    (hd : ∀ t ∈ Ioo 0 z, HasDerivAt y (w t) t)
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    y (z * a) - y 0 = ∫ u in (0 : ℝ)..a, z * w (z * u) := by
  have hmap : ∀ u ∈ Icc (0 : ℝ) 1, z * u ∈ Icc 0 z := by
    intro u hu
    exact ⟨mul_nonneg hz.le hu.1, by nlinarith [hu.2]⟩
  have hcont : ContinuousOn (fun u => y (z * u)) (Icc 0 a) :=
    hy.comp (continuous_const.mul continuous_id).continuousOn
      (fun u hu => hmap u ⟨hu.1, hu.2.trans ha.2⟩)
  have hwi : ContinuousOn (fun u => z * w (z * u)) (Icc 0 a) :=
    continuousOn_const.mul (hw.comp (continuous_const.mul continuous_id).continuousOn
      (fun u hu => hmap u ⟨hu.1, hu.2.trans ha.2⟩))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1 hcont
    (fun u hu => by
      have hzu : z * u ∈ Ioo 0 z := ⟨mul_pos hz hu.1, by nlinarith [hu.2.trans_le ha.2]⟩
      convert (hd _ hzu).comp u ((hasDerivAt_id u).const_mul z) using 1
      dsimp [Function.comp]
      ring)
    (ContinuousOn.intervalIntegrable_of_Icc ha.1 hwi)
  simpa only [mul_zero] using hftc.symm

def OriginalDollarParameterPulse.normalizedDollars (p : OriginalDollarParameterPulse edges) : κ → ℝ := by
  classical
  exact fun e => if e = p.edge then p.z else 0

omit [Fintype ι] in
theorem OriginalDollarParameterPulse.normalized_flow (p : OriginalDollarParameterPulse edges) (i : ι) :
    tradingInput (pairedMatrix edges) p.normalizedDollars i =
      p.z * pairedMatrix edges i p.edge := by
  classical
  simp [tradingInput, OriginalDollarParameterPulse.normalizedDollars, mul_comm]

def OriginalDollarParameterPulse.normalize (p : OriginalDollarParameterPulse edges) : OriginalFlowCompletedPulse edges where
  physicalTime := p.physicalTime
  F := p.F
  response := p.response
  benchmark_positive := p.benchmark_positive
  dollars := p.normalizedDollars
  nonnegative_dollars := by
    classical
    intro e
    dsimp [OriginalDollarParameterPulse.normalizedDollars]
    split
    · exact p.z_positive.le
    · exact le_rfl
  prices := fun a i => p.prices (p.z * a) i
  shares := fun a i => p.shares (p.z * a) i
  dollarLedger := fun a i => p.dollarLedger (p.z * a) i
  continuous_prices := fun i => (p.continuous_prices i).comp
    (continuous_const.mul continuous_id).continuousOn (fun a ha =>
      ⟨mul_nonneg p.z_positive.le ha.1, by nlinarith [ha.2, p.z_positive]⟩)
  positive_prices := fun a ha => p.positive_prices _
    ⟨mul_nonneg p.z_positive.le ha.1, by nlinarith [ha.2, p.z_positive]⟩
  no_short_sales := fun a ha => p.no_short_sales _
    ⟨mul_nonneg p.z_positive.le ha.1, by nlinarith [ha.2, p.z_positive]⟩
  physical_price_primitive := by
    intro i a ha
    have hw : ContinuousOn (fun t => (p.response i).impact (p.prices t i) / p.prices t i *
        pairedMatrix edges i p.edge) (Icc 0 p.z) := (((p.response i).continuousOn_positive.comp (p.continuous_prices i)
      (fun t ht => p.positive_prices t ht i)).div (p.continuous_prices i)
      (fun t ht => (p.positive_prices t ht i).ne')).mul continuousOn_const
    have hh := dollar_parameter_normalization_primitive p.z p.z_positive
      (fun t => p.prices t i)
      (fun t => (p.response i).impact (p.prices t i) / p.prices t i * pairedMatrix edges i p.edge)
      (p.continuous_prices i) hw (fun t ht => p.price_flow t ht i) a ha
    simp only [mul_zero]
    rw [hh]
    congr 1
    funext u
    rw [p.normalized_flow]
    ring
  physical_share_primitive := by
    intro i a ha
    have hw : ContinuousOn (fun t => pairedMatrix edges i p.edge / p.prices t i) (Icc 0 p.z) :=
      continuousOn_const.div (p.continuous_prices i) (fun t ht => (p.positive_prices t ht i).ne')
    have hh := dollar_parameter_normalization_primitive p.z p.z_positive
      (fun t => p.shares t i) (fun t => pairedMatrix edges i p.edge / p.prices t i)
      (p.continuous_shares i) hw (fun t ht => p.share_flow t ht i) a ha
    simp only [mul_zero]
    rw [hh]
    congr 1
    funext u
    rw [p.normalized_flow]
    ring
  marginal_dollar_primitive := by
    intro i a ha
    have hh := dollar_parameter_normalization_primitive p.z p.z_positive
      (fun t => p.dollarLedger t i) (fun _ => pairedMatrix edges i p.edge)
      (p.continuous_ledgers i) continuousOn_const (fun t ht => p.ledger_flow t ht i) a ha
    simp only [mul_zero]
    rw [hh, p.normalized_flow]

theorem OriginalDollarParameterPulse.normalize_endpoints (p : OriginalDollarParameterPulse edges) :
    p.normalize.prices 0 = p.prices 0 ∧ p.normalize.prices 1 = p.prices p.z ∧
      p.normalize.shares 0 = p.shares 0 ∧ p.normalize.shares 1 = p.shares p.z ∧
      p.normalize.dollarLedger 0 = p.dollarLedger 0 ∧ p.normalize.dollarLedger 1 = p.dollarLedger p.z := by
  simp [OriginalDollarParameterPulse.normalize]

theorem continuous_unit_primitive_boundedVariation (f w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc 0 1))
    (hp : ∀ a ∈ Icc (0 : ℝ) 1, f a - f 0 = ∫ u in (0 : ℝ)..a, w u) :
    BoundedVariationOn f (Icc (0 : ℝ) 1) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hw.norm
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hi (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      IntervalIntegrable w volume s t := by
    apply ContinuousOn.intervalIntegrable
    exact hw.mono (fun u hu => ⟨(le_min hs.1 ht.1).trans hu.1,
      hu.2.trans (max_le hs.2 ht.2)⟩)
  have hprim : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      f t - f s = ∫ u in s..t, w u := by
    intro s hs t ht
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (hi 0 ⟨le_rfl, by norm_num⟩ s hs) (hi s hs t ht)
    linarith [hp s hs, hp t ht]
  have hl := lipschitzOn_of_bounded_primitive f w 0 1 C hprim (by
    filter_upwards [] with u hu
    exact (hB (mem_image_of_mem _ hu)).trans (le_max_left _ _))
  have hv := hl.locallyBoundedVariationOn 0 1 ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩
  simpa only [inter_self] using hv

theorem OriginalDollarParameterPulse.normalized_shares_bv
    (p : OriginalDollarParameterPulse edges) (i : ι) :
    BoundedVariationOn (fun a => p.normalize.shares a i) (Icc (0 : ℝ) 1) := by
  apply continuous_unit_primitive_boundedVariation _
    (fun a => tradingInput (pairedMatrix edges) p.normalize.dollars i / p.normalize.prices a i)
    (continuousOn_const.div (p.normalize.continuous_prices i)
      (fun a ha => (p.normalize.positive_prices a ha i).ne'))
    (p.normalize.physical_share_primitive i)

/-- Direct entry into the finite chronological trace API, with all raw economic endpoints. -/
def OriginalDollarParameterPulse.toOriginalStep (p : OriginalDollarParameterPulse edges) (rho : ι → ℝ) :
    OriginalPhysicalStep p.F rho p.response edges
      ⟨p.physicalTime, p.prices 0, p.shares 0, p.dollarLedger 0⟩
      ⟨p.physicalTime, p.prices p.z, p.shares p.z, p.dollarLedger p.z⟩ := by
  simpa only [OriginalDollarParameterPulse.normalize, mul_zero, mul_one] using
    (OriginalPhysicalStep.pulse (rho := rho) p.normalize rfl rfl p.normalized_shares_bv)

end MarketCrash
