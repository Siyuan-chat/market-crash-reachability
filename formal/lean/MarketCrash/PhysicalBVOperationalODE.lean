import MarketCrash.PhysicalContinuousBV
import MarketCrash.ContinuousClockChangeOfVariables
import MarketCrash.StieltjesPrimitiveDerivative
import Mathlib.Analysis.Calculus.Monotone

noncomputable section
namespace MarketCrash
open Set MeasureTheory Filter
open scoped Topology
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

/-- Only inverse-clock data; all these fields have a constructive existence theorem.
No price derivative, transformed primitive, or ODE is a field. -/
structure PhysicalBVClock (m : PhysicalContinuousBVPiece edges) (scale : ℝ) where
  time : ℝ → ℝ
  continuous_time : Continuous time
  monotone_time : Monotone time
  time_range : ∀ u, time u ∈ Icc m.a m.b
  clock_time : ∀ u, m.execution.variationClock scale (time u) =
    max (m.execution.variationClock scale m.a) (min (m.execution.variationClock scale m.b) u)
  time_clock : ∀ t ∈ Icc m.a m.b, time (m.execution.variationClock scale t) = t

theorem PhysicalContinuousBVPiece.exists_physicalBVClock
    (m : PhysicalContinuousBVPiece edges) (scale : ℝ) (hs : 0 < scale) :
    Nonempty (PhysicalBVClock m scale) := by
  obtain ⟨T, hc, hm, hr, hct, htc⟩ := continuous_piece_clamped_inverse
    m.execution scale m.a m.b hs m.time_order m.continuous_execution
  exact ⟨⟨T, hc, hm, hr, hct, htc⟩⟩

variable {m : PhysicalContinuousBVPiece edges} {scale : ℝ}

def PhysicalBVClock.edge (c : PhysicalBVClock m scale) (e : κ) : StieltjesFunction :=
  clockTransformedCumulative (m.execution.cumulative e) c.time m.a m.b
    c.continuous_time c.monotone_time c.time_range (m.continuous_execution e)

def PhysicalBVClock.timeIntegrator (c : PhysicalBVClock m scale) : StieltjesFunction :=
  clockTransformedCumulative StieltjesFunction.id c.time m.a m.b
    c.continuous_time c.monotone_time c.time_range continuousOn_id

def PhysicalBVClock.A (_c : PhysicalBVClock m scale) : ℝ := m.execution.variationClock scale m.a
def PhysicalBVClock.B (_c : PhysicalBVClock m scale) : ℝ := m.execution.variationClock scale m.b

theorem PhysicalBVClock.clock_time_on (c : PhysicalBVClock m scale)
    (u : ℝ) (hu : u ∈ Icc c.A c.B) : m.execution.variationClock scale (c.time u) = u := by
  have hu' : m.execution.variationClock scale m.a ≤ u ∧ u ≤ m.execution.variationClock scale m.b := hu
  rw [c.clock_time, min_eq_right hu'.2, max_eq_right hu'.1]

theorem PhysicalBVClock.integral_prefix (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (G : StieltjesFunction) (hG : ContinuousOn G (Icc m.a m.b))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc m.a m.b))
    (u : ℝ) (hu : u ∈ Icc c.A c.B) :
    (∫ t in m.a..c.time u, w t ∂G.measure) =
      ∫ v in c.A..u, w (c.time v) ∂(clockTransformedCumulative G c.time m.a m.b
        c.continuous_time c.monotone_time c.time_range hG).measure := by
  have hh := clamped_clock_integral_subinterval G (m.execution.variationClock scale) c.time
    m.a m.b m.time_order (m.execution.variationClock_strictMono scale hs.le)
    c.continuous_time c.monotone_time c.time_range hG c.clock_time c.time_clock
    m.a (c.time u) ⟨le_rfl, m.time_order⟩ (c.time_range u) (c.time_range u).1 w hw
  simpa only [c.clock_time_on u hu] using hh

theorem PhysicalBVClock.price_primitive (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (i : ι) (u : ℝ) (hu : u ∈ Icc c.A c.B) :
    m.prices (c.time u) i - m.prices m.a i =
      (∫ v in c.A..u, -m.rho i * (m.prices (c.time v) i - m.F i) ∂c.timeIntegrator.measure) +
      ∑ e, pairedMatrix edges i e *
        ∫ v in c.A..u, (m.response i).impact (m.prices (c.time v) i) / m.prices (c.time v) i
          ∂(c.edge e).measure := by
  rw [m.physical_price_primitive i m.a ⟨le_rfl, m.time_order⟩ (c.time u) (c.time_range u)]
  have hrec : ContinuousOn (fun t => -m.rho i * (m.prices t i - m.F i)) (Icc m.a m.b) :=
    continuousOn_const.mul ((m.continuous_prices i).sub continuousOn_const)
  have htime := c.integral_prefix hs StieltjesFunction.id continuousOn_id _ hrec u hu
  rw [identity_stieltjes_measure_eq_volume] at htime
  rw [htime]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [c.integral_prefix hs (m.execution.cumulative e) (m.continuous_execution e) _
    (m.price_trade_integrand_continuous i) u hu]
  rfl

theorem PhysicalBVClock.share_primitive (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (i : ι) (u : ℝ) (hu : u ∈ Icc c.A c.B) :
    m.shares (c.time u) i - m.shares m.a i =
      ∑ e, pairedMatrix edges i e *
        ∫ v in c.A..u, 1 / m.prices (c.time v) i ∂(c.edge e).measure := by
  rw [m.physical_share_primitive i m.a ⟨le_rfl, m.time_order⟩ (c.time u) (c.time_range u)]
  apply Finset.sum_congr rfl
  intro e _
  rw [c.integral_prefix hs (m.execution.cumulative e) (m.continuous_execution e) _
    (m.share_trade_integrand_continuous i) u hu]
  rfl

theorem PhysicalBVClock.price_hasDerivAt (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (i : ι) (u : ℝ) (hu : u ∈ Ioo c.A c.B)
    (hT : HasDerivAt c.timeIntegrator (deriv c.timeIntegrator u) u)
    (hE : ∀ e, HasDerivAt (c.edge e) (deriv (c.edge e) u) u) :
    HasDerivAt (fun v => m.prices (c.time v) i)
      (-m.rho i * (m.prices (c.time u) i - m.F i) * deriv c.timeIntegrator u +
        (m.response i).impact (m.prices (c.time u) i) *
          (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i)) u := by
  let R := fun v => -m.rho i * (m.prices (c.time v) i - m.F i)
  let W := fun v => (m.response i).impact (m.prices (c.time v) i) / m.prices (c.time v) i
  have hRc : Continuous R := (continuousOn_const.mul
    ((m.continuous_prices i).sub continuousOn_const)).comp_continuous c.continuous_time c.time_range
  have hWc : Continuous W := (m.price_trade_integrand_continuous i).comp_continuous c.continuous_time c.time_range
  have hR := stieltjes_primitive_hasDerivAt c.timeIntegrator R hRc c.A u _ hT
  have hW (e : κ) := stieltjes_primitive_hasDerivAt (c.edge e) W hWc c.A u _ (hE e)
  have hD := (hR.add (HasDerivAt.sum (u := Finset.univ)
    (fun e _ => (hW e).const_mul (pairedMatrix edges i e)))).add_const (m.prices m.a i)
  have heq : (fun v => m.prices (c.time v) i) =ᶠ[nhds u]
      (fun v => ((∫ x in c.A..v, R x ∂c.timeIntegrator.measure) +
        ∑ e, pairedMatrix edges i e * ∫ x in c.A..v, W x ∂(c.edge e).measure) + m.prices m.a i) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    have hh := c.price_primitive hs i v ⟨hv.1.le, hv.2.le⟩
    dsimp [R, W]
    linarith
  have hfinal := hD.congr_of_eventuallyEq heq
  convert hfinal using 1
  dsimp [R, W, tradingInput]
  rw [Finset.sum_div, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem PhysicalBVClock.share_hasDerivAt (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (i : ι) (u : ℝ) (hu : u ∈ Ioo c.A c.B)
    (hE : ∀ e, HasDerivAt (c.edge e) (deriv (c.edge e) u) u) :
    HasDerivAt (fun v => m.shares (c.time v) i)
      (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i) u := by
  let W := fun v => 1 / m.prices (c.time v) i
  have hWc : Continuous W := (m.share_trade_integrand_continuous i).comp_continuous c.continuous_time c.time_range
  have hW (e : κ) := stieltjes_primitive_hasDerivAt (c.edge e) W hWc c.A u _ (hE e)
  have hD := (HasDerivAt.sum (u := Finset.univ)
    (fun e _ => (hW e).const_mul (pairedMatrix edges i e))).add_const (m.shares m.a i)
  have heq : (fun v => m.shares (c.time v) i) =ᶠ[nhds u]
      (fun v => (∑ e, pairedMatrix edges i e * ∫ x in c.A..v, W x ∂(c.edge e).measure) + m.shares m.a i) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v hv
    have hh := c.share_primitive hs i v ⟨hv.1.le, hv.2.le⟩
    dsimp [W]
    linarith
  have hfinal := hD.congr_of_eventuallyEq heq
  convert hfinal using 1
  dsimp [W, tradingInput]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem PhysicalBVClock.ledger_hasDerivAt (c : PhysicalBVClock m scale)
    (i : ι) (u : ℝ) (hu : u ∈ Ioo c.A c.B)
    (hE : ∀ e, HasDerivAt (c.edge e) (deriv (c.edge e) u) u) :
    HasDerivAt (fun v => m.dollarLedger (c.time v) i)
      (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i) u := by
  have hD := (HasDerivAt.sum (u := Finset.univ) (fun e _ =>
    ((hE e).sub_const ((m.execution.cumulative e) m.a)).const_mul (pairedMatrix edges i e))).add_const
      (m.dollarLedger m.a i)
  have heq : (fun v => m.dollarLedger (c.time v) i) =ᶠ[nhds u]
      (fun v => (∑ e, pairedMatrix edges i e *
        ((c.edge e) v - (m.execution.cumulative e) m.a)) + m.dollarLedger m.a i) := by
    filter_upwards [Ioo_mem_nhds hu.1 hu.2] with v _
    have hh := m.marginal_dollar_primitive i m.a ⟨le_rfl, m.time_order⟩ (c.time v) (c.time_range v)
    change m.dollarLedger (c.time v) i - m.dollarLedger m.a i =
      ∑ e, pairedMatrix edges i e * ((c.edge e) v - (m.execution.cumulative e) m.a) at hh
    linarith
  exact hD.congr_of_eventuallyEq heq

theorem stieltjes_true_derivative_ae (G : StieltjesFunction) :
    ∀ᵐ u ∂volume, HasDerivAt G (deriv G u) u ∧ 0 ≤ deriv G u := by
  filter_upwards [G.ae_hasDerivAt] with u hu
  exact ⟨hu.differentiableAt.hasDerivAt, hu.deriv.symm ▸ ENNReal.toReal_nonneg⟩

theorem monotone_true_deriv_nonnegative {f : ℝ → ℝ} (hf : Monotone f) (u : ℝ) :
    0 ≤ deriv f u := by
  by_cases hd : DifferentiableAt ℝ f u
  · apply ge_of_tendsto hd.hasDerivAt.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 ≤ t⁻¹ * (f (u + t) - f u)
    exact mul_nonneg (inv_nonneg.mpr ht.le)
      (sub_nonneg.mpr (hf (le_add_of_nonneg_right ht.le)))
  · rw [deriv_zero_of_not_differentiableAt hd]

theorem PhysicalBVClock.actual_speeds_nonnegative (c : PhysicalBVClock m scale) (u : ℝ) :
    0 ≤ deriv c.timeIntegrator u ∧ ∀ e, 0 ≤ deriv (c.edge e) u := by
  exact ⟨monotone_true_deriv_nonnegative c.timeIntegrator.mono u,
    fun e => monotone_true_deriv_nonnegative (c.edge e).mono u⟩

/-- Actual derivative speeds and all three operational physical ODEs,
deduced from raw physical primitives by prefix change of variables. -/
theorem PhysicalBVClock.physical_ode_ae (c : PhysicalBVClock m scale) (hs : 0 < scale) :
    ∀ᵐ u ∂volume, u ∈ Icc c.A c.B →
      (HasDerivAt c.time (deriv c.timeIntegrator u) u ∧ 0 ≤ deriv c.timeIntegrator u) ∧
      (∀ e, HasDerivAt (c.edge e) (deriv (c.edge e) u) u ∧ 0 ≤ deriv (c.edge e) u) ∧
      (∀ i, HasDerivAt (fun v => m.prices (c.time v) i)
        (-m.rho i * (m.prices (c.time u) i - m.F i) * deriv c.timeIntegrator u +
          (m.response i).impact (m.prices (c.time u) i) *
            (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i)) u) ∧
      (∀ i, HasDerivAt (fun v => m.shares (c.time v) i)
        (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i) u) ∧
      (∀ i, HasDerivAt (fun v => m.dollarLedger (c.time v) i)
        (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i) u) := by
  have hE : ∀ᵐ u ∂volume, ∀ e, HasDerivAt (c.edge e) (deriv (c.edge e) u) u ∧
      0 ≤ deriv (c.edge e) u := ae_all_iff.mpr (fun e => stieltjes_true_derivative_ae (c.edge e))
  filter_upwards [stieltjes_true_derivative_ae c.timeIntegrator, hE,
    show ∀ᵐ u : ℝ ∂volume, u ≠ c.A by simp [ae_iff],
    show ∀ᵐ u : ℝ ∂volume, u ≠ c.B by simp [ae_iff]] with u hT hE hA hB hu
  have hui : u ∈ Ioo c.A c.B := ⟨lt_of_le_of_ne hu.1 hA.symm, lt_of_le_of_ne hu.2 hB⟩
  refine ⟨⟨hT.1, hT.2⟩, hE, ?_, ?_, ?_⟩
  · exact fun i => c.price_hasDerivAt hs i u hui hT.1 (fun e => (hE e).1)
  · exact fun i => c.share_hasDerivAt hs i u hui (fun e => (hE e).1)
  · exact fun i => c.ledger_hasDerivAt i u hui (fun e => (hE e).1)

end MarketCrash
