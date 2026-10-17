import MarketCrash.StieltjesExecution
import MarketCrash.Coordinates
import Mathlib.Topology.Order.ProjIcc

/-!
Primitive M2 on a continuous physical-time BV piece. The Stieltjes
integrals below encode marginal share and dollar execution before any
response-coordinate chain rule. Singular-continuous controls are allowed.
Only finitely many physical pulses may be concatenated outside this type.
This file does not assume a weak-normal-form identity or operational ODE.
-/
noncomputable section
namespace MarketCrash
open MeasureTheory Set

structure PhysicalContinuousBVPiece {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (edges : κ → PairedEdge ι) where
  a : ℝ
  b : ℝ
  time_order : a ≤ b
  F : ι → ℝ
  rho : ι → ℝ
  response : ι → Response
  benchmark_positive : ∀ i, 0 < F i
  resilience_nonnegative : ∀ i, 0 ≤ rho i
  execution : StieltjesPairedExecution edges
  continuous_execution : ∀ e, ContinuousOn (execution.cumulative e) (Icc a b)
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  continuous_prices : ∀ i, ContinuousOn (fun t => prices t i) (Icc a b)
  positive_prices : ∀ t ∈ Icc a b, ∀ i, 0 < prices t i
  no_short_sales : ∀ t ∈ Icc a b, ∀ i, 0 ≤ shares t i
  physical_price_primitive : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    prices t i - prices s i =
      (∫ u in s..t, -rho i * (prices u i - F i)) +
      ∑ e, pairedMatrix edges i e *
        ∫ u in s..t, (response i).impact (prices u i) / prices u i
          ∂(execution.cumulative e).measure
  physical_share_primitive : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    shares t i - shares s i =
      ∑ e, pairedMatrix edges i e *
        ∫ u in s..t, 1 / prices u i ∂(execution.cumulative e).measure
  marginal_dollar_primitive : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    dollarLedger t i - dollarLedger s i =
      tradingInput (pairedMatrix edges)
        (fun e => (execution.cumulative e) t - (execution.cumulative e) s) i

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

theorem PhysicalContinuousBVPiece.price_trade_integrand_continuous
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    ContinuousOn (fun t => (m.response i).impact (m.prices t i) / m.prices t i)
      (Icc m.a m.b) := by
  exact ((m.response i).continuousOn_positive.comp (m.continuous_prices i)
    (fun t ht => m.positive_prices t ht i)).div (m.continuous_prices i)
    (fun t ht => (m.positive_prices t ht i).ne')

theorem PhysicalContinuousBVPiece.share_trade_integrand_continuous
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    ContinuousOn (fun t => 1 / m.prices t i) (Icc m.a m.b) := by
  exact continuousOn_const.div (m.continuous_prices i)
    (fun t ht => (m.positive_prices t ht i).ne')

/-- Continuity of the genuine physical-time recovery integrand needs
no global recoveryForce extension premise. -/
theorem PhysicalContinuousBVPiece.recovery_integrand_continuous
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    ContinuousOn (fun t => m.prices t i * (m.prices t i - m.F i) /
      (m.response i).impact (m.prices t i)) (Icc m.a m.b) := by
  exact ((m.continuous_prices i).mul ((m.continuous_prices i).sub continuousOn_const)).div
    ((m.response i).continuousOn_positive.comp (m.continuous_prices i)
      (fun t ht => m.positive_prices t ht i))
    (fun t ht => ((m.response i).positive _ (m.positive_prices t ht i)).ne')

/-- A derived global extension of recovery on the physical interval.
It agrees at both endpoints, including a degenerate piece. -/
def PhysicalContinuousBVPiece.recoveryExtension
    (m : PhysicalContinuousBVPiece edges) (t : ℝ) (i : ι) : ℝ :=
  let s : ℝ := Set.projIcc m.a m.b m.time_order t
  m.prices s i * (m.prices s i - m.F i) / (m.response i).impact (m.prices s i)

theorem PhysicalContinuousBVPiece.recoveryExtension_continuous
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    Continuous (fun t => m.recoveryExtension t i) := by
  exact (m.recovery_integrand_continuous i).restrict.comp continuous_projIcc

theorem PhysicalContinuousBVPiece.recoveryExtension_eq
    (m : PhysicalContinuousBVPiece edges) (t : ℝ) (ht : t ∈ Icc m.a m.b) (i : ι) :
    m.recoveryExtension t i = m.prices t i * (m.prices t i - m.F i) /
      (m.response i).impact (m.prices t i) := by
  simp only [PhysicalContinuousBVPiece.recoveryExtension,
    Set.projIcc_of_mem m.time_order ht]

end MarketCrash
