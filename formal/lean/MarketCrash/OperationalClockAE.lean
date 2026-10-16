import MarketCrash.OperationalClockLedger
import Mathlib.Analysis.Calculus.Rademacher

/-!
# A.e. physical response on a common Lipschitz operational clock

The complete graph of a BV transaction control is expected to have a
Lipschitz operational parametrization, even when trading is singular
continuous in physical time or incorporates ordered jump arcs. For that
prospective representation, this file DEFINES a physical market solution
with Lipschitz time, cumulative edge dollars, prices, holdings and ledgers,
and imposes physical marginal-settlement differential equations ONLY
almost everywhere in the operational parameter.

Crucially the response-adapted coordinate equation, aggregate cancellation
and the integrating-factor derivative inequality are DERIVED here from the
physical price ODE; they are not additional fields of the solution.

This module alone does not construct completed graphs from all original
M1--M5 controls, nor does an a.e. derivative inequality by itself imply an
endpoint comparison without absolute continuity / the corresponding FTC.
-/

noncomputable section
namespace MarketCrash
open MeasureTheory

/-- An a.e. physical model in a common operational parameter.
All Lipschitz functions are given on the whole real line; restricting
or extending any completed graph to this global form remains a model
inclusion obligation, separate from the algebraic a.e. calculus below. -/
structure AEOperationalClockSegment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  a : ℝ
  b : ℝ
  time_order : a ≤ b
  physicalTime : ℝ → ℝ
  timeSpeed : ℝ → ℝ
  edgeDollars : ℝ → κ → ℝ
  edgeRates : ℝ → κ → ℝ
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  physical_time_lipschitz : ∃ C : ℝ≥0, LipschitzWith C physicalTime
  edge_dollars_lipschitz : ∀ e, ∃ C : ℝ≥0,
    LipschitzWith C (fun u => edgeDollars u e)
  prices_lipschitz : ∀ i, ∃ C : ℝ≥0,
    LipschitzWith C (fun u => prices u i)
  shares_lipschitz : ∀ i, ∃ C : ℝ≥0,
    LipschitzWith C (fun u => shares u i)
  ledgers_lipschitz : ∀ i, ∃ C : ℝ≥0,
    LipschitzWith C (fun u => dollarLedger u i)
  positive_prices : ∀ u ∈ Set.Icc a b, ∀ i, 0 < prices u i
  no_short_sales : ∀ u ∈ Set.Icc a b, ∀ i, 0 ≤ shares u i
  nonnegative_time_speed : ∀ u ∈ Set.Icc a b, 0 ≤ timeSpeed u
  nonnegative_edge_rates : ∀ u ∈ Set.Icc a b, ∀ e, 0 ≤ edgeRates u e
  physical_time_flow_ae :
    ∀ᵐ u ∂volume, u ∈ Set.Icc a b →
      HasDerivAt physicalTime (timeSpeed u) u
  cumulative_edge_flow_ae :
    ∀ᵐ u ∂volume, u ∈ Set.Icc a b → ∀ e,
      HasDerivAt (fun v => edgeDollars v e) (edgeRates u e) u
  physical_price_flow_ae :
    ∀ᵐ u ∂volume, u ∈ Set.Icc a b → ∀ i,
      HasDerivAt (fun v => prices v i)
        (-rho * (prices u i - F) * timeSpeed u +
          g.impact (prices u i) *
            (tradingInput (pairedMatrix edges) (edgeRates u) i / prices u i)) u
  physical_share_flow_ae :
    ∀ᵐ u ∂volume, u ∈ Set.Icc a b → ∀ i,
      HasDerivAt (fun v => shares v i)
        (tradingInput (pairedMatrix edges) (edgeRates u) i / prices u i) u
  physical_ledger_flow_ae :
    ∀ᵐ u ∂volume, u ∈ Set.Icc a b → ∀ i,
      HasDerivAt (fun v => dollarLedger v i)
        (tradingInput (pairedMatrix edges) (edgeRates u) i) u

/-- Rademacher differentiability of each physical price follows from
its Lipschitz regularity independently of the ODE validity assumption. -/
theorem AEOperationalClockSegment.price_differentiable_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : AEOperationalClockSegment F rho g edges)
    (i : ι) :
    ∀ᵐ u ∂volume, DifferentiableAt ℝ (fun v => m.prices v i) u := by
  obtain ⟨C, hC⟩ := m.prices_lipschitz i
  exact hC.ae_differentiableAt_real

/-- The a.e. speed in the physical model equals the genuine a.e.
derivative of its Lipschitz physical-time clock. -/
theorem AEOperationalClockSegment.time_deriv_eq_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : AEOperationalClockSegment F rho g edges) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b →
      deriv m.physicalTime u = m.timeSpeed u := by
  filter_upwards [m.physical_time_flow_ae] with u hu hmem
  exact (hu hmem).deriv

/-- The same matching property holds for every actual cumulative
directed-edge executed-dollar clock. -/
theorem AEOperationalClockSegment.edge_deriv_eq_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : AEOperationalClockSegment F rho g edges) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b → ∀ e,
      deriv (fun v => m.edgeDollars v e) u = m.edgeRates u e := by
  filter_upwards [m.cumulative_edge_flow_ae] with u hu hmem e
  exact (hu hmem e).deriv

/-- A genuine a.e. nonlinear coordinate chain rule obtained only from
the PHYSICAL marginal-price settlement law and the local derivative
of Phi(S) = integral_F^S x/g(x) dx. -/
theorem AEOperationalClockSegment.coordinate_ode_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b → ∀ i,
      HasDerivAt (fun v => coordinate F g.impact (m.prices v i))
        (tradingInput (pairedMatrix edges) (m.edgeRates u) i -
          rho * m.timeSpeed u *
            (m.prices u i * (m.prices u i - F) / g.impact (m.prices u i))) u := by
  filter_upwards [m.physical_price_flow_ae] with u hu hmem i
  have hs : 0 < m.prices u i := m.positive_prices u hmem i
  have hp : m.prices u i ≠ 0 := hs.ne'
  have hg : g.impact (m.prices u i) ≠ 0 :=
    (g.positive (m.prices u i) hs).ne'
  have h := (coordinate_hasDerivAt F g hF hs).comp u (hu hmem i)
  convert h using 1 <;> dsimp [Function.comp] <;> field_simp [hp, hg] <;> ring

/-- Concurrent directed trades cancel in the a.e. aggregate price
potential equation. This is NOT postulated as a conservation law. -/
theorem AEOperationalClockSegment.potential_ode_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b →
      HasDerivAt
        (fun v => potential (fun i => coordinate F g.impact (m.prices v i)))
        (-rho * m.timeSpeed u *
          ∑ i, m.prices u i * (m.prices u i - F) /
            g.impact (m.prices u i)) u := by
  filter_upwards [m.coordinate_ode_ae F rho g edges hF] with u hu hmem
  have hd := HasDerivAt.sum (u := Finset.univ) (fun i _ => hu hmem i)
  have heq :
      (∑ i, (tradingInput (pairedMatrix edges) (m.edgeRates u) i -
        rho * m.timeSpeed u *
          (m.prices u i * (m.prices u i - F) / g.impact (m.prices u i)))) =
      -rho * m.timeSpeed u *
        ∑ i, m.prices u i * (m.prices u i - F) /
          g.impact (m.prices u i) := by
    rw [Finset.sum_sub_distrib, paired_trading_sum_zero]
    simp [Finset.mul_sum, mul_assoc]
  simpa [potential, heq] using hd

/-- The integrating factor has the physically derived a.e. derivative.
It includes trading during physical-time pauses and concurrent recovery. -/
theorem AEOperationalClockSegment.integrating_factor_ode_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges) (hF : 0 < F) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b →
      HasDerivAt
        (fun v => Real.exp (rho * m.physicalTime v) *
          potential (fun i => coordinate F g.impact (m.prices v i)))
        (Real.exp (rho * m.physicalTime u) * (rho * m.timeSpeed u) *
          (potential (fun i => coordinate F g.impact (m.prices u i)) -
            ∑ i, m.prices u i * (m.prices u i - F) /
              g.impact (m.prices u i))) u := by
  filter_upwards [m.potential_ode_ae F rho g edges hF,
    m.physical_time_flow_ae] with u hpot htime hmem
  have hinner : HasDerivAt (fun v : ℝ => rho * m.physicalTime v)
      (rho * m.timeSpeed u) u :=
    (htime hmem).const_mul rho
  have hexp : HasDerivAt (fun v : ℝ => Real.exp (rho * m.physicalTime v))
      (Real.exp (rho * m.physicalTime u) * (rho * m.timeSpeed u)) u := by
    convert (Real.hasDerivAt_exp (rho * m.physicalTime u)).comp u hinner using 1 <;> ring
  convert (hexp.mul (hpot hmem)) using 1 <;> dsimp [Function.comp] <;> ring

/-- Under e>=1 the exponential weighted market potential has
nonnegative derivative ALMOST EVERYWHERE. The remaining endpoint
comparison requires an absolutely continuous FTC theorem, not a
naive application of ordinary everywhere-differentiable monotonicity. -/
theorem AEOperationalClockSegment.integrating_factor_deriv_nonneg_ae
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S) :
    ∀ᵐ u ∂volume, u ∈ Set.Icc m.a m.b →
      0 ≤ deriv
        (fun v => Real.exp (rho * m.physicalTime v) *
          potential (fun i => coordinate F g.impact (m.prices v i))) u := by
  filter_upwards [m.integrating_factor_ode_ae F rho g edges hF] with u hJ hmem
  rw [(hJ hmem).deriv]
  have hr :
      (∑ i, m.prices u i * (m.prices u i - F) /
        g.impact (m.prices u i)) ≤
        potential (fun i => coordinate F g.impact (m.prices u i)) :=
    restoring_drain_sum_le_potential_of_elasticity_ge_one
      F g hF hdiff hel (m.prices u) (m.positive_prices u hmem)
  have hfactor : 0 ≤ rho * m.timeSpeed u :=
    mul_nonneg hrho (m.nonnegative_time_speed u hmem)
  exact mul_nonneg
    (mul_nonneg (Real.exp_pos _).le hfactor)
    (sub_nonneg.mpr hr)

end MarketCrash
