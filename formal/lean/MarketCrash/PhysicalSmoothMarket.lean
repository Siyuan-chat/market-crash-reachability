import MarketCrash.HybridPositivity
import MarketCrash.RestoringTangent
import MarketCrash.PotentialFromTime
import Mathlib.Analysis.BoundedVariation

/-!
Physical price-space dynamics for a smooth dollar-paired trading segment.

This layer encodes dS/dt = -rho (S-F) + g(S) dtheta/dt,
dtheta/dt = (B dot z)/S, and dX/dt = B dot z instead of
postulating the transformed coordinate equation. Nonnegative gross
directed edge rates, nonnegative shares, and finite share variation
on [a,b] are represented explicitly.

IMPORTANT: differentiability and positive prices are assumed on all ℝ,
not merely almost everywhere on [a,b]. This is a strong regular subclass
of Assumption M1-M5; it is not yet the manuscript's full BV market.
-/
noncomputable section
namespace MarketCrash

structure PhysicalSmoothSegment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  a : ℝ
  b : ℝ
  time_order : a ≤ b
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  rates : ℝ → κ → ℝ
  positive_prices : ∀ t i, 0 < prices t i
  nonnegative_rates : ∀ t e, 0 ≤ rates t e
  no_short_sales : ∀ t i, 0 ≤ shares t i
  finite_share_variation : ∀ i,
    BoundedVariationOn (fun t => shares t i) (Set.Icc a b)
  price_ode : ∀ t i, HasDerivAt (fun u => prices u i)
    (-rho * (prices t i - F) +
       g.impact (prices t i) *
         (tradingInput (pairedMatrix edges) (rates t) i / prices t i)) t
  share_ode : ∀ t i, HasDerivAt (fun u => shares u i)
    (tradingInput (pairedMatrix edges) (rates t) i / prices t i) t
  ledger_ode : ∀ t i, HasDerivAt (fun u => dollarLedger u i)
    (tradingInput (pairedMatrix edges) (rates t) i) t

/-- The transformed dynamics are DEDUCED from the physical price ODE.
    In particular, dollar pairing is not replaced by a new assumption. -/
theorem PhysicalSmoothSegment.coordinate_ode
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : PhysicalSmoothSegment F rho g edges) (hF : 0 < F)
    (t : ℝ) (i : ι) :
    HasDerivAt (fun u => coordinate F g.impact (m.prices u i))
      (tradingInput (pairedMatrix edges) (m.rates t) i -
        rho * (m.prices t i * (m.prices t i - F) / g.impact (m.prices t i))) t := by
  have hp : m.prices t i ≠ 0 := (m.positive_prices t i).ne'
  have hg : g.impact (m.prices t i) ≠ 0 :=
    (g.positive (m.prices t i) (m.positive_prices t i)).ne'
  have h := (coordinate_hasDerivAt F g hF (m.positive_prices t i)).comp
    t (m.price_ode t i)
  convert h using 1
  · simp only [Function.comp_def]
  · field_simp [hp, hg] <;> ring

/-- Summing the physically derived coordinate equations cancels each
    paired-dollar trade, leaving only the genuine resilience drift. -/
theorem PhysicalSmoothSegment.potential_ode
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : PhysicalSmoothSegment F rho g edges) (hF : 0 < F)
    (t : ℝ) :
    HasDerivAt
      (fun u => potential (fun i => coordinate F g.impact (m.prices u i)))
      (-rho * ∑ i, m.prices t i * (m.prices t i - F) /
        g.impact (m.prices t i)) t := by
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun i _ => m.coordinate_ode F rho g edges hF t i)
  have heq :
      (∑ i, (tradingInput (pairedMatrix edges) (m.rates t) i -
        rho * (m.prices t i * (m.prices t i - F) /
          g.impact (m.prices t i)))) =
      -rho * ∑ i, m.prices t i * (m.prices t i - F) /
        g.impact (m.prices t i) := by
    rw [Finset.sum_sub_distrib, paired_trading_sum_zero]
    simp [Finset.mul_sum]
  simpa [potential, heq] using hd

/-- The genuine physical-price equations preserve nonnegative
    generalized-price potential on any smooth segment, assuming the
    global elasticity lower bound from the existing curvature lemma. -/
theorem PhysicalSmoothSegment.potential_nonnegative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : PhysicalSmoothSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (hstart : 0 ≤ potential (fun i => coordinate F g.impact (m.prices m.a i))) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  let H : ℝ → ℝ := fun u =>
    potential (fun i => coordinate F g.impact (m.prices u i))
  let slope : ℝ → ℝ := fun u =>
    -rho * ∑ i, m.prices u i * (m.prices u i - F) /
      g.impact (m.prices u i)
  have hd (u : ℝ) : HasDerivAt H (slope u) u :=
    m.potential_ode F rho g edges hF u
  have hb (u : ℝ) : -rho * H u ≤ slope u := by
    have ht := restoring_drain_sum_le_potential_of_elasticity_ge_one
      F g hF hdiff hel (m.prices u) (m.positive_prices u)
    have hn : 0 ≤ rho * (H u -
        ∑ i, m.prices u i * (m.prices u i - F) /
          g.impact (m.prices u i)) :=
      mul_nonneg hrho (sub_nonneg.mpr ht)
    dsimp [slope]
    dsimp [H] at hn
    nlinarith
  exact nonnegative_of_derivative_ge_linear_from
    H slope rho hd hb m.a m.b m.time_order hstart

end MarketCrash
