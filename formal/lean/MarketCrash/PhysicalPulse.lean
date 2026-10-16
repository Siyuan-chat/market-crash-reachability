import MarketCrash.PhysicalSmoothMarket
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
Marginal-dollar flow completion for one directed paired-asset execution
pulse, as in manuscript (M2)/(2.3).

The original pulse is parameterized by executed dollars a∈[0,mass].
The derivatives of marginal prices, executed shares, and signed dollar
ledgers are tied to the SAME directed incidence edge.

The present endpoint-derivative representation is stronger than assuming
derivatives only on the pulse interior. This is a regular pulse subclass,
not yet every BV/piecewise-continuous admissible execution.
-/
noncomputable section
namespace MarketCrash

structure FlowCompletedPulse
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  edge : κ
  mass : ℝ
  nonnegative_mass : 0 ≤ mass
  prices : ℝ → ι → ℝ
  shares : ℝ → ι → ℝ
  dollarLedger : ℝ → ι → ℝ
  positive_prices : ∀ a ∈ Set.Icc (0 : ℝ) mass, ∀ i, 0 < prices a i
  no_short_sales : ∀ a ∈ Set.Icc (0 : ℝ) mass, ∀ i, 0 ≤ shares a i
  finite_share_variation : ∀ i,
    BoundedVariationOn (fun a => shares a i) (Set.Icc 0 mass)
  price_flow : ∀ a ∈ Set.Icc (0 : ℝ) mass, ∀ i,
    HasDerivAt (fun u => prices u i)
      (g.impact (prices a i) / prices a i * pairedMatrix edges i edge) a
  share_flow : ∀ a ∈ Set.Icc (0 : ℝ) mass, ∀ i,
    HasDerivAt (fun u => shares u i)
      (pairedMatrix edges i edge / prices a i) a
  ledger_flow : ∀ a ∈ Set.Icc (0 : ℝ) mass, ∀ i,
    HasDerivAt (fun u => dollarLedger u i) (pairedMatrix edges i edge) a

/-- The pulse flow equation implies that each marginal executed dollar
changes the generalized coordinate by exactly the signed edge incidence.
This is derived from the physical price flow, not postulated. -/
theorem FlowCompletedPulse.coordinate_hasDerivAt
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (p : FlowCompletedPulse F g edges) (hF : 0 < F)
    (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) p.mass) (i : ι) :
    HasDerivAt (fun u => coordinate F g.impact (p.prices u i))
      (pairedMatrix edges i p.edge) a := by
  have hs : 0 < p.prices a i := p.positive_prices a ha i
  have hp : p.prices a i ≠ 0 := hs.ne'
  have hg : g.impact (p.prices a i) ≠ 0 :=
    (g.positive (p.prices a i) hs).ne'
  have h := (coordinate_hasDerivAt F g hF hs).comp a
    (p.price_flow a ha i)
  convert h using 1 <;> dsimp [Function.comp] <;> field_simp [hp, hg] <;> ring

/-- The marginal-dollar ODE gives the exact coordinate change between
pulse endpoints. Both endpoints and all intermediate prices are positive
by the pulse's actual execution conditions. -/
theorem FlowCompletedPulse.coordinate_endpoint
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (p : FlowCompletedPulse F g edges) (hF : 0 < F)
    (i : ι) :
    coordinate F g.impact (p.prices p.mass i) =
      coordinate F g.impact (p.prices 0 i) +
        p.mass * pairedMatrix edges i p.edge := by
  have hFTC :
      (∫ a in (0 : ℝ)..p.mass, pairedMatrix edges i p.edge) =
        coordinate F g.impact (p.prices p.mass i) -
          coordinate F g.impact (p.prices 0 i) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro a ha
      exact p.coordinate_hasDerivAt F g edges hF a ha i
    · exact intervalIntegrable_const
  have hc :
      (∫ a in (0 : ℝ)..p.mass, pairedMatrix edges i p.edge) =
        p.mass * pairedMatrix edges i p.edge := by
    simp
  rw [hc] at hFTC
  linarith

/-- The signed-dollar ledger increment of the pulse is the executed
dollar mass times the incidence sign. -/
theorem FlowCompletedPulse.ledger_endpoint
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (p : FlowCompletedPulse F g edges) (i : ι) :
    p.dollarLedger p.mass i = p.dollarLedger 0 i +
      p.mass * pairedMatrix edges i p.edge := by
  have hFTC :
      (∫ a in (0 : ℝ)..p.mass, pairedMatrix edges i p.edge) =
        p.dollarLedger p.mass i - p.dollarLedger 0 i := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro a ha
      exact p.ledger_flow a ha i
    · exact intervalIntegrable_const
  have hc :
      (∫ a in (0 : ℝ)..p.mass, pairedMatrix edges i p.edge) =
        p.mass * pairedMatrix edges i p.edge := by
    simp
  rw [hc] at hFTC
  linarith

end MarketCrash
