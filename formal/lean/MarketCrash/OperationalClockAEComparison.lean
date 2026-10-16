import MarketCrash.OperationalClockAE
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The precise a.e.-FTC proof gate for the market barrier

The Phase 3 physical model derives a nonnegative derivative of
J(u) = exp(rho*t(u)) * sum_i Phi(S_i(u)) almost everywhere. Unlike an
everywhere-derivative comparison, this alone does NOT establish endpoint
nonnegativity: for example the Cantor function shows the danger of
inferring endpoint differences from a.e. derivatives without absolute
continuity.

Here we factor out the exact remaining real-analysis requirement:
the fundamental theorem of calculus for J on the completed operational
interval. We establish the market barrier conditional on this analytical
identity. This is a proof obligation, not an additional economic market
axiom, and must ultimately be DERIVED from Lipschitz/absolute continuity
on the completed graph to close the whole-paper M1--M5 statement.
-/

noncomputable section
namespace MarketCrash
open MeasureTheory

/-- With the a.e. fundamental theorem of calculus, a nonnegative
derivative almost everywhere really does propagate positivity from one
endpoint to the other. The FTC identity is an explicit hypothesis here. -/
theorem nonnegative_of_ae_derivative_and_FTC
    (J : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hae : ∀ᵐ u ∂volume, u ∈ Set.Icc a b → 0 ≤ deriv J u)
    (hFTC : (∫ u in a..b, deriv J u) = J b - J a)
    (hstart : 0 ≤ J a) :
    0 ≤ J b := by
  have hrestricted :
      0 ≤ᵐ[volume.restrict (Set.Icc a b)] (fun u => deriv J u) :=
    (ae_restrict_iff' measurableSet_Icc).mpr hae
  have hint : (0 : ℝ) ≤ ∫ u in a..b, deriv J u :=
    intervalIntegral.integral_nonneg_of_ae_restrict hab hrestricted
  rw [hFTC] at hint
  linarith

/-- The physical a.e. execution dynamics imply the market's full
endpoint potential barrier ONCE the absolutely-continuous FTC for the
derived integrating factor is supplied. No price-coordinate conservation
is assumed in the physical model. -/
theorem AEOperationalClockSegment.potential_nonnegative_of_FTC
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : AEOperationalClockSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hel : ∀ S : ℝ, 0 < S → 1 ≤ responseElasticity g.impact S)
    (hFTC :
      (∫ u in m.a..m.b,
        deriv (fun v => Real.exp (rho * m.physicalTime v) *
          potential (fun i => coordinate F g.impact (m.prices v i))) u) =
      Real.exp (rho * m.physicalTime m.b) *
        potential (fun i => coordinate F g.impact (m.prices m.b i)) -
      Real.exp (rho * m.physicalTime m.a) *
        potential (fun i => coordinate F g.impact (m.prices m.a i)))
    (hstart : 0 ≤ potential
      (fun i => coordinate F g.impact (m.prices m.a i))) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  let J : ℝ → ℝ := fun v => Real.exp (rho * m.physicalTime v) *
    potential (fun i => coordinate F g.impact (m.prices v i))
  have hFTC' : (∫ u in m.a..m.b, deriv J u) =
      J m.b - J m.a := hFTC
  have hJstart : 0 ≤ J m.a :=
    mul_nonneg (Real.exp_pos _).le hstart
  have hJend : 0 ≤ J m.b :=
    nonnegative_of_ae_derivative_and_FTC
      J m.a m.b m.time_order
      (m.integrating_factor_deriv_nonneg_ae F rho g edges
        hF hrho hdiff hel)
      hFTC' hJstart
  classical
  by_contra hbad
  have hneg : potential (fun i => coordinate F g.impact (m.prices m.b i)) < 0 :=
    lt_of_not_ge hbad
  have hJneg : J m.b < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  exact (not_lt_of_ge hJend) hJneg

end MarketCrash
