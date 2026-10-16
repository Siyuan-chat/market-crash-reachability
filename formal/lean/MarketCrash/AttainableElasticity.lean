import MarketCrash.LocalElasticity
import Mathlib.Topology.Order.IntermediateValue

/-!
Attainable-price elasticity for a single smooth physical execution segment.

This proves two distinct missing links for the regular continuous subclass:
1. A scalar integrating-factor comparison using only actual times [a,b].
2. The intermediate-value fact that each price between the starting
   benchmark F and a price visited at time t is itself attained at some
   execution time s ∈ [a,t].

Consequently the local radial restoring inequality needs e(S) >= 1 only
at prices VISITED by the physical path, rather than all positive prices.

These statements are about the smooth regular continuous subclass, not
the full M5 BV/Marcus path class. The latter still needs Stieltjes calculus.
-/
noncomputable section
namespace MarketCrash

/-- Time-LOCAL integrating-factor comparison: from H'(u) >= -rho H(u)
for u ∈ [a,b], positivity of H(a) implies positivity of H(b).
No differential inequality outside the actual time interval is assumed. -/
theorem nonnegative_of_derivative_ge_linear_on_Icc
    (H slope : ℝ → ℝ) (rho a b : ℝ) (hab : a ≤ b)
    (hd : ∀ u ∈ Set.Icc a b, HasDerivAt H (slope u) u)
    (hb : ∀ u ∈ Set.Icc a b, -rho * H u ≤ slope u)
    (hstart : 0 ≤ H a) :
    0 ≤ H b := by
  let J : ℝ → ℝ := fun u => Real.exp (rho * u) * H u
  have hJ (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt J (Real.exp (rho * u) * (rho * H u + slope u)) u := by
    have hlin : HasDerivAt (fun v : ℝ => rho * v) rho u := by
      convert (hasDerivAt_id u).const_mul rho using 1 <;> ring
    have hexp : HasDerivAt (fun v : ℝ => Real.exp (rho * v))
        (Real.exp (rho * u) * rho) u :=
      (Real.hasDerivAt_exp (rho * u)).comp u hlin
    convert (hexp.mul (hd u hu)) using 1 <;> ring
  have hcont : ContinuousOn J (Set.Icc a b) := by
    intro u hu
    exact (hJ u hu).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ J (interior (Set.Icc a b)) := by
    intro u hu
    exact (hJ u (interior_subset hu)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ interior (Set.Icc a b), 0 ≤ deriv J u := by
    intro u hu
    have hmem : u ∈ Set.Icc a b := interior_subset hu
    rw [(hJ u hmem).deriv]
    have hlin : 0 ≤ rho * H u + slope u := by
      have hs := hb u hmem
      linarith
    exact mul_nonneg (Real.exp_pos _).le hlin
  have hmono : MonotoneOn J (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hderiv
  have hJa : 0 ≤ J a := by
    change 0 ≤ Real.exp (rho * a) * H a
    exact mul_nonneg (Real.exp_pos _).le hstart
  have hJb : 0 ≤ J b := hJa.trans (hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)
  by_contra hbad
  have hneg : H b < 0 := lt_of_not_ge hbad
  have hJneg : J b < 0 := mul_neg_of_pos_of_neg (Real.exp_pos _) hneg
  exact (not_lt_of_ge hJb) hJneg

/-- Every price between a smooth segment's starting benchmark F and its
price at time t is really attained somewhere on [a,t], by IVT.
The price path is continuous because its physical ODE is differentiable. -/
theorem PhysicalSmoothSegment.radial_price_attained
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : PhysicalSmoothSegment F rho g edges)
    (i : ι) (hinit : m.prices m.a i = F)
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (x : ℝ) (hx : x ∈ Set.Icc (min F (m.prices t i))
      (max F (m.prices t i))) :
    ∃ u ∈ Set.Icc m.a t, m.prices u i = x := by
  have hc : ContinuousOn (fun u : ℝ => m.prices u i) (Set.uIcc m.a t) := by
    intro u _
    exact (m.price_ode u i).continuousAt.continuousWithinAt
  have hbetween : x ∈ Set.uIcc (m.prices m.a i) (m.prices t i) := by
    simpa only [Set.uIcc, hinit] using hx
  obtain ⟨u, hu, heq⟩ := (intermediate_value_uIcc hc) hbetween
  refine ⟨u, ?_, heq⟩
  simpa only [Set.uIcc_of_le ht.1] using hu

/-- Along a smooth physical price/share/dollar execution that starts
at the common benchmark F, elasticity e>=1 at the ACTUALLY VISITED
prices suffices to keep H(b)>=0. This neither assumes global
elasticity nor assumes a radial elasticity bound. -/
theorem PhysicalSmoothSegment.potential_nonnegative_of_attained_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : PhysicalSmoothSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ t ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices t i)) :
    0 ≤ potential (fun i => coordinate F g.impact (m.prices m.b i)) := by
  let H : ℝ → ℝ := fun t =>
    potential (fun i => coordinate F g.impact (m.prices t i))
  let slope : ℝ → ℝ := fun t =>
    -rho * ∑ i, m.prices t i * (m.prices t i - F) /
      g.impact (m.prices t i)
  have hd (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
      HasDerivAt H (slope t) t :=
    m.potential_ode F rho g edges hF t
  have hbound (t : ℝ) (ht : t ∈ Set.Icc m.a m.b) :
      -rho * H t ≤ slope t := by
    have hrestore := restoring_drain_sum_le_potential_of_radial_elasticity
      F g hF (m.prices t) (m.positive_prices t)
      (fun i x hx => by
        have hp : 0 < x :=
          (lt_min hF (m.positive_prices t i)).trans_le hx.1
        exact hdiff x hp)
      (fun i x hx => by
        obtain ⟨u, hu, heq⟩ := m.radial_price_attained
          F rho g edges i (hinit i) t ht x hx
        have hab : u ∈ Set.Icc m.a m.b :=
          ⟨hu.1, hu.2.trans ht.2⟩
        rw [← heq]
        exact hel u hab i)
    have hnonneg : 0 ≤ rho * (H t -
        ∑ i, m.prices t i * (m.prices t i - F) /
          g.impact (m.prices t i)) :=
      mul_nonneg hrho (sub_nonneg.mpr hrestore)
    dsimp [slope]
    nlinarith
  have hstart : 0 ≤ H m.a := by
    have hz (i : ι) : coordinate F g.impact (m.prices m.a i) = 0 := by
      rw [hinit i, coordinate_at_benchmark]
    simp [H, potential, hz]
  exact nonnegative_of_derivative_ge_linear_on_Icc
    H slope rho m.a m.b m.time_order hd hbound hstart

/-- Smooth physical-market Theorem 3.1 with elasticity restricted to
prices visited by that execution on [a,b] (no global e assumption). -/
theorem PhysicalSmoothSegment.no_all_asset_decline_of_attained_elasticity
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : PhysicalSmoothSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ t ∈ Set.Icc m.a m.b, ∀ i,
      1 ≤ responseElasticity g.impact (m.prices t i)) :
    ¬ ∀ i, m.prices m.b i < F := by
  exact not_all_below_benchmark F g hF (m.prices m.b)
    (m.positive_prices m.b)
    (m.potential_nonnegative_of_attained_elasticity
      F rho g edges hF hrho hdiff hinit hel)

end MarketCrash
