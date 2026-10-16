import MarketCrash.WeakBVFiniteExecution
import MarketCrash.CrisisQuantile

/-!
# Exact V12 breadth and k=N consequence for weak BV price paths

These results connect the already proved physical-pulse/continuous
Stieltjes-BV weak-normal-form endpoint barriers to the PAPER's
logarithmic loss, k = ceil(alpha*N), and strictly positive thresholds.

They do not assume an aggregate potential invariant. The remaining
all-M1--M5 proof obligation is still the primitive marginal-settlement
to weak-normal-form continuous-BV chain rule and model inclusion.
-/

noncomputable section
namespace MarketCrash

/-- For strictly positive real asset prices, an actual strictly positive
k=N crisis threshold forces EVERY asset below the benchmark. This
formalizes the 'in particular' clause of Theorem 3.1, including its
genuine coverage quantile, without replacing it by an informal count. -/
theorem positive_full_coverage_crisis_forces_all_below
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (F : ℝ) (prices : ι → ℝ) (hF : 0 < F)
    (hp : ∀ i, 0 < prices i)
    (delta : ℝ) (hdelta : 0 < delta)
    (hcrisis : delta ≤ systemicCrisis
      (logPriceFromBenchmark F prices) (Fintype.card ι)) :
    ∀ i, prices i < F := by
  classical
  let q : ι → ℝ := logPriceFromBenchmark F prices
  have hk : 0 < Fintype.card ι := Fintype.card_pos
  have hcover :
      Fintype.card ι ≤
        (Finset.univ.filter (fun i : ι => delta ≤ -q i)).card :=
    ((systemicCrisis_threshold_iff q (Fintype.card ι)
      hk le_rfl delta).mp hcrisis).2
  have hfull :
      (Finset.univ.filter (fun i : ι => delta ≤ -q i)) =
        (Finset.univ : Finset ι) := by
    apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
    simpa using hcover
  intro i
  have hi : delta ≤ -q i := by
    have hmem : i ∈ Finset.univ.filter
        (fun i : ι => delta ≤ -q i) := by
      rw [hfull]
      exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hmem).2
  have hqneg : q i < 0 := by linarith
  have hexp : Real.exp (q i) < 1 := by
    simpa only [Real.exp_zero] using (Real.exp_strictMono hqneg)
  have hmul := mul_lt_mul_of_pos_left hexp hF
  have hprice : F * Real.exp (q i) = prices i :=
    exp_logPrice_eq_price F prices hF hp i
  rw [hprice, mul_one] at hmul
  exact hmul

/-- The verified finite mixed singular-continuous-BV/physical-pulse
3.1 exclusion also excludes any POSITIVE full-coverage crisis threshold,
using true executed prices and the paper's kth-largest loss statistic. -/
theorem RadiallyElasticWeakBVPriceReachable.no_positive_full_coverage_crisis
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    {s t : WeakBVPriceState ι}
    (trace : RadiallyElasticWeakBVPriceReachable F rho g edges s t)
    (hinit : ∀ i, s.prices i = F)
    (delta : ℝ) (hdelta : 0 < delta) :
    ¬ delta ≤ systemicCrisis (logPriceFromBenchmark F t.prices)
      (Fintype.card ι) := by
  intro hcrisis
  have hp : ∀ i, 0 < t.prices i :=
    trace.positive_terminal F rho g edges
      (fun i => by rw [hinit i]; exact hF)
  have hall := positive_full_coverage_crisis_forces_all_below
    F t.prices hF hp delta hdelta hcrisis
  exact (trace.no_all_asset_decline F rho g edges hF hrho
    hdiff hinit) hall

/-- Exact breadth-parameter version of the finite weak BV 3.2 result:
the true log-price score with k = ceil(alpha*N), alpha in (0,1].
Elasticity still appears explicitly on the required benchmark-to-endpoint
radial ranges, not at unrelated positive prices. -/
theorem RadiallyElasticWeakBVPriceReachable.no_systemic_crisis_at_breadth
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    {s t : WeakBVPriceState ι}
    (trace : RadiallyElasticWeakBVPriceReachable F rho g edges s t)
    (hinit : ∀ i, s.prices i = F)
    (alpha : ℝ) (halpha : 0 < alpha) (hale : alpha ≤ 1)
    (hel2 : ∀ i x,
      x ∈ Set.Icc
        (min 0 (logPriceFromBenchmark F t.prices i))
        (max 0 (logPriceFromBenchmark F t.prices i)) →
      2 ≤ responseElasticity g.impact (F * Real.exp x)) :
    systemicCrisis (logPriceFromBenchmark F t.prices)
      (requiredAssetCount (ι := ι) alpha) ≤ 0 := by
  have hp : ∀ i, 0 < t.prices i :=
    trace.positive_terminal F rho g edges
      (fun i => by rw [hinit i]; exact hF)
  exact trace.no_systemic_crisis F rho g edges hF hrho hdiff
    hinit (logPriceFromBenchmark F t.prices)
    (fun i => (exp_logPrice_eq_price F t.prices hF hp i).symm)
    hel2 (requiredAssetCount (ι := ι) alpha)


/-- Exact paper breadth for an arbitrary CONTINUOUS weak-Stieltjes-BV
solution at any physical-time horizon, including singular-continuous
nonatomic dollar execution. No standalone a.e. FTC premise is used.
This is not the original all-M1--M5 representation theorem. -/
theorem ContinuousWeakBVPriceSegment.no_systemic_crisis_at_breadth
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [Nonempty ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι)
    (m : ContinuousWeakBVPriceSegment F rho g edges)
    (hF : 0 < F) (hrho : 0 ≤ rho)
    (hdiff : ∀ S : ℝ, 0 < S → DifferentiableAt ℝ g.impact S)
    (hinit : ∀ i, m.prices m.a i = F)
    (hel : ∀ u ∈ Set.Icc m.a m.b, ∀ i,
      2 ≤ responseElasticity g.impact (m.prices u i))
    (t : ℝ) (ht : t ∈ Set.Icc m.a m.b)
    (alpha : ℝ) (halpha : 0 < alpha) (hale : alpha ≤ 1) :
    systemicCrisis
      (logPriceFromBenchmark F (m.prices t))
      (requiredAssetCount (ι := ι) alpha) ≤ 0 := by
  have hp : ∀ i, 0 < m.prices t i := m.positive_prices t ht
  exact m.no_systemic_crisis_of_visited_elasticity
    F rho g edges hF hrho hdiff hinit hel t ht
    (logPriceFromBenchmark F (m.prices t))
    (fun i => (exp_logPrice_eq_price F (m.prices t) hF hp i).symm)
    (requiredAssetCount (ι := ι) alpha)


end MarketCrash
