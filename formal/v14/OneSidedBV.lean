import MarketCrash.OriginalResources

/-!
V14-R1, `lem:one-sided-BV`: a direct original-model formulation of the
one-sided resource variation bound.  We reuse the existing source-faithful
continuous-BV and finite flow-completed pulse lemmas, rather than installing
the desired inequality as a hypothesis.

`trace.dollarSales` and `trace.shareSales` are sums of the genuine Jordan
negative variations on the chronologically joined completed pieces.
-/

noncomputable section
namespace MarketCrashV14

open MarketCrash

/-- A trace-level result: no terminal dollar closure is required, so the
paper's one-sided bound also holds for every physically feasible prefix. -/
theorem one_sided_BV_original_trace
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {response : ι → Response}
    {edges : κ → PairedEdge ι}
    {s t : PhysicalMarketState ι}
    (trace : OriginalPhysicalReachable F rho response edges s t)
    (i : ι) (hstart : s.prices i = F i) :
    max (-(coordinate (F i) (response i).impact (t.prices i))) 0 ≤
      trace.dollarSales i ∧
    max (-(shareResponseCoordinate (F i) (response i).impact (t.prices i))) 0 ≤
      trace.shareSales i := by
  have hd := trace.dollar_resource_lower i
  have hs := trace.share_resource_lower i
  rw [hstart, coordinate_at_benchmark] at hd
  rw [hstart, shareResponseCoordinate_at_benchmark] at hs
  simp only [min_self, zero_sub] at hd hs
  constructor
  · apply max_le
    · linarith
    · exact trace.dollarSales_nonnegative i
  · apply max_le
    · linarith
    · exact trace.shareSales_nonnegative i

/-- The V14 lemma for an original admissible physical path, derived from
the stronger path-prefix version above (which does not need dollar closure). -/
theorem one_sided_BV_original_path
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {response : ι → Response}
    {edges : κ → PairedEdge ι}
    (p : OriginalAdmissiblePhysicalPath F rho response edges) (i : ι) :
    max (-(coordinate (F i) (response i).impact (p.terminal.prices i))) 0 ≤
      p.trace.dollarSales i ∧
    max (-(shareResponseCoordinate (F i) (response i).impact (p.terminal.prices i))) 0 ≤
      p.trace.shareSales i :=
  one_sided_BV_original_trace p.trace i (p.initial_prices i)

#print axioms MarketCrashV14.one_sided_BV_original_trace
#print axioms MarketCrashV14.one_sided_BV_original_path

end MarketCrashV14
