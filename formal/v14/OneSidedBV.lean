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

theorem one_sided_BV_original_path
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ι → ℝ} {response : ι → Response}
    {edges : κ → PairedEdge ι}
    (p : OriginalAdmissiblePhysicalPath F rho response edges) (i : ι) :
    max (-(coordinate (F i) (response i).impact (p.terminal.prices i))) 0 ≤
      p.trace.dollarSales i ∧
    max (-(shareResponseCoordinate (F i) (response i).impact (p.terminal.prices i))) 0 ≤
      p.trace.shareSales i := by
  have hd := p.trace.dollar_resource_lower i
  have hs := p.trace.share_resource_lower i
  rw [p.initial_prices i, coordinate_at_benchmark] at hd
  rw [p.initial_prices i, shareResponseCoordinate_at_benchmark] at hs
  simp only [min_self, zero_sub] at hd hs
  constructor
  · apply max_le
    · linarith
    · exact p.trace.dollarSales_nonnegative i
  · apply max_le
    · linarith
    · exact p.trace.shareSales_nonnegative i

#print axioms MarketCrashV14.one_sided_BV_original_path

end MarketCrashV14
