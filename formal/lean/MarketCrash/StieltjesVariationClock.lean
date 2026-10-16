import MarketCrash.StieltjesExecution

/-!
# The physical-time plus executed-dollar variation clock

A Stieltjes cumulative dollar control can be singular continuous or have
atoms. For a common operational clock, give executed dollars a positive
conversion factor `scale` (with units of time per currency amount) and
set u(t) = t + scale * sum_e Z_e(t).

This file proves that the increase of u dominates elapsed physical time
and EACH scaled directed-edge executed-dollar increment. These estimates
are the finite-measure input for graph completion; they do not construct
a Lipschitz inverse or resolve the internal order at multi-edge jumps.
In particular, the u(t) clock is generally discontinuous at atoms.
-/

noncomputable section
namespace MarketCrash

/-- Scalar accumulation of normalized physical time and all directed-edge
executed-dollar balances. An arbitrary additive origin does not affect
any interval increments. -/
def StieltjesPairedExecution.variationClock
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges) (scale t : ℝ) : ℝ :=
  t + scale * ∑ e, (exec.cumulative e) t

/-- Exact graph-clock increment, including the singular and atomic
dollar mass on the specified half-open interval. -/
theorem StieltjesPairedExecution.variationClock_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale s t : ℝ) :
    exec.variationClock scale t - exec.variationClock scale s =
      (t - s) + scale *
        ∑ e, ((exec.cumulative e) t - (exec.cumulative e) s) := by
  unfold StieltjesPairedExecution.variationClock
  calc
    (t + scale * ∑ e, (exec.cumulative e) t) -
        (s + scale * ∑ e, (exec.cumulative e) s) =
      (t - s) + scale *
        ((∑ e, (exec.cumulative e) t) - (∑ e, (exec.cumulative e) s)) := by
          ring
    _ = (t - s) + scale *
        ∑ e, ((exec.cumulative e) t - (exec.cumulative e) s) := by
          rw [Finset.sum_sub_distrib]

/-- The increase in the common graph clock bounds elapsed physical time.
This statement holds for every monotone right-continuous Stieltjes
control, even when its distribution is singular. -/
theorem StieltjesPairedExecution.physicalTime_le_clock_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale s t : ℝ) (hscale : 0 ≤ scale) (hst : s ≤ t) :
    t - s ≤ exec.variationClock scale t - exec.variationClock scale s := by
  rw [exec.variationClock_increment]
  apply le_add_of_nonneg_right
  apply mul_nonneg hscale
  apply Finset.sum_nonneg
  intro e _
  exact sub_nonneg.mpr ((exec.cumulative e).mono hst)

/-- The same clock dominates any ONE scaled edge-dollar increment,
not just the sum across all edges. This inequality is the prospective
one-Lipschitz estimate after inverse-graph completion. -/
theorem StieltjesPairedExecution.edgeMass_le_clock_increment
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale s t : ℝ) (hscale : 0 ≤ scale) (hst : s ≤ t)
    (e : κ) :
    scale * exec.intervalMass e s t ≤
      exec.variationClock scale t - exec.variationClock scale s := by
  classical
  rw [exec.variationClock_increment, exec.intervalMass_eq_delta e s t hst]
  have hs : 0 ≤ t - s := sub_nonneg.mpr hst
  have he (e' : κ) : 0 ≤ (exec.cumulative e') t - (exec.cumulative e') s :=
    sub_nonneg.mpr ((exec.cumulative e').mono hst)
  have hsum :
      (exec.cumulative e) t - (exec.cumulative e) s ≤
        ∑ e', ((exec.cumulative e') t - (exec.cumulative e') s) := by
    exact Finset.single_le_sum (fun e' _ hne => he e') (Finset.mem_univ e)
  have hscaled := mul_le_mul_of_nonneg_left hsum hscale
  linarith

/-- The clock is monotone, even across simultaneous edge atoms.
The total increment is larger than physical elapsed time. -/
theorem StieltjesPairedExecution.variationClock_monotone
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale : ℝ) (hscale : 0 ≤ scale) :
    Monotone (exec.variationClock scale) := by
  intro s t hst
  have hbound := exec.physicalTime_le_clock_increment scale s t hscale hst
  have hs : 0 ≤ t - s := sub_nonneg.mpr hst
  exact sub_nonneg.mp (hs.trans hbound)

end MarketCrash
