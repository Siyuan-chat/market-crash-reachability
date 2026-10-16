import MarketCrash.StieltjesVariationClock

/-!
# Actual atomic masses and the gaps of the Stieltjes variation clock

A monotone right-continuous cumulative executed-dollar function can jump.
The graph clock u(t) = t + scale * Σ_e Z_e(t) therefore skips an interval
whose length is the scaled sum of the ACTUAL singleton Stieltjes masses.

This file determines both endpoints of this gap and constructs a simple
proportional affine interpolation with fixed physical time. This is an
explicit monotone *candidate* gap filling for the cumulative dollar state;
it is NOT assumed to preserve the original chronological execution order
at simultaneous edge atoms, nor to supply physical price/inventory flows.
Those M1--M5 equivalence obligations remain separate.
-/
noncomputable section
namespace MarketCrash

open MeasureTheory

/-- The executed-dollar mass at a single jump of an edge. -/
def StieltjesPairedExecution.atomicMass
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t : ℝ) : ℝ :=
  (exec.cumulative e) t - Function.leftLim (exec.cumulative e) t

/-- Atoms are nonnegative, including the case of no jump. -/
theorem StieltjesPairedExecution.atomicMass_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t : ℝ) :
    0 ≤ exec.atomicMass e t := by
  unfold StieltjesPairedExecution.atomicMass
  exact sub_nonneg.mpr ((exec.cumulative e).mono.leftLim_le le_rfl)

/-- Actual singleton Lebesgue--Stieltjes measure equals the atomic
executed-dollar amount. No density in physical time is assumed. -/
theorem StieltjesPairedExecution.atomicMass_eq_measure
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t : ℝ) :
    exec.atomicMass e t =
      (((exec.cumulative e).measure {t}).toReal) := by
  rw [StieltjesFunction.measure_singleton]
  exact (ENNReal.toReal_ofReal (exec.atomicMass_nonneg e t)).symm

/-- The left endpoint of the skipped clock interval at physical time t. -/
def StieltjesPairedExecution.leftClock
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) : ℝ :=
  t + scale * ∑ e, Function.leftLim (exec.cumulative e) t

/-- The exact difference between the right and left clock values is
the scaled sum of per-edge executed-dollar atoms at that time. -/
theorem StieltjesPairedExecution.atomic_clock_gap
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) :
    exec.variationClock scale t - exec.leftClock scale t =
      scale * ∑ e, exec.atomicMass e t := by
  unfold StieltjesPairedExecution.variationClock
    StieltjesPairedExecution.leftClock
    StieltjesPairedExecution.atomicMass
  rw [← Finset.sum_sub_distrib]
  ring

theorem StieltjesPairedExecution.leftClock_le_clock
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) (hscale : 0 ≤ scale) :
    exec.leftClock scale t ≤ exec.variationClock scale t := by
  rw [← sub_nonneg, exec.atomic_clock_gap]
  exact mul_nonneg hscale (Finset.sum_nonneg (fun e _ => exec.atomicMass_nonneg e t))

/-- The skipped clock width is exactly the total of scaled real
singleton Stieltjes masses, not a generic assumed jump size. -/
theorem StieltjesPairedExecution.atomic_clock_gap_eq_measure
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) :
    exec.variationClock scale t - exec.leftClock scale t =
      scale * ∑ e, ((exec.cumulative e).measure {t}).toReal := by
  rw [exec.atomic_clock_gap]
  congr 1
  exact Finset.sum_congr rfl (fun e _ => exec.atomicMass_eq_measure e t)

/-- Affine candidate interpolation for one edge's cumulative executed
dollars across a jump, parameterized by 0 ≤ r ≤ 1. -/
def StieltjesPairedExecution.gapEdge
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t r : ℝ) : ℝ :=
  Function.leftLim (exec.cumulative e) t + r * exec.atomicMass e t

theorem StieltjesPairedExecution.gapEdge_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t : ℝ) :
    exec.gapEdge e t 0 = Function.leftLim (exec.cumulative e) t := by
  simp [StieltjesPairedExecution.gapEdge]

theorem StieltjesPairedExecution.gapEdge_one
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t : ℝ) :
    exec.gapEdge e t 1 = (exec.cumulative e) t := by
  unfold StieltjesPairedExecution.gapEdge StieltjesPairedExecution.atomicMass
  ring

theorem StieltjesPairedExecution.gapEdge_monotone
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (e : κ) (t : ℝ) :
    Monotone (exec.gapEdge e t) := by
  intro r s hrs
  unfold StieltjesPairedExecution.gapEdge
  have h := mul_le_mul_of_nonneg_right hrs (exec.atomicMass_nonneg e t)
  linarith

/-- Affine interpolation of the common clock across the same gap. -/
def StieltjesPairedExecution.gapClock
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t r : ℝ) : ℝ :=
  exec.leftClock scale t + r * (scale * ∑ e, exec.atomicMass e t)

theorem StieltjesPairedExecution.gapClock_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) :
    exec.gapClock scale t 0 = exec.leftClock scale t := by
  simp [StieltjesPairedExecution.gapClock]

theorem StieltjesPairedExecution.gapClock_one
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) :
    exec.gapClock scale t 1 = exec.variationClock scale t := by
  have h := exec.atomic_clock_gap scale t
  unfold StieltjesPairedExecution.gapClock
  nlinarith

theorem StieltjesPairedExecution.gapClock_monotone
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {edges : κ → PairedEdge ι}
    (exec : StieltjesPairedExecution edges)
    (scale t : ℝ) (hscale : 0 ≤ scale) :
    Monotone (exec.gapClock scale t) := by
  intro r s hrs
  unfold StieltjesPairedExecution.gapClock
  have hm : 0 ≤ scale * ∑ e, exec.atomicMass e t :=
    mul_nonneg hscale (Finset.sum_nonneg (fun e _ => exec.atomicMass_nonneg e t))
  have h := mul_le_mul_of_nonneg_right hrs hm
  linarith

end MarketCrash
