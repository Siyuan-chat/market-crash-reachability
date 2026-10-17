import MarketCrash.StieltjesVariationClock
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Inverse variation clock on one continuous physical-time piece only.
No assertion of a physical BV ODE projection or atomic graph completion. -/
noncomputable section
namespace MarketCrash
open Set
open scoped NNReal
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

theorem StieltjesPairedExecution.variationClock_continuousOn
    (exec : StieltjesPairedExecution edges) (scale a b : ℝ)
    (hc : ∀ e, ContinuousOn (exec.cumulative e) (Icc a b)) :
    ContinuousOn (exec.variationClock scale) (Icc a b) := by
  exact continuousOn_id.add (continuousOn_const.mul
    (continuousOn_finset_sum Finset.univ (fun e _ => hc e)))

theorem StieltjesPairedExecution.continuous_clock_inverse
    (exec : StieltjesPairedExecution edges) (scale a b : ℝ)
    (hs : 0 < scale) (hab : a ≤ b)
    (hc : ∀ e, ContinuousOn (exec.cumulative e) (Icc a b)) :
    ∃ time : Icc (exec.variationClock scale a) (exec.variationClock scale b) → Icc a b,
      (∀ u, exec.variationClock scale (time u) = (u : ℝ)) ∧
      (∀ t ∈ Icc a b, exec.variationClock scale t ∈
        Icc (exec.variationClock scale a) (exec.variationClock scale b)) ∧
      (∀ t : Icc a b, ∀ hu : exec.variationClock scale (t : ℝ) ∈
          Icc (exec.variationClock scale a) (exec.variationClock scale b),
        (time ⟨exec.variationClock scale t, hu⟩ : ℝ) = t) ∧
      (∀ u : Icc (exec.variationClock scale a) (exec.variationClock scale b),
        (u : ℝ) = exec.variationClock scale a → (time u : ℝ) = a) ∧
      (∀ u : Icc (exec.variationClock scale a) (exec.variationClock scale b),
        (u : ℝ) = exec.variationClock scale b → (time u : ℝ) = b) ∧
      LipschitzWith 1 (fun u => (time u : ℝ)) ∧
      (∀ e, LipschitzWith (⟨1 / scale, by positivity⟩ : ℝ≥0)
        (fun u => (exec.cumulative e) (time u))) := by
  have hmono := exec.variationClock_strictMono scale hs.le
  have hclock := exec.variationClock_continuousOn scale a b hc
  have hex : ∀ u : Icc (exec.variationClock scale a) (exec.variationClock scale b),
      ∃ t : Icc a b, exec.variationClock scale (t : ℝ) = u := by
    intro u
    have hu : (u : ℝ) ∈ uIcc (exec.variationClock scale a) (exec.variationClock scale b) := by
      simpa only [uIcc_of_le (hmono.monotone hab)] using u.property
    obtain ⟨t, ht, heq⟩ := intermediate_value_uIcc
      (f := exec.variationClock scale) (by simpa [uIcc_of_le hab] using hclock) hu
    exact ⟨⟨t, by simpa [uIcc_of_le hab] using ht⟩, heq⟩
  let time := fun u => Classical.choose (hex u)
  have hright : ∀ u, exec.variationClock scale (time u : ℝ) = (u : ℝ) :=
    fun u => Classical.choose_spec (hex u)
  have hincr (u v : Icc (exec.variationClock scale a) (exec.variationClock scale b))
      (huv : (u : ℝ) ≤ v) :
      (time u : ℝ) ≤ time v ∧ (time v : ℝ) - time u ≤ (v : ℝ) - u := by
    have ht : (time u : ℝ) ≤ time v := hmono.le_iff_le.mp (by simpa [hright] using huv)
    refine ⟨ht, ?_⟩
    simpa [hright] using exec.physicalTime_le_clock_increment scale (time u) (time v) hs.le ht
  refine ⟨time, hright, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hmono.monotone ht.1, hmono.monotone ht.2⟩
  · intro t hu
    exact hmono.injective (hright ⟨_, hu⟩)
  · intro u hu
    exact hmono.injective ((hright u).trans hu)
  · intro u hu
    exact hmono.injective ((hright u).trans hu)
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq, Subtype.dist_eq, one_mul, NNReal.coe_one]
    rcases le_total (u : ℝ) v with huv | hvu
    · have h := hincr u v huv
      rw [abs_of_nonpos (sub_nonpos.mpr h.1), abs_of_nonpos (sub_nonpos.mpr huv)]
      linarith [h.2]
    · have h := hincr v u hvu
      rw [abs_of_nonneg (sub_nonneg.mpr h.1), abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact h.2
  · intro e
    apply LipschitzWith.of_dist_le_mul
    intro u v
    simp only [Real.dist_eq, Subtype.dist_eq, NNReal.coe_mk]
    have hbound (x y : Icc (exec.variationClock scale a) (exec.variationClock scale b))
        (hxy : (x : ℝ) ≤ y) :
        (exec.cumulative e) (time y) - (exec.cumulative e) (time x) ≤
          (1 / scale) * ((y : ℝ) - x) := by
      have ht := (hincr x y hxy).1
      have hh := exec.edgeMass_le_clock_increment scale (time x) (time y) hs.le ht e
      rw [exec.intervalMass_eq_delta e _ _ ht, hright, hright] at hh
      calc
        _ ≤ ((y : ℝ) - x) / scale := (le_div_iff₀ hs).mpr (by nlinarith)
        _ = _ := by ring
    rcases le_total (u : ℝ) v with huv | hvu
    · have ht := (hincr u v huv).1
      rw [abs_of_nonpos (sub_nonpos.mpr ((exec.cumulative e).mono ht)),
        abs_of_nonpos (sub_nonpos.mpr huv)]
      simpa only [neg_sub] using hbound u v huv
    · have ht := (hincr v u hvu).1
      rw [abs_of_nonneg (sub_nonneg.mpr ((exec.cumulative e).mono ht)),
        abs_of_nonneg (sub_nonneg.mpr hvu)]
      exact hbound v u hvu

end MarketCrash
