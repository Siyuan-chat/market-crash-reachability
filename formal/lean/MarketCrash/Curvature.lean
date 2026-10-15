import MarketCrash.Coordinates

noncomputable section
namespace MarketCrash

def responseElasticity (g : ℝ → ℝ) (S : ℝ) : ℝ := S * deriv g S / g S

theorem coordinate_slope_hasDerivAt (g : ℝ → ℝ) (S g' : ℝ)
    (hg : HasDerivAt g g' S) (hgne : g S ≠ 0) :
    HasDerivAt (fun u => u / g u) ((1 - S * g' / g S) / g S) S := by
  convert (hasDerivAt_id S).div hg hgne using 1 <;>
    field_simp [hgne] <;> ring <;> simp_all

theorem coordinate_slope_elasticity (g : ℝ → ℝ) (S : ℝ)
    (hg : DifferentiableAt ℝ g S) (hgne : g S ≠ 0) :
    HasDerivAt (fun u => u / g u) ((1 - responseElasticity g S) / g S) S :=
  coordinate_slope_hasDerivAt g S (deriv g S) hg.hasDerivAt hgne

def logCoordinate (F : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  coordinate F g (F * Real.exp x)

theorem logCoordinate_hasDerivAt (F : ℝ) (g : Response) (hF : 0 < F) (x : ℝ) :
    HasDerivAt (logCoordinate F g.impact)
      ((F * Real.exp x) ^ 2 / g.impact (F * Real.exp x)) x := by
  have hs : 0 < F * Real.exp x := mul_pos hF (Real.exp_pos x)
  have h := (coordinate_hasDerivAt F g hF hs).comp x ((Real.hasDerivAt_exp x).const_mul F)
  convert h using 1 <;> simp_all [logCoordinate, pow_two, div_eq_mul_inv] <;> ring

theorem log_slope_hasDerivAt (F x g' : ℝ) (g : ℝ → ℝ)
    (hg : HasDerivAt g g' (F * Real.exp x)) (hgne : g (F * Real.exp x) ≠ 0) :
    HasDerivAt (fun u => (F * Real.exp u) ^ 2 / g (F * Real.exp u))
      (((F * Real.exp x) ^ 2 / g (F * Real.exp x)) *
        (2 - (F * Real.exp x) * g' / g (F * Real.exp x))) x := by
  have hs := (Real.hasDerivAt_exp x).const_mul F
  have h := (hs.pow 2).div (hg.comp x hs) hgne
  convert h using 1 <;> field_simp [hgne] <;> ring <;> simp_all

end MarketCrash
