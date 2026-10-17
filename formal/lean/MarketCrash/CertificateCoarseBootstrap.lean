import MarketCrash.LipschitzFTC

open Set MeasureTheory
open scoped NNReal
namespace MarketCrash.OriginalCertificate

/-- Two endpoint enclosures and an already proved Lipschitz bound give a
pointwise double-ended enclosure; no differential bound is used here. -/
theorem certificateBootstrap_endpoint_box {Y : ℝ → ℝ} {a b la ua lb ub : ℝ}
    {L : ℝ≥0} (hab : a ≤ b) (hY : LipschitzOnWith L Y (Icc a b))
    (ha : Y a ∈ Icc la ua) (hb : Y b ∈ Icc lb ub) :
    ∀ t ∈ Icc a b, Y t ∈ Icc
      (max (la - L * (t-a)) (lb - L * (b-t)))
      (min (ua + L * (t-a)) (ub + L * (b-t))) := by
  intro t ht
  have hta := hY.dist_le_mul t ht a ⟨le_rfl, hab⟩
  have htb := hY.dist_le_mul t ht b ⟨hab, le_rfl⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)] at hta
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at htb
  have hta' := abs_le.mp hta
  have htb' := abs_le.mp htb
  constructor
  · apply max_le <;> linarith [ha.1, hb.1]
  · apply le_min <;> linarith [ha.2, hb.2]

/-- A genuine AE derivative bound improves a pre-existing Lipschitz constant
by the Lipschitz FTC, including degenerate intervals. -/
theorem certificateBootstrap_lipschitz_of_ae_derivative {Y w : ℝ → ℝ}
    {a b : ℝ} {L₀ L₁ : ℝ≥0} (hY : LipschitzOnWith L₀ Y (Icc a b))
    (hder : ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt Y (w t) t)
    (hw : ∀ᵐ t ∂volume, t ∈ Icc a b → |w t| ≤ L₁) :
    LipschitzOnWith L₁ Y (Icc a b) := by
  have hordered (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b)
      (hst : s ≤ t) : |Y t - Y s| ≤ L₁ * |t-s| := by
    have hsub : Icc s t ⊆ Icc a b := fun x hx => ⟨hs.1.trans hx.1, hx.2.trans ht.2⟩
    have hd : ∀ᵐ x ∂volume, x ∈ Ioo s t → HasDerivAt Y (w x) x := by
      filter_upwards [hder] with x hx hxt
      exact hx ⟨lt_of_le_of_lt hs.1 hxt.1, lt_of_lt_of_le hxt.2 ht.2⟩
    have he := (MarketCrash.lipschitzOn_integral_eq_sub_of_hasDerivAt_ae
      (hY.mono hsub) hst hd).2
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := s) (b := t) (C := (L₁:ℝ)) (f := w) (by
        filter_upwards [hw] with x hbound hx
        rw [uIoc_of_le hst] at hx
        simpa only [Real.norm_eq_abs] using hbound (hsub ⟨hx.1.le, hx.2⟩))
    simpa only [he, Real.norm_eq_abs] using hn
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total s t with hst | hts
  · simpa only [abs_sub_comm] using hordered s hs t ht hst
  · exact hordered t ht s hs hts

/-- Non-circular bootstrap: the original constant constructs the coarse box;
the actual field is bounded on that box; FTC then gives the refined constant
and the refined two-ended box for the same solution. -/
theorem certificateBootstrap_refine {Y : ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    {a b la ua lb ub : ℝ} {L₀ L₁ : ℝ≥0}
    (hab : a ≤ b) (hY : LipschitzOnWith L₀ Y (Icc a b))
    (ha : Y a ∈ Icc la ua) (hb : Y b ∈ Icc lb ub)
    (hode : ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt Y (v t (Y t)) t)
    (hfield : ∀ t ∈ Icc a b, ∀ y ∈ Icc
      (max (la - L₀ * (t-a)) (lb - L₀ * (b-t)))
      (min (ua + L₀ * (t-a)) (ub + L₀ * (b-t))), |v t y| ≤ L₁) :
    LipschitzOnWith L₁ Y (Icc a b) ∧
    ∀ t ∈ Icc a b, Y t ∈ Icc
      (max (la - L₁ * (t-a)) (lb - L₁ * (b-t)))
      (min (ua + L₁ * (t-a)) (ub + L₁ * (b-t))) := by
  have hc := certificateBootstrap_endpoint_box hab hY ha hb
  have hl := certificateBootstrap_lipschitz_of_ae_derivative hY hode
    (Filter.Eventually.of_forall (fun t ht => hfield t ht (Y t) (hc t ht)))
  exact ⟨hl, certificateBootstrap_endpoint_box hab hl ha hb⟩

/-- Uniform double-ended box, obtained by adding the two endpoint bounds. -/
theorem certificateBootstrap_uniform_box {Y : ℝ → ℝ} {a b la ua lb ub : ℝ}
    {L : ℝ≥0} (hab : a ≤ b) (hY : LipschitzOnWith L Y (Icc a b))
    (ha : Y a ∈ Icc la ua) (hb : Y b ∈ Icc lb ub) :
    ∀ t ∈ Icc a b, Y t ∈ Icc
      ((la + lb - L * (b-a))/2) ((ua + ub + L * (b-a))/2) := by
  intro t ht
  have hta := hY.dist_le_mul t ht a ⟨le_rfl, hab⟩
  have htb := hY.dist_le_mul t ht b ⟨hab, le_rfl⟩
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)] at hta
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ht.2)] at htb
  have hta' := abs_le.mp hta
  have htb' := abs_le.mp htb
  constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]

/-- AE field control on the original uniform coarse box improves the actual
solution's Lipschitz constant and its uniform box. No refined bound is assumed. -/
theorem certificateBootstrap_uniform_refine {Y : ℝ → ℝ} {v : ℝ → ℝ → ℝ}
    {a b la ua lb ub : ℝ} {L₀ L₁ : ℝ≥0}
    (hab : a ≤ b) (hY : LipschitzOnWith L₀ Y (Icc a b))
    (ha : Y a ∈ Icc la ua) (hb : Y b ∈ Icc lb ub)
    (hode : ∀ᵐ t ∂volume, t ∈ Ioo a b → HasDerivAt Y (v t (Y t)) t)
    (hfield : ∀ᵐ t ∂volume, t ∈ Icc a b → ∀ y ∈ Icc
      ((la + lb - L₀ * (b-a))/2) ((ua + ub + L₀ * (b-a))/2), |v t y| ≤ L₁) :
    LipschitzOnWith L₁ Y (Icc a b) ∧
    ∀ t ∈ Icc a b, Y t ∈ Icc
      ((la + lb - L₁ * (b-a))/2) ((ua + ub + L₁ * (b-a))/2) := by
  have hc := certificateBootstrap_uniform_box hab hY ha hb
  have hw : ∀ᵐ t ∂volume, t ∈ Icc a b → |v t (Y t)| ≤ L₁ := by
    filter_upwards [hfield] with t ht hmem
    exact ht hmem (Y t) (hc t hmem)
  have hl := certificateBootstrap_lipschitz_of_ae_derivative hY hode hw
  exact ⟨hl, certificateBootstrap_uniform_box hab hl ha hb⟩

end MarketCrash.OriginalCertificate
