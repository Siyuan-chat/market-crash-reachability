import MarketCrash.Coordinates

noncomputable section
namespace MarketCrash

def constantCoordinate (F η S : ℝ) : ℝ := (S ^ 2 - F ^ 2) / (2 * η)
def linearCoordinate (F η S : ℝ) : ℝ := F * (S - F) / η
def logarithmicCoordinate (F η S : ℝ) : ℝ := F ^ 2 / η * Real.log (S / F)

def constantResponse (η : ℝ) (hη : 0 < η) : Response where
  impact := fun _ => η
  continuousOn_positive := continuousOn_const
  positive := fun _ _ => hη

def linearResponse (F η : ℝ) (hF : 0 < F) (hη : 0 < η) : Response where
  impact := fun S => η * (S / F)
  continuousOn_positive := continuousOn_const.mul (continuousOn_id.div_const F)
  positive := fun S hS => mul_pos hη (div_pos hS hF)

def quadraticResponse (F η : ℝ) (hF : 0 < F) (hη : 0 < η) : Response where
  impact := fun S => η * (S / F) ^ 2
  continuousOn_positive := continuousOn_const.mul ((continuousOn_id.div_const F).pow 2)
  positive := fun S hS => mul_pos hη (pow_pos (div_pos hS hF) 2)

theorem constantCoordinate_normalized (F η : ℝ) : constantCoordinate F η F = 0 := by
  simp [constantCoordinate]

theorem linearCoordinate_normalized (F η : ℝ) : linearCoordinate F η F = 0 := by
  simp [linearCoordinate]

theorem logarithmicCoordinate_normalized (F η : ℝ) (hF : 0 < F) :
    logarithmicCoordinate F η F = 0 := by
  simp [logarithmicCoordinate, ne_of_gt hF]

theorem constantCoordinate_hasDerivAt (F η S : ℝ) (hη : 0 < η) :
    HasDerivAt (constantCoordinate F η) (S / η) S := by
  convert (((hasDerivAt_id S).pow 2).sub_const (F ^ 2)).div_const (2 * η) using 1 <;>
    simp [constantCoordinate] <;> field_simp <;> ring

theorem linearCoordinate_hasDerivAt (F η S : ℝ) :
    HasDerivAt (linearCoordinate F η) (F / η) S := by
  convert (((hasDerivAt_id S).sub_const F).const_mul F).div_const η using 1 <;>
    simp [linearCoordinate]

theorem logarithmicCoordinate_hasDerivAt (F η S : ℝ) (hF : 0 < F)
    (hη : 0 < η) (hS : 0 < S) :
    HasDerivAt (logarithmicCoordinate F η) (F ^ 2 / (η * S)) S := by
  convert (((hasDerivAt_id S).div_const F).log (div_ne_zero hS.ne' hF.ne')).const_mul
    (F ^ 2 / η) using 1 <;>
    simp [logarithmicCoordinate] <;> field_simp <;> ring

theorem constantCoordinate_eq_integral (F η : ℝ) (hF : 0 < F) (hη : 0 < η) :
    Set.EqOn (constantCoordinate F η) (coordinate F (fun _ => η)) positivePrices := by
  apply coordinate_unique F (constantResponse η hη) hF
    (constantCoordinate F η)
    (fun S _ => (constantCoordinate_hasDerivAt F η S hη).differentiableAt)
    (constantCoordinate_normalized F η)
  intro S _
  rw [(constantCoordinate_hasDerivAt F η S hη).deriv]
  exact div_mul_cancel₀ S hη.ne'

theorem linearCoordinate_eq_integral (F η : ℝ) (hF : 0 < F) (hη : 0 < η) :
    Set.EqOn (linearCoordinate F η) (coordinate F (fun S => η * (S / F))) positivePrices := by
  apply coordinate_unique F (linearResponse F η hF hη) hF
    (linearCoordinate F η)
    (fun S _ => (linearCoordinate_hasDerivAt F η S).differentiableAt)
    (linearCoordinate_normalized F η)
  intro S _
  rw [(linearCoordinate_hasDerivAt F η S).deriv]
  change F / η * (η * (S / F)) = S
  field_simp [hF.ne', hη.ne']
  <;> ring

theorem logarithmicCoordinate_eq_integral (F η : ℝ) (hF : 0 < F) (hη : 0 < η) :
    Set.EqOn (logarithmicCoordinate F η)
      (coordinate F (fun S => η * (S / F) ^ 2)) positivePrices := by
  apply coordinate_unique F (quadraticResponse F η hF hη) hF
    (logarithmicCoordinate F η)
    (fun S hS => (logarithmicCoordinate_hasDerivAt F η S hF hη hS).differentiableAt)
    (logarithmicCoordinate_normalized F η hF)
  intro S hS
  rw [(logarithmicCoordinate_hasDerivAt F η S hF hη hS).deriv]
  change F ^ 2 / (η * S) * (η * (S / F) ^ 2) = S
  field_simp [hF.ne', hη.ne', (show S ≠ 0 from ne_of_gt hS)]
  <;> ring

theorem constantCoordinate_lower_bound (F η S : ℝ) (hη : 0 < η) (hS : 0 < S) :
    -(F ^ 2) / (2 * η) < constantCoordinate F η S := by
  have hp : 0 < S ^ 2 / (2 * η) := div_pos (sq_pos_of_pos hS) (by positivity)
  dsimp [constantCoordinate]
  rw [sub_div, neg_div]
  linarith

theorem constantCoordinate_range (F η y : ℝ) (hη : 0 < η)
    (hy : -(F ^ 2) / (2 * η) < y) :
    ∃ S > 0, constantCoordinate F η S = y := by
  have hy' := (div_lt_iff₀ (show 0 < 2 * η by positivity)).mp hy
  have hr : 0 < F ^ 2 + 2 * η * y := by nlinarith
  refine ⟨Real.sqrt (F ^ 2 + 2 * η * y), Real.sqrt_pos.2 hr, ?_⟩
  dsimp [constantCoordinate]
  rw [Real.sq_sqrt hr.le]
  field_simp [hη.ne']
  <;> ring

theorem constantCoordinate_image (F η : ℝ) (hη : 0 < η) :
    constantCoordinate F η '' positivePrices = Set.Ioi (-(F ^ 2) / (2 * η)) := by
  ext y
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact constantCoordinate_lower_bound F η S hη hS
  · intro hy
    rcases constantCoordinate_range F η y hη hy with ⟨S, hS, heq⟩
    exact ⟨S, hS, heq⟩

theorem linearCoordinate_lower_bound (F η S : ℝ) (hF : 0 < F)
    (hη : 0 < η) (hS : 0 < S) :
    -(F ^ 2) / η < linearCoordinate F η S := by
  have hp : 0 < F * S / η := div_pos (mul_pos hF hS) hη
  dsimp [linearCoordinate]
  rw [mul_sub, sub_div, ← pow_two, neg_div]
  linarith

theorem linearCoordinate_range (F η y : ℝ) (hF : 0 < F) (hη : 0 < η)
    (hy : -(F ^ 2) / η < y) : ∃ S > 0, linearCoordinate F η S = y := by
  have hy' := (div_lt_iff₀ hη).mp hy
  have hr : 0 < F ^ 2 + η * y := by nlinarith
  refine ⟨(F ^ 2 + η * y) / F, div_pos hr hF, ?_⟩
  dsimp [linearCoordinate]
  field_simp [hF.ne', hη.ne']
  <;> ring

theorem linearCoordinate_image (F η : ℝ) (hF : 0 < F) (hη : 0 < η) :
    linearCoordinate F η '' positivePrices = Set.Ioi (-(F ^ 2) / η) := by
  ext y
  constructor
  · rintro ⟨S, hS, rfl⟩
    exact linearCoordinate_lower_bound F η S hF hη hS
  · intro hy
    rcases linearCoordinate_range F η y hF hη hy with ⟨S, hS, heq⟩
    exact ⟨S, hS, heq⟩

theorem logarithmicCoordinate_range (F η y : ℝ) (hF : 0 < F) (hη : 0 < η) :
    ∃ S > 0, logarithmicCoordinate F η S = y := by
  refine ⟨F * Real.exp (η * y / F ^ 2), mul_pos hF (Real.exp_pos _), ?_⟩
  dsimp [logarithmicCoordinate]
  rw [mul_div_cancel_left₀ _ hF.ne', Real.log_exp]
  field_simp [hF.ne', hη.ne']
  <;> ring

theorem logarithmicCoordinate_image (F η : ℝ) (hF : 0 < F) (hη : 0 < η) :
    logarithmicCoordinate F η '' positivePrices = Set.univ := by
  ext y
  simp only [Set.mem_univ, iff_true]
  rcases logarithmicCoordinate_range F η y hF hη with ⟨S, hS, heq⟩
  exact ⟨S, hS, heq⟩

end MarketCrash
