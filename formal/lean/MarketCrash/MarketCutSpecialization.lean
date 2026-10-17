import MarketCrash.ResponseFamilies

noncomputable section
namespace MarketCrash

/-- Finite-horizon version: no assumptions on future reference closes. -/
theorem rolling_upper_reference_bound_finite (F β : ℝ) (hβ : 0 ≤ β)
    (reference : ℕ → ℝ) (hzero : reference 0 ≤ F) (D : ℕ)
    (hstep : ∀ n < D, reference (n + 1) ≤ (1 + β) * reference n) :
    reference D ≤ F * (1 + β) ^ D := by
  have hh : ∀ n ≤ D, reference n ≤ F * (1 + β) ^ n := by
    intro n
    induction n with
    | zero => intro _; simpa using hzero
    | succ n ih =>
      intro hn
      calc
        reference (n + 1) ≤ (1 + β) * reference n := hstep n (by omega)
        _ ≤ (1 + β) * (F * (1 + β) ^ n) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (by linarith)
        _ = _ := by rw [pow_succ]; ring
  exact hh D le_rfl

/-- Repeated upper bands bound the actual sequence of reference closes. -/
theorem rolling_upper_reference_bound (F β : ℝ) (hβ : 0 ≤ β)
    (reference : ℕ → ℝ) (hzero : reference 0 ≤ F)
    (hstep : ∀ d, reference (d + 1) ≤ (1 + β) * reference d) :
    ∀ d, reference d ≤ F * (1 + β) ^ d := by
  intro d
  induction d with
  | zero => simpa using hzero
  | succ d ih =>
    calc
      reference (d + 1) ≤ (1 + β) * reference d := hstep d
      _ ≤ (1 + β) * (F * (1 + β) ^ d) := mul_le_mul_of_nonneg_left ih (by linarith)
      _ = F * (1 + β) ^ (d + 1) := by rw [pow_succ]; ring

/-- A session's pointwise upper band inherits the rolling reference bound. -/
theorem rolling_upper_session_bound (F β : ℝ) (hβ : 0 ≤ β)
    (reference : ℕ → ℝ) (hzero : reference 0 ≤ F)
    (hstep : ∀ d, reference (d + 1) ≤ (1 + β) * reference d)
    (d : ℕ) (S : ℝ) (hS : S ≤ (1 + β) * reference d) :
    S ≤ F * (1 + β) ^ (d + 1) := by
  calc
    S ≤ (1 + β) * reference d := hS
    _ ≤ (1 + β) * (F * (1 + β) ^ d) :=
      mul_le_mul_of_nonneg_left (rolling_upper_reference_bound F β hβ reference hzero hstep d)
        (by linarith)
    _ = F * (1 + β) ^ (d + 1) := by rw [pow_succ]; ring

theorem constant_coordinate_session_difference (F η q : ℝ) (hF : 0 < F)
    (hη : 0 < η) (hq : 0 < q) (d : ℕ) :
    coordinate F (fun _ => η) (F * q ^ (d - 1)) -
      coordinate F (fun _ => η) (F * q ^ d) =
        ((F * q ^ (d - 1)) ^ 2 - (F * q ^ d) ^ 2) / (2 * η) := by
  rw [← constantCoordinate_eq_integral F η hF hη (mul_pos hF (pow_pos hq _)),
    ← constantCoordinate_eq_integral F η hF hη (mul_pos hF (pow_pos hq _))]
  dsimp [constantCoordinate]
  ring

/-- The manuscript's k/m rate specialization, using the physical cut's K and capacity. -/
theorem market_cut_constant_impact_specialization
    (k m : ℕ) (F η τ β q K v : ℝ) (d : ℕ)
    (hm : 0 < m) (hF : 0 < F) (hη : 0 < η) (hτ : 0 < τ)
    (hβ : 0 ≤ β) (hq : 0 < q) (_hd : 2 ≤ d)
    (hK : K = k * (coordinate F (fun _ => η) (F * q ^ (d - 1)) -
      coordinate F (fun _ => η) (F * q ^ d)))
    (hrate : K / (τ * (m * F * (1 + β) ^ d)) ≤ v) :
    (k : ℝ) / m * F * (q ^ (2 * (d - 1)) - q ^ (2 * d)) /
      (2 * η * τ * (1 + β) ^ d) ≤ v := by
  rw [hK, constant_coordinate_session_difference F η q hF hη hq d] at hrate
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hb : (1 + β) ^ d ≠ 0 := pow_ne_zero _ (by linarith)
  have heq :
      (k : ℝ) / m * F * (q ^ (2 * (d - 1)) - q ^ (2 * d)) /
        (2 * η * τ * (1 + β) ^ d) =
      (k * (((F * q ^ (d - 1)) ^ 2 - (F * q ^ d) ^ 2) / (2 * η))) /
        (τ * (m * F * (1 + β) ^ d)) := by
    simp only [pow_mul, mul_pow]
    field_simp
    <;> ring
  rw [heq]
  exact hrate

end MarketCrash
