import MarketCrash.CrisisParameters
import Mathlib.Data.Finset.Max

/-!
A finite-sample order-statistic proof for the paper's coverage quantile.

For 1 ≤ k ≤ N, the sSup-based definition is equal to one of the
observed log losses. It has the exact kth-largest threshold semantics:
at least k losses exceed threshold x iff x ≤ Q_k.

No regularity or model-path assumption is needed for this finite
combinatorial result; the result applies to real log losses from any
positive-price endpoint once linked by CrisisParameters.lean.
-/
noncomputable section
namespace MarketCrash

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The sample loss of asset i is an admissible kth-largest cutoff if
    at least k assets have loss at least that loss. -/
def candidateCutoffs (q : ι → ℝ) (k : ℕ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i : ι =>
    k ≤ (Finset.univ.filter (fun j : ι => -q i ≤ -q j)).card)

/-- Every threshold attained by k assets is bounded by one of the
    ACTUALLY OBSERVED sample-loss candidate cutoffs. -/
theorem coverage_threshold_below_candidate
    (q : ι → ℝ) (k : ℕ) (hk : 0 < k) (x : ℝ)
    (hx : k ≤ (Finset.univ.filter (fun i : ι => x ≤ -q i)).card) :
    ∃ i ∈ candidateCutoffs q k, x ≤ -q i := by
  classical
  let eligible : Finset ι :=
    Finset.univ.filter (fun i : ι => x ≤ -q i)
  have he : eligible.Nonempty := by
    apply Finset.card_pos.mp
    exact lt_of_lt_of_le hk hx
  obtain ⟨i, hi, hmin⟩ :=
    Finset.exists_min_image eligible (fun i => -q i) he
  have hxi : x ≤ -q i := (Finset.mem_filter.mp hi).2
  have hsubset : eligible ⊆
      Finset.univ.filter (fun j : ι => -q i ≤ -q j) := by
    intro j hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hmin j hj⟩
  have hcandidate : k ≤
      (Finset.univ.filter (fun j : ι => -q i ≤ -q j)).card :=
    hx.trans (Finset.card_le_card hsubset)
  exact ⟨i, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hcandidate⟩, hxi⟩

/-- For a valid coverage count there exists a finite-sample cutoff.
    The asset with the smallest log loss is always a candidate. -/
theorem coverage_candidates_nonempty
    (q : ι → ℝ) (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (candidateCutoffs q k).Nonempty := by
  classical
  obtain ⟨i, _, hmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι)
      (fun i : ι => -q i) Finset.univ_nonempty
  have hfull :
      (Finset.univ.filter (fun j : ι => -q i ≤ -q j)) =
        (Finset.univ : Finset ι) := by
    apply Finset.filter_eq_self.mpr
    intro j hj
    exact hmin j hj
  refine ⟨i, ?_⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simpa only [hfull, Finset.card_univ] using hk

/-- There is an observed sample loss that is the *greatest* admissible
    kth-largest cutoff, and coverageQuantile equals that loss exactly. -/
theorem coverageQuantile_eq_max_candidate
    (q : ι → ℝ) (k : ℕ)
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    ∃ i ∈ candidateCutoffs q k,
      coverageQuantile q k = -q i ∧
      ∀ j ∈ candidateCutoffs q k, -q j ≤ -q i := by
  classical
  obtain ⟨i, hi, hmax⟩ :=
    Finset.exists_max_image (candidateCutoffs q k)
      (fun i : ι => -q i) (coverage_candidates_nonempty q k hkn)
  have hset :
      {x : ℝ | k ≤
        (Finset.univ.filter (fun j : ι => x ≤ -q j)).card} =
        Set.Iic (-q i) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨j, hj, hxj⟩ :=
        coverage_threshold_below_candidate q k hk x hx
      exact hxj.trans (hmax j hj)
    · intro hxi
      have hcand :
          k ≤ (Finset.univ.filter
            (fun j : ι => -q i ≤ -q j)).card :=
        (Finset.mem_filter.mp hi).2
      have hsub :
          (Finset.univ.filter (fun j : ι => -q i ≤ -q j)) ⊆
            (Finset.univ.filter (fun j : ι => x ≤ -q j)) := by
        intro j hj
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hxi.trans (Finset.mem_filter.mp hj).2⟩
      exact hcand.trans (Finset.card_le_card hsub)
  refine ⟨i, hi, ?_, hmax⟩
  unfold coverageQuantile
  rw [hset]
  exact csSup_Iic

/-- Exact order-statistic threshold semantics, independent of tie-breaking:
    at least k losses reach x iff x does not exceed the kth-largest loss. -/
theorem coverageQuantile_threshold_iff
    (q : ι → ℝ) (k : ℕ)
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) (x : ℝ) :
    x ≤ coverageQuantile q k ↔
      k ≤ (Finset.univ.filter (fun i : ι => x ≤ -q i)).card := by
  classical
  obtain ⟨i, hi, heq, hmax⟩ :=
    coverageQuantile_eq_max_candidate q k hk hkn
  rw [heq]
  constructor
  · intro hxi
    have hcand : k ≤
        (Finset.univ.filter (fun j : ι => -q i ≤ -q j)).card :=
      (Finset.mem_filter.mp hi).2
    have hsub :
        (Finset.univ.filter (fun j : ι => -q i ≤ -q j)) ⊆
          (Finset.univ.filter (fun j : ι => x ≤ -q j)) := by
      intro j hj
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hxi.trans (Finset.mem_filter.mp hj).2⟩
    exact hcand.trans (Finset.card_le_card hsub)
  · intro hx
    obtain ⟨j, hj, hxj⟩ :=
      coverage_threshold_below_candidate q k hk x hx
    exact hxj.trans (hmax j hj)

/-- A coverage quantile really is the observed kth-largest sample loss,
with the sharp strict-threshold count bound above that value. -/
theorem coverageQuantile_is_kth_largest
    (q : ι → ℝ) (k : ℕ)
    (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    (∃ i : ι, coverageQuantile q k = -q i) ∧
      k ≤ (Finset.univ.filter
        (fun i : ι => coverageQuantile q k ≤ -q i)).card ∧
      ∀ x : ℝ, coverageQuantile q k < x →
        (Finset.univ.filter (fun i : ι => x ≤ -q i)).card < k := by
  obtain ⟨i, _, hi, _⟩ :=
    coverageQuantile_eq_max_candidate q k hk hkn
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · exact (coverageQuantile_threshold_iff q k hk hkn _).mp le_rfl
  · intro x hx
    have hnot : ¬ k ≤
        (Finset.univ.filter (fun i : ι => x ≤ -q i)).card := by
      intro h
      have hle := (coverageQuantile_threshold_iff q k hk hkn x).mpr h
      exact (not_le_of_gt hx) hle
    omega

end MarketCrash
