import MarketCrash.FiniteRateConstruction
import MarketCrash.CrisisQuantile
import MarketCrash.OriginalResources
import MarketCrash.ResponseFamilies

noncomputable section
namespace MarketCrash
open Set

theorem severe_endpoint_crisis_lower {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (p : ι → ℝ) (F L d : ℝ) (hF : 0 < F) (hp : ∀ i, 0 < p i)
    (j : ι) (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card ι)
    (hL : d ≤ L) (htarget : ∀ i, i ≠ j → L ≤ Real.log F-Real.log (p i))
    (hcomp : p j ≤ F*Real.sqrt (Fintype.card ι))
    (hmean : (Fintype.card ι : ℝ)*d ≤
      ((Fintype.card ι : ℝ)-1)*L-Real.log (Real.sqrt (Fintype.card ι))) :
    d ≤ systemicCrisis (logPriceFromBenchmark F p) k := by
  classical
  let q := logPriceFromBenchmark F p
  have hloss (i : ι) : -q i = Real.log F-Real.log (p i) := by
    dsimp [q,logPriceFromBenchmark]
    rw [Real.log_div (hp i).ne' hF.ne']
    ring
  have hqj : q j ≤ Real.log (Real.sqrt (Fintype.card ι)) := by
    apply Real.log_le_log (div_pos (hp j) hF)
    exact (div_le_iff₀ hF).mpr (by simpa only [mul_comm] using hcomp)
  have hsum : ((Fintype.card ι : ℝ)-1)*L-Real.log (Real.sqrt (Fintype.card ι)) ≤ ∑ i,-q i := by
    have hsumT := Finset.sum_le_sum (s := Finset.univ.erase j)
      (fun i hi => (htarget i (Finset.mem_erase.mp hi).1).trans_eq (hloss i).symm)
    simp only [Finset.sum_const,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,nsmul_eq_mul] at hsumT
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    have hc : ((Fintype.card ι-1 : ℕ):ℝ) = (Fintype.card ι : ℝ)-1 := by rw [Nat.cast_sub hn,Nat.cast_one]
    rw [hc] at hsumT
    have hh := Finset.sum_erase_add Finset.univ (fun i => -q i) (Finset.mem_univ j)
    dsimp only at hh
    linarith only [hsumT,hh,hqj]
  have hm : d ≤ meanLogLoss q := by
    have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [meanLogLoss,le_div_iff₀ hn]
    have hh := hmean.trans hsum
    rw [Finset.sum_neg_distrib] at hh
    nlinarith
  have hq : d ≤ coverageQuantile q k := by
    apply (coverageQuantile_threshold_iff q k hk hkn.le d).mpr
    have hsub : Finset.univ.erase j ⊆ Finset.univ.filter (fun i => d ≤ -q i) := by
      intro i hi
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ i,hL.trans ((htarget i (Finset.mem_erase.mp hi).1).trans_eq (hloss i).symm)⟩
    have hc := Finset.card_le_card hsub
    simp only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ] at hc
    exact (Nat.le_sub_one_of_lt hkn).trans hc
  exact le_min hm hq

theorem severe_endpoint_for_small_target {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (F delta : ℝ) (hF : 0 < F) (hd : 0 < delta)
    (j : ι) (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card ι) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∀ p : ι → ℝ, (∀ i, 0 < p i) → (∀ i, i ≠ j → p i = eps) →
        p j ≤ F*Real.sqrt (Fintype.card ι) →
        delta < systemicCrisis (logPriceFromBenchmark F p) k := by
  let N : ℝ := Fintype.card ι
  let d := delta+1
  let B := |Real.log (Real.sqrt N)|
  let L := N*(d+B+1)
  have hn : 2 ≤ N := by dsimp [N]; exact_mod_cast hN
  have hd0 : 0 < d := by dsimp [d]; linarith
  have hB : 0 ≤ B := abs_nonneg _
  have hL0 : 0 < L := by dsimp [L]; positivity
  have hLd : d ≤ L := by
    dsimp [L]
    nlinarith only [mul_nonneg (by linarith : 0 ≤ N-1) hd0.le,
      mul_nonneg (by linarith : 0 ≤ N) hB,hn]
  have hmean : N*d ≤ (N-1)*L-Real.log (Real.sqrt N) := by
    have h1 : L ≤ (N-1)*L := by nlinarith only [mul_nonneg (by linarith : 0 ≤ N-2) hL0.le]
    have h2 : Real.log (Real.sqrt N) ≤ N*B := by
      exact (le_abs_self _).trans (by nlinarith only [mul_nonneg (by linarith : 0 ≤ N-1) hB])
    have h3 : N*d ≤ L-Real.log (Real.sqrt N) := by
      dsimp [L]
      nlinarith only [h2,hn]
    linarith only [h1,h3]
  refine ⟨F*Real.exp (-L),mul_pos hF (Real.exp_pos _),?_⟩
  intro eps hep hepb p hp htargets hcomp
  have htarget (i : ι) (hij : i ≠ j) : L ≤ Real.log F-Real.log (p i) := by
    have hpi : p i ≤ F*Real.exp (-L) := by rw [htargets i hij]; exact hepb.le
    have hh := Real.log_le_log (hp i) hpi
    rw [Real.log_mul hF.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
    linarith
  have hh := severe_endpoint_crisis_lower p F L d hF hp j k hk hkn hLd htarget hcomp hmean
  exact (by dsimp [d]; linarith : delta < d).trans_le hh

theorem severe_family_arbitrary_threshold {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (hN : 2 ≤ Fintype.card ι) (F rho eta : ℝ) (hF : 0 < F) (he : 0 < eta)
    (j : ι) (k : ℕ) (hk : 0 < k) (hkn : k < Fintype.card ι)
    (T eps0 M0 H0 J0 : ℝ) (heps0 : 0 < eps0)
    (hfamily : ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho)
        (fun _ => constantResponse eta he) completePairedEdges,
        P.terminal.time = T ∧ (∀ i, i ≠ j → P.terminal.prices i = eps) ∧
        P.terminal.prices j ≤ F*Real.sqrt (Fintype.card ι) ∧
        P.trace.pairedTurnover ≤ M0 ∧ (∀ i, P.trace.shareSales i ≤ H0) ∧
        (∀ i, P.initial.shares i ≤ J0)) :
    ∀ delta : ℝ, 0 < delta →
      ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho)
        (fun _ => constantResponse eta he) completePairedEdges,
        P.terminal.time = T ∧ P.trace.pairedTurnover ≤ M0 ∧
        (∀ i, P.trace.shareSales i ≤ H0) ∧ (∀ i, P.initial.shares i ≤ J0) ∧
        delta < systemicCrisis (logPriceFromBenchmark F P.terminal.prices) k := by
  intro delta hd
  obtain ⟨eps1,heps1,hcrisis⟩ := severe_endpoint_for_small_target hN F delta hF hd j k hk hkn
  let eps := min eps0 eps1/2
  have hep : 0 < eps := half_pos (lt_min heps0 heps1)
  have hep0 : eps < eps0 := (half_lt_self (lt_min heps0 heps1)).trans_le (min_le_left _ _)
  have hep1 : eps < eps1 := (half_lt_self (lt_min heps0 heps1)).trans_le (min_le_right _ _)
  obtain ⟨P,hPT,hprices,hcomp,hM,hH,hJ⟩ := hfamily eps hep hep0
  have hp : ∀ i, 0 < P.terminal.prices i := P.trace.endpoint_positive (fun i => by rw [P.initial_prices i]; exact hF)
  exact ⟨P,hPT,hM,hH,hJ,hcrisis eps hep hep1 P.terminal.prices hp hprices hcomp⟩

end MarketCrash
