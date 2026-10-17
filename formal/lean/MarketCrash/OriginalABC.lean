import MarketCrash.OriginalABRegimes
import MarketCrash.SevereAssembly
import MarketCrash.SevereCrisis

noncomputable section
namespace MarketCrash
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

def OriginalABCBarrier (F rho eta : ℝ) (hF : 0 < F) (he : 0 < eta) : Prop :=
  ∀ (κ : Type) [Fintype κ] (edges : κ → PairedEdge ι)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho)
      (fun _ => quadraticResponse F eta hF he) edges),
    ∀ o, P.trace.Observes o → ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
      systemicCrisis (logPriceFromBenchmark F o.prices) (requiredAssetCount (ι := ι) alpha) ≤ 0

def OriginalABCInventory (F rho eta alpha : ℝ) (hF : 0 < F) (he : 0 < eta) : Prop :=
  (∀ T : ℝ, 0 < T → ∀ zeta : ℝ, 0 < zeta →
    ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho)
      (fun _ => linearResponse F eta hF he) completePairedEdges,
      P.terminal.time = T ∧
      0 < systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) alpha) ∧
      systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) alpha) < zeta) ∧
  ∀ (κ : Type) [Fintype κ] (edges : κ → PairedEdge ι) (H0 : ℝ)
    (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho)
      (fun _ => linearResponse F eta hF he) edges),
      (∀ i, P.initial.shares i ≤ H0) →
      systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (requiredAssetCount (ι := ι) alpha) ≤ 1+eta*H0/F

def OriginalABCSevere (F rho eta : ℝ) (he : 0 < eta) : Prop :=
  ∃ T M0 H0 : ℝ, 0 < T ∧ 0 ≤ M0 ∧ 0 < H0 ∧
    ∀ k : ℕ, 0 < k → k < Fintype.card ι → ∀ delta : ℝ, 0 < delta →
      ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho)
        (fun _ => constantResponse eta he) completePairedEdges,
        P.terminal.time = T ∧ P.trace.pairedTurnover ≤ M0 ∧
        (∀ i, P.trace.shareSales i ≤ H0) ∧ (∀ i, P.initial.shares i ≤ H0) ∧
        delta < systemicCrisis (logPriceFromBenchmark F P.terminal.prices) k

theorem theorem_4_1_C_original (hN : 2 ≤ Fintype.card ι)
    (F rho eta : ℝ) (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta) :
    OriginalABCSevere (ι := ι) F rho eta he := by
  classical
  let comp : ι := Classical.arbitrary ι
  obtain ⟨T,eps0,M0,H0,J0,hT,heps0,hM,hH,hJ,hfamily⟩ :=
    severeAssembly_uniform_original_family comp F rho eta hF hr he hN
  let H := 1+max H0 J0
  have hHpos : 0 < H := by dsimp [H]; linarith [le_max_left H0 J0]
  refine ⟨T,M0,H,hT,hM,hHpos,?_⟩
  intro k hk hkn delta hd
  obtain ⟨P,hPT,hPM,hPH,hPJ,hcrisis⟩ := severe_family_arbitrary_threshold hN F rho eta hF he
    comp k hk hkn T eps0 M0 H0 J0 heps0 hfamily delta hd
  refine ⟨P,hPT,hPM,?_,?_,hcrisis⟩
  · intro i
    exact (hPH i).trans (by dsimp [H]; linarith [le_max_left H0 J0])
  · intro i
    exact (hPJ i).trans (by dsimp [H]; linarith [le_max_right H0 J0])

/-! Original Theorem 4.1 (paper/main.tex, thm:ABC):
Let N >= 2 and k=ceil(alpha*N)<N. Compare the three power-response
markets under the same model protocol.
(A) p=2: C_alpha(t)<=0 for every admissible path and every horizon.
(B) p=1: positive but sufficiently small terminal systemic drawdowns are
reachable. With a fixed finite per-asset starting inventory cap and no
short selling, terminal crisis severity is bounded independently of the
trade sequence.
(C) p=0: for every fixed N>=2,k<N there exist a sufficiently long finite
T and finite M0,H0 such that every finite delta>0 has an admissible
positive-price, terminally dollar-closed path at T with M<=M0,
H_i^-<=H0 and C_alpha(T)>delta. The constants do not depend on delta.
The severe branch below chooses the same constants even before k and also
bounds actual initial holdings by H0. No uniformity in changing N is claimed.
-/
theorem theorem_4_1_original (hN : 2 ≤ Fintype.card ι)
    (F rho eta alpha : ℝ) (hF : 0 < F) (hr : 0 < rho) (he : 0 < eta)
    (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hk : requiredAssetCount (ι := ι) alpha < Fintype.card ι) :
    OriginalABCBarrier (ι := ι) F rho eta hF he ∧
    OriginalABCInventory (ι := ι) F rho eta alpha hF he ∧
    OriginalABCSevere (ι := ι) F rho eta he := by
  refine ⟨?_,⟨?_,?_⟩,theorem_4_1_C_original hN F rho eta hF hr he⟩
  · intro κ inst edges P o ho a ha' ha1'
    exact theorem_4_1_A_original F rho eta hF hr.le he hN P o ho a ha' ha1'
  · intro T hT zeta hzeta
    exact theorem_4_1_B_small_positive hN F rho eta T hF hr he hT alpha ha ha1 hk zeta hzeta
  · intro κ inst edges H0 P hH
    exact theorem_4_1_B_inventory_bound F rho eta hF he H0 P hH alpha

end MarketCrash
