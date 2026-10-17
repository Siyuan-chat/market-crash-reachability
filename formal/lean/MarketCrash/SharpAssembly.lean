import MarketCrash.SharpTraceConstruction
import MarketCrash.SharpRadialPiece
import MarketCrash.SharpRadialBarrier
import MarketCrash.OriginalResources

noncomputable section
namespace MarketCrash
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def SharpPrefix (F ρ η : ℝ) (hη : 0 < η) (τ : ℝ) (Q I : ι → ℝ) : Prop :=
  ∃ (s t : PhysicalMarketState ι)
    (path : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη)
      completePairedEdges s t),
    s.time = 0 ∧ s.prices = (fun _ => F) ∧ (∀ i, 0 ≤ s.shares i) ∧ s.dollars = 0 ∧
    t.time = τ ∧ t.prices = Q ∧ ∀ i, path.recoveryIntegral i = I i

theorem sharpPrefix_zero (F ρ η : ℝ) (hη : 0 < η) :
    SharpPrefix (ι := ι) F ρ η hη 0 (fun _ => F) 0 := by
  let s : PhysicalMarketState ι := ⟨0,fun _ => F,0,0⟩
  exact ⟨s,s,.refl s,rfl,rfl,fun _ => le_rfl,rfl,rfl,rfl,fun _ => rfl⟩

theorem sharpPrefix_append (F ρ η : ℝ) (hη : 0 < η) (τ σ : ℝ) (Q Q' I J : ι → ℝ)
    (hp : SharpPrefix F ρ η hη τ Q I) {u v : PhysicalMarketState ι}
    (arc : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη)
      completePairedEdges u v)
    (hut : u.time = τ) (hup : u.prices = Q) (hvt : v.time = σ) (hvp : v.prices = Q')
    (hrec : ∀ i, arc.recoveryIntegral i = J i) :
    SharpPrefix F ρ η hη σ Q' (fun i => I i+J i) := by
  obtain ⟨s,t,path,hs0,hsP,hsH,hsL,htT,htP,hI⟩ := hp
  obtain ⟨H1,H2,L,hH1,hH2,joined,hjoin⟩ := concatenate_with_finite_inventory path arc
    (htT.trans hut.symm) (htP.trans hup.symm)
  refine ⟨physicalEconomicOffset s H1 0,physicalEconomicOffset v H2 L,joined,
    hs0,hsP,?_,?_,hvt,hvp,?_⟩
  · intro i
    exact add_nonneg (hH1 i) (hsH i)
  · change (fun i => 0+s.dollars i) = 0
    simp [hsL]
    rfl
  · intro i
    rw [hjoin,hI,hrec]

theorem sharpPrefix_transport (hub : ι) (F ρ η τ : ℝ) (hF : 0 < F) (hη : 0 < η)
    (P Q I : ι → ℝ) (hP : ∀ i, 0 < P i) (hQ : ∀ i, 0 < Q i)
    (hsq : ∑ i,(P i)^2 = ∑ i,(Q i)^2) (hp : SharpPrefix F ρ η hη τ P I) :
    SharpPrefix F ρ η hη τ Q I := by
  let x := fun i => (P i)^2/(2*η)
  let y := fun i => (Q i)^2/(2*η)
  have hx (i : ι) : 0 < x i := div_pos (sq_pos_of_pos (hP i)) (by positivity)
  have hy (i : ι) : 0 < y i := div_pos (sq_pos_of_pos (hQ i)) (by positivity)
  have hxy : ∑ i,x i = ∑ i,y i := by dsimp [x,y];rw [←Finset.sum_div,←Finset.sum_div,hsq]
  obtain ⟨arc⟩ := positive_square_transport_reachable hub τ F η hF hη (fun _ => ρ) 0 0 x y
    (fun _ => le_rfl) hx hy hxy
  have hsx (i : ι) : Real.sqrt (2*η*x i) = P i := by
    have he : 2*η*x i = (P i)^2 := by dsimp [x];field_simp
    rw [he,Real.sqrt_sq (hP i).le]
  have hsy (i : ι) : Real.sqrt (2*η*y i) = Q i := by
    have he : 2*η*y i = (Q i)^2 := by dsimp [y];field_simp
    rw [he,Real.sqrt_sq (hQ i).le]
  have hh := sharpPrefix_append F ρ η hη τ τ P Q I 0 hp arc rfl (funext hsx) rfl (funext hsy)
    (arc.recovery_zero_of_equal_time rfl)
  simpa only [Pi.zero_apply,add_zero] using hh

theorem sharp_isotropic_square_sum (R : ℝ) (hN : 0 < Fintype.card ι) :
    (∑ _ : ι,(R/Real.sqrt (Fintype.card ι))^2) = R^2 := by
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast hN
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,div_pow,Real.sq_sqrt hn.le]
  field_simp

theorem sharpPrefix_continuous_piece (F ρ η : ℝ) (hη : 0 < η)
    (m : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)))
    (hF : m.F = fun _ => F) (hρ : m.rho = fun _ => ρ) (hg : m.response = fun _ => constantResponse η hη)
    (hBV : ∀ i, BoundedVariationOn (m.shares · i) (Icc m.a m.b))
    (I : ι → ℝ) (hp : SharpPrefix F ρ η hη m.a (m.prices m.a) I) :
    SharpPrefix F ρ η hη m.b (m.prices m.b) (fun i => I i+
      ∫ u in m.a..m.b,m.prices u i*(m.prices u i-F)/η) := by
  let step := OriginalPhysicalStep.continuous m hF hρ hg hBV
  let arc := OriginalPhysicalReachable.append (.refl _) step
  apply sharpPrefix_append F ρ η hη m.a m.b _ _ I _ hp arc rfl rfl rfl rfl
  intro i
  simp [arc,step,OriginalPhysicalReachable.recoveryIntegral,OriginalPhysicalStep.recoveryIntegral,constantResponse]

theorem sharpPrefix_one_direction (hub : ι) (F ρ η b T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hb : 0 < b) (hnb : (Fintype.card ι : ℝ)*b^2 < 1) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i,0 < u i) (hun : ∑ i,(u i)^2 = 1)
    (huH : ∑ i,u i = sharpDirectionSum (Fintype.card ι) b)
    (a c : ℝ) (ha : a ∈ Icc 0 T) (hc : c ∈ Icc 0 T) (hac : a ≤ c)
    (I : ι → ℝ)
    (hp : SharpPrefix F ρ η hη a (fun _ => sharpRadius F ρ (Fintype.card ι) b a/Real.sqrt (Fintype.card ι)) I) :
    SharpPrefix F ρ η hη c (fun _ => sharpRadius F ρ (Fintype.card ι) b c/Real.sqrt (Fintype.card ι))
      (fun i => I i+∫ t in a..c,(u i*sharpRadius F ρ (Fintype.card ι) b t)*
        (u i*sharpRadius F ρ (Fintype.card ι) b t-F)/η) := by
  have hn : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  let R := sharpRadius F ρ (Fintype.card ι) b
  have hroot : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hRP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < R t := by
    obtain ⟨_,_,_,hH,_⟩ := sharp_direction_geometry (Fintype.card ι) b hn hb hnb
    exact (mul_pos hF (by linarith)).trans_le
      (sharpRadius_bounds F ρ (Fintype.card ι) b t hF hρ.le hn hb hnb ht.1).1
  obtain ⟨m,hma,hmb,hmF,hmρ,hmg,hmS,hmL,hmBV⟩ :=
    sharp_radial_physical_piece hub F ρ η (Fintype.card ι) b T hF hρ hη hn hb hnb hT u hu hun huH
  have hunit (t : ℝ) : ∑ i,(u i*R t)^2 = (R t)^2 := by
    simp_rw [mul_pow]
    rw [←Finset.sum_mul,hun,one_mul]
  have hmaP (i : ι) : 0 < m.prices a i := by rw [hmS];exact mul_pos (hu i) (hRP a ha)
  have hmcP (i : ι) : 0 < m.prices c i := by rw [hmS];exact mul_pos (hu i) (hRP c hc)
  have hstart := sharpPrefix_transport hub F ρ η a hF hη _ (m.prices a) I
    (fun _ => div_pos (hRP a ha) hroot) hmaP
    (by rw [hmS,sharp_isotropic_square_sum _ (by omega),hunit]) hp
  let q := restrictPhysicalPiece m a c (by rw [hma];exact ha.1) (by rw [hmb];exact hc.2) hac
  have hqBV (i : ι) : BoundedVariationOn (q.shares · i) (Icc q.a q.b) := by
    exact (hmBV i).mono (fun t ht => ⟨ha.1.trans ht.1,ht.2.trans hc.2⟩)
  have hmid := sharpPrefix_continuous_piece F ρ η hη q hmF hmρ hmg hqBV I hstart
  have hend := sharpPrefix_transport hub F ρ η c hF hη (m.prices c) _ _ hmcP
    (fun _ => div_pos (hRP c hc) hroot)
    (by rw [hmS,sharp_isotropic_square_sum _ (by omega),hunit]) hmid
  simpa only [q,restrictPhysicalPiece,hmS] using hend

theorem sharpPrefix_sequence (F ρ η : ℝ) (hη : 0 < η) (N : ℕ)
    (τ : ℕ → ℝ) (Q : ℕ → ι → ℝ) (J : ℕ → ι → ℝ)
    (hτ : τ 0 = 0) (hQ : Q 0 = fun _ => F)
    (hstep : ∀ k < N, ∀ I : ι → ℝ, SharpPrefix F ρ η hη (τ k) (Q k) I →
      SharpPrefix F ρ η hη (τ (k+1)) (Q (k+1)) (fun i => I i+J k i)) :
    SharpPrefix F ρ η hη (τ N) (Q N) (fun i => ∑ k ∈ Finset.range N,J k i) := by
  have hall : ∀ k ≤ N, SharpPrefix F ρ η hη (τ k) (Q k) (fun i => ∑ j ∈ Finset.range k,J j i) := by
    intro k
    induction k with
    | zero => intro _;simpa only [hτ,hQ,Finset.range_zero,Finset.sum_empty] using sharpPrefix_zero (ι := ι) F ρ η hη
    | succ k ih =>
      intro hk
      have hh := hstep k (by omega) _ (ih (by omega))
      simpa only [Finset.sum_range_succ] using hh
  exact hall N le_rfl

theorem sharp_direction_interval_recovery (F η a b : ℝ) (R : ℝ → ℝ) (j i : ι) (s t W : ℝ)
    (hR : Continuous R) (hW : (∫ u in s..t,(a-b)*R u*((a+b)*R u-F)) = W) :
    (∫ u in s..t,(sharpDirection a b j i*R u)*(sharpDirection a b j i*R u-F)/η) =
      (∫ u in s..t,(b*R u)*(b*R u-F))/η+(if i = j then W/η else 0) := by
  have hB : IntervalIntegrable (fun u => (b*R u)*(b*R u-F)) volume s t := (show Continuous (fun u => (b*R u)*(b*R u-F)) by fun_prop).intervalIntegrable s t
  have hI : IntervalIntegrable (fun u => (a-b)*R u*((a+b)*R u-F)) volume s t :=
    (show Continuous (fun u => (a-b)*R u*((a+b)*R u-F)) by fun_prop).intervalIntegrable s t
  rw [intervalIntegral.integral_div]
  simp_rw [sharp_recovery_density_split]
  by_cases hij : i = j
  · simp only [if_pos hij]
    rw [intervalIntegral.integral_add hB hI,hW,add_div]
  · simp only [if_neg hij,add_zero]

set_option maxHeartbeats 800000 in
theorem sharp_symmetric_recovery_prefix (hub : ι) (F ρ η b T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hb : 0 < b) (hnb : (Fintype.card ι : ℝ)*b^2 < 1) (hT : 0 < T) :
    ∃ I : ℝ, SharpPrefix (ι := ι) F ρ η hη T
      (fun _ => sharpRadius F ρ (Fintype.card ι) b T/Real.sqrt (Fintype.card ι)) (fun _ => I) := by
  classical
  let N := Fintype.card ι
  let n : ℝ := N
  have hn : 2 ≤ n := by dsimp [n,N];exact_mod_cast hN
  have hn0 : (0:ℝ) < n := by linarith
  have hN0 : 0 < N := by dsimp [N];omega
  let R := sharpRadius F ρ n b
  let A := sharpHighDirection n b
  let B := fun t => (b*R t)*(b*R t-F)
  let W := fun t => (A-b)*R t*((A+b)*R t-F)
  have hR : Continuous R := continuous_iff_continuousAt.mpr (fun t => (sharpRadius_derivative F ρ n b t).continuousAt)
  have hBC : Continuous B := by dsimp [B];fun_prop
  have hWC : Continuous W := by dsimp [W];fun_prop
  have hWP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < W t := sharp_weight_positive F ρ n b t hF hρ.le hn hb hnb ht.1
  obtain ⟨cuts,hcuts,hmono,hcut0,hcutN,hcutI⟩ := exists_equal_weight_interval_partition W T hT hWC.continuousOn hWP N hN0
  let τ := fun k : ℕ => if hk : k ≤ N then cuts ⟨k,Nat.lt_succ_of_le hk⟩ else T
  have hτ0 : τ 0 = 0 := by simpa only [τ,dif_pos (Nat.zero_le N)] using hcut0
  have hτN : τ N = T := by simpa only [τ,dif_pos (le_refl N)] using hcutN
  have hτmem (k : ℕ) (hk : k ≤ N) : τ k ∈ Icc 0 T := by
    dsimp [τ]
    rw [dif_pos hk]
    exact hcuts _
  let e := Fintype.equivFin ι
  let WI := ∫ t in (0:ℝ)..T,W t
  let J := fun k i => (∫ t in τ k..τ (k+1),B t)/η+
    if (e i).val = k then WI/(η*n) else 0
  let Q := fun k (_ : ι) => R (τ k)/Real.sqrt n
  have hQ0 : Q 0 = fun _ => F := by
    funext i
    dsimp [Q]
    rw [hτ0]
    dsimp [R,sharpRadius]
    simp only [mul_zero,Real.exp_zero,mul_one,add_sub_cancel]
    field_simp
  have hstep (k : ℕ) (hk : k < N) (I : ι → ℝ) (hp : SharpPrefix F ρ η hη (τ k) (Q k) I) :
      SharpPrefix F ρ η hη (τ (k+1)) (Q (k+1)) (fun i => I i+J k i) := by
    let j : Fin N := ⟨k,hk⟩
    let u := sharpDirection A b (e.symm j)
    obtain ⟨hab,hsq,_,_,_⟩ := sharp_direction_geometry n b hn hb hnb
    have hu (i : ι) : 0 < u i := by
      dsimp [u,sharpDirection]
      split
      · exact hb.trans hab
      · exact hb
    have hun : ∑ i,(u i)^2 = 1 := by rw [sharpDirection_square_sum];exact hsq
    have huH : ∑ i,u i = sharpDirectionSum n b := by rw [sharpDirection_sum];rfl
    have hleft : τ k = cuts j.castSucc := by simp [τ,j,Nat.le_of_lt hk]
    have hright : τ (k+1) = cuts j.succ := by simp [τ,j,Nat.succ_le_of_lt hk]
    have hac : τ k ≤ τ (k+1) := by
      rw [hleft,hright]
      exact (hmono (show j.castSucc < j.succ by exact_mod_cast Nat.lt_succ_self k)).le
    have hWI : (∫ t in τ k..τ (k+1),W t) = WI/n := by rw [hleft,hright];exact hcutI j
    have hrec (i : ι) : (∫ t in τ k..τ (k+1),(u i*R t)*(u i*R t-F)/η) = J k i := by
      have hh := sharp_direction_interval_recovery F η A b R (e.symm j) i (τ k) (τ (k+1)) (WI/n) hR hWI
      have heq : i = e.symm j ↔ (e i).val = k := by
        constructor
        · intro hi
          rw [hi,e.apply_symm_apply]
        · intro hi
          apply e.injective
          rw [e.apply_symm_apply]
          exact Fin.ext hi
      dsimp [J]
      simpa only [u,B,heq,div_div,mul_comm] using hh
    have hh := sharpPrefix_one_direction hub F ρ η b T hF hρ hη hN hb hnb hT u hu hun huH
      (τ k) (τ (k+1)) (hτmem k hk.le) (hτmem (k+1) (by omega)) hac I hp
    change SharpPrefix F ρ η hη (τ (k+1)) (Q (k+1))
      (fun i => I i+∫ t in τ k..τ (k+1),(u i*R t)*(u i*R t-F)/η) at hh
    simpa only [hrec] using hh
  have hpref := sharpPrefix_sequence F ρ η hη N τ Q J hτ0 hQ0 hstep
  have hBsum : (∑ k ∈ Finset.range N,∫ t in τ k..τ (k+1),B t) = ∫ t in (0:ℝ)..T,B t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := B) (a := τ) (n := N)
      (fun k _ => hBC.intervalIntegrable (τ k) (τ (k+1)))
    simpa only [hτ0,hτN] using hh
  have hsum (i : ι) : (∑ k ∈ Finset.range N,J k i) = (∫ t in (0:ℝ)..T,B t)/η+WI/(η*n) := by
    dsimp [J]
    rw [Finset.sum_add_distrib,←Finset.sum_div,hBsum]
    have hi : (e i).val < N := (e i).isLt
    simp [hi]
  refine ⟨(∫ t in (0:ℝ)..T,B t)/η+WI/(η*n),?_⟩
  simpa only [Q,hτN,hsum] using hpref

theorem sharp_rotating_original_path (hub : ι) (F ρ η b T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hb : 0 < b) (hnb : (Fintype.card ι : ℝ)*b^2 < 1) (hT : 0 < T) :
    ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => constantResponse η hη) completePairedEdges,
      P.terminal.time = T ∧ ∀ i, P.terminal.prices i =
        sharpRadius F ρ (Fintype.card ι) b T/Real.sqrt (Fintype.card ι) := by
  letI : Nonempty ι := ⟨hub⟩
  obtain ⟨I,s,t,path,hs0,hsP,hsH,hsL,htT,htP,hrec⟩ :=
    sharp_symmetric_recovery_prefix hub F ρ η b T hF hρ hη hN hb hnb hT
  have hclose := common_recovery_dollars_closed F ρ (constantResponse η hη)
    (sharpRadius F ρ (Fintype.card ι) b T/Real.sqrt (Fintype.card ι)) I path
    (fun i => congrFun hsP i) (fun i => congrFun htP i) (fun i => by rw [hsL];rfl) hrec
  let P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => constantResponse η hη) completePairedEdges := {
    benchmark_positive := fun _ => hF
    resilience_nonnegative := fun _ => hρ.le
    initial := s
    terminal := t
    trace := path
    at_zero := hs0
    initial_prices := fun i => congrFun hsP i
    initial_holdings := hsH
    initial_dollars := fun i => by rw [hsL];rfl
    terminal_dollars := hclose }
  exact ⟨P,htT,fun i => congrFun htP i⟩

theorem theorem_4_4_original_feasible [Nonempty ι] (hN : 2 ≤ Fintype.card ι)
    (F ρ η T δ : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    (hδ : 0 < δ) (hcrit : δ < sharpCriticalLoss (Fintype.card ι) ρ T) :
    ∃ (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => constantResponse η hη) completePairedEdges) (M0 H0 : ℝ),
      P.terminal.time = T ∧ (∀ i, P.terminal.prices i = F*Real.exp (-δ)) ∧
      0 ≤ M0 ∧ P.trace.pairedTurnover ≤ M0 ∧ 0 < H0 ∧ (∀ i, P.initial.shares i ≤ H0) ∧
      δ ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) := by
  classical
  have hn : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  obtain ⟨b,hb,hnb,hratio⟩ := sharp_delta_parameter (Fintype.card ι) ρ T δ hn hρ hT hδ hcrit
  let hub : ι := Classical.arbitrary ι
  obtain ⟨P,hPT,hPS⟩ := sharp_rotating_original_path hub F ρ η b T hF hρ hη hN hb hnb hT
  have hprice (i : ι) : P.terminal.prices i = F*Real.exp (-δ) := by
    rw [hPS i]
    dsimp [sharpRadius]
    rw [mul_div_assoc,hratio]
  let M0 := max 0 P.trace.pairedTurnover
  let H0 := 1+∑ i,|P.initial.shares i|
  have hH0 : 0 < H0 := by
    have hh := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (P.initial.shares i))
    dsimp [H0]
    linarith
  have hH (i : ι) : P.initial.shares i ≤ H0 := by
    have hh := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => abs_nonneg (P.initial.shares j)) (Finset.mem_univ i)
    dsimp [H0]
    linarith [le_abs_self (P.initial.shares i)]
  refine ⟨P,M0,H0,hPT,hprice,le_max_left _ _,le_max_right _ _,hH0,hH,?_⟩
  apply systemicCrisis_lower_of_each_loss _ _ Fintype.card_pos le_rfl
  intro i
  dsimp [logPriceFromBenchmark]
  rw [hprice i,mul_div_cancel_left₀ _ hF.ne',Real.log_exp]
  linarith

def sharpOriginalCrisisSet (F ρ η T : ℝ) (hη : 0 < η) : Set ℝ :=
  {δ | ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
    (fun _ => constantResponse η hη) completePairedEdges,
    P.terminal.time = T ∧ δ ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι)}

theorem sharpOriginalCrisisSet_supremum [Nonempty ι] (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T) :
    sSup (sharpOriginalCrisisSet (ι := ι) F ρ η T hη) = sharpCriticalLoss (Fintype.card ι) ρ T := by
  let D := sharpCriticalLoss (Fintype.card ι) ρ T
  have hD : 0 < D := originalSharpCriticalLoss_positive (Fintype.card ι) ρ T
    (by exact_mod_cast hN) hρ hT
  have hmem (δ : ℝ) (hδ : 0 < δ) (hδD : δ < D) : δ ∈ sharpOriginalCrisisSet (ι := ι) F ρ η T hη := by
    obtain ⟨P,M,H,hPT,hPS,hM,hMcap,hH,hHcap,hC⟩ := theorem_4_4_original_feasible hN F ρ η T δ hF hρ hη hT hδ hδD
    exact ⟨P,hPT,hC⟩
  have hne : (sharpOriginalCrisisSet (ι := ι) F ρ η T hη).Nonempty :=
    ⟨D/2,hmem (D/2) (half_pos hD) (half_lt_self hD)⟩
  have hupper : ∀ δ ∈ sharpOriginalCrisisSet (ι := ι) F ρ η T hη, δ ≤ D := by
    intro δ hδ
    obtain ⟨P,hPT,hC⟩ := hδ
    exact hC.trans (original_path_strict_crisis_upper hN F ρ η T hF hρ hη hT P hPT).le
  have hbounded : BddAbove (sharpOriginalCrisisSet (ι := ι) F ρ η T hη) := ⟨D,hupper⟩
  apply le_antisymm (csSup_le hne hupper)
  apply le_of_not_gt
  intro hlt
  let δ := (max 0 (sSup (sharpOriginalCrisisSet (ι := ι) F ρ η T hη))+D)/2
  have hmax : max 0 (sSup (sharpOriginalCrisisSet (ι := ι) F ρ η T hη)) < D := max_lt_iff.mpr ⟨hD,hlt⟩
  have hδ : 0 < δ := by dsimp [δ];linarith [le_max_left 0 (sSup (sharpOriginalCrisisSet (ι := ι) F ρ η T hη))]
  have hδD : δ < D := by dsimp [δ];linarith
  have hδsup := le_csSup hbounded (hmem δ hδ hδD)
  dsimp [δ] at hδsup
  linarith [le_max_right 0 (sSup (sharpOriginalCrisisSet (ι := ι) F ρ η T hη))]

/-- The full original Theorem 4.4: actual finite economic constructions
at every strictly interior threshold, the strict universal exclusion,
and the unattained supremum of the attainable full-coverage thresholds. -/
theorem theorem_4_4_original [Nonempty ι] (hN : 2 ≤ Fintype.card ι)
    (F ρ η T : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T) :
    (0 < sharpCriticalLoss (Fintype.card ι) ρ T) ∧
    (∀ δ : ℝ, 0 < δ → δ < sharpCriticalLoss (Fintype.card ι) ρ T →
      ∃ (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
        (fun _ => constantResponse η hη) completePairedEdges) (M0 H0 : ℝ),
        P.terminal.time = T ∧ (∀ i, P.terminal.prices i = F*Real.exp (-δ)) ∧
        0 ≤ M0 ∧ P.trace.pairedTurnover ≤ M0 ∧ 0 < H0 ∧ (∀ i, P.initial.shares i ≤ H0) ∧
        δ ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι)) ∧
    (∀ (κ : Type) [Fintype κ] (edges : κ → PairedEdge ι)
      (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
        (fun _ => constantResponse η hη) edges), P.terminal.time = T →
      systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) <
        sharpCriticalLoss (Fintype.card ι) ρ T) ∧
    sSup (sharpOriginalCrisisSet (ι := ι) F ρ η T hη) = sharpCriticalLoss (Fintype.card ι) ρ T := by
  refine ⟨originalSharpCriticalLoss_positive (Fintype.card ι) ρ T (by exact_mod_cast hN) hρ hT,
    fun δ hδ hcrit => theorem_4_4_original_feasible hN F ρ η T δ hF hρ hη hT hδ hcrit,?_,
    sharpOriginalCrisisSet_supremum hN F ρ η T hF hρ hη hT⟩
  intro κ inst edges P hPT
  exact original_path_strict_crisis_upper hN F ρ η T hF hρ hη hT P hPT

theorem theorem_4_4_original_finite_resources [Nonempty ι] (hN : 2 ≤ Fintype.card ι)
    (F ρ η T δ : ℝ) (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hT : 0 < T)
    (hδ : 0 < δ) (hcrit : δ < sharpCriticalLoss (Fintype.card ι) ρ T) :
    ∃ (P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => constantResponse η hη) completePairedEdges) (M0 H0 V0 : ℝ),
      P.terminal.time = T ∧ (∀ i, P.terminal.prices i = F*Real.exp (-δ)) ∧
      0 ≤ M0 ∧ P.trace.pairedTurnover ≤ M0 ∧ 0 < H0 ∧ (∀ i, P.initial.shares i ≤ H0) ∧
      0 ≤ V0 ∧ (∀ i, P.trace.shareSales i ≤ V0) ∧
      δ ≤ systemicCrisis (logPriceFromBenchmark F P.terminal.prices) (Fintype.card ι) := by
  classical
  obtain ⟨P,M,H,hT,hP,hM,hMc,hH,hHc,hC⟩ :=
    theorem_4_4_original_feasible hN F ρ η T δ hF hρ hη hT hδ hcrit
  refine ⟨P,M,H,∑ i, P.trace.shareSales i,hT,hP,hM,hMc,hH,hHc,?_,?_,hC⟩
  · exact Finset.sum_nonneg (fun i _ => P.trace.shareSales_nonnegative i)
  · intro i
    exact Finset.single_le_sum (fun j _ => P.trace.shareSales_nonnegative j) (Finset.mem_univ i)

end MarketCrash

