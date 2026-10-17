import MarketCrash.SharpAssembly
import MarketCrash.SharpTransportResources
import MarketCrash.SevereRadial
import MarketCrash.SevereParameter
import MarketCrash.SevereRateBounds

noncomputable section
namespace MarketCrash
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def severeAssemblyDirection (a c b : ℝ) (comp center : ι) (i : ι) : ℝ :=
  if i = comp then b else if i = center then a else c

theorem severeAssemblyDirection_sum (a c b : ℝ) (comp center : ι) (hne : center ≠ comp) :
    ∑ i, severeAssemblyDirection a c b comp center i = a+((Fintype.card ι : ℝ)-2)*c+b := by
  have he (i : ι) : severeAssemblyDirection a c b comp center i =
      c+(if i = comp then b-c else 0)+(if i = center then a-c else 0) := by
    by_cases hi : i = comp
    · subst i;simp [severeAssemblyDirection,hne.symm] <;> ring
    · by_cases hj : i = center
      · subst i;simp [severeAssemblyDirection,hne] <;> ring
      · simp [severeAssemblyDirection,hi,hj]
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp
  ring

theorem severeAssemblyDirection_square_sum (a c b : ℝ) (comp center : ι) (hne : center ≠ comp) :
    ∑ i, (severeAssemblyDirection a c b comp center i)^2 = a^2+((Fintype.card ι : ℝ)-2)*c^2+b^2 := by
  simpa only [severeAssemblyDirection,ite_pow] using severeAssemblyDirection_sum (a^2) (c^2) (b^2) comp center hne

theorem severeAssemblyPrefix_one_direction (hub : ι) (F ρ η H T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt (Fintype.card ι)) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i,0 < u i) (hun : ∑ i,(u i)^2 = 1)
    (huH : ∑ i,u i = H)
    (a c : ℝ) (ha : a ∈ Icc 0 T) (hc : c ∈ Icc 0 T) (hac : a ≤ c)
    (I : ι → ℝ)
    (hp : SharpPrefix F ρ η hη a (fun _ => severeRadius F ρ (Fintype.card ι) H a/Real.sqrt (Fintype.card ι)) I) :
    SharpPrefix F ρ η hη c (fun _ => severeRadius F ρ (Fintype.card ι) H c/Real.sqrt (Fintype.card ι))
      (fun i => I i+∫ t in a..c,(u i*severeRadius F ρ (Fintype.card ι) H t)*
        (u i*severeRadius F ρ (Fintype.card ι) H t-F)/η) := by
  have hn : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  let R := severeRadius F ρ (Fintype.card ι) H
  have hroot : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hRP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < R t := by
    exact (mul_pos hF hH).trans_le
      (severe_radius_bounds F ρ (Fintype.card ι) H t hF hρ.le hH hHn ht.1).1
  obtain ⟨m,hma,hmb,hmF,hmρ,hmg,hmS,hmL,hmBV⟩ :=
    severe_radial_physical_piece hub F ρ η (Fintype.card ι) H T hF hρ hη hn hH hHn hT u hu hun huH
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


set_option maxHeartbeats 800000 in
theorem severeAssembly_symmetric_prefix (comp : ι) (F ρ η c b T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hc : 0 < c) (hb : 0 < b) (hT : 0 < T)
    (hac : c < severeHigh (Fintype.card ι) c b)
    (hnorm : (severeHigh (Fintype.card ι) c b)^2+((Fintype.card ι : ℝ)-2)*c^2+b^2 = 1)
    (hH : 0 < severeDirectionSum (Fintype.card ι) c b)
    (hHn : severeDirectionSum (Fintype.card ι) c b ≤ Real.sqrt (Fintype.card ι))
    (hW : 1 < (severeHigh (Fintype.card ι) c b+c)*severeDirectionSum (Fintype.card ι) c b) :
    ∃ I : ℝ, SharpPrefix F ρ η hη T
      (fun _ : ι => severeRadius F ρ (Fintype.card ι) (severeDirectionSum (Fintype.card ι) c b) T/Real.sqrt (Fintype.card ι))
      (fun i => if i = comp then severeRecoveryPrimitive F ρ (Fintype.card ι)
        (severeDirectionSum (Fintype.card ι) c b) b T/η else I) := by
  classical
  let Targets := {i : ι // i ≠ comp}
  let M := Fintype.card Targets
  let n : ℝ := Fintype.card ι
  let H := severeDirectionSum n c b
  let A := severeHigh n c b
  let R := severeRadius F ρ n H
  have hNtarget : M = Fintype.card ι-1 := by dsimp [M,Targets];simp
  have hM : 0 < M := by omega
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  let C := fun t => (c*R t)*(c*R t-F)
  let B := fun t => (b*R t)*(b*R t-F)
  let W := fun t => (A-c)*R t*((A+c)*R t-F)
  have hRC : Continuous R := continuous_iff_continuousAt.mpr (fun t => (severeRadius_derivative F ρ n H t).continuousAt)
  have hCC : Continuous C := by dsimp [C];fun_prop
  have hBC : Continuous B := by dsimp [B];fun_prop
  have hWC : Continuous W := by dsimp [W];fun_prop
  have hWP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < W t := by
    have hR := (severe_radius_bounds F ρ n H t hF hρ.le hH hHn ht.1).1
    have hRp : 0 < R t := (mul_pos hF hH).trans_le hR
    have hAc : 0 < A+c := by dsimp [A] at *;linarith
    have hmul := mul_le_mul_of_nonneg_left hR hAc.le
    have hlast : 0 < (A+c)*R t-F := by
      have hh := mul_lt_mul_of_pos_left hW hF
      dsimp [A,H] at *
      nlinarith
    exact mul_pos (mul_pos (sub_pos.mpr hac) hRp) hlast
  obtain ⟨cuts,hcuts,hmono,hcut0,hcutM,hcutI⟩ := exists_equal_weight_interval_partition W T hT hWC.continuousOn hWP M hM
  let τ := fun k : ℕ => if hk : k ≤ M then cuts ⟨k,Nat.lt_succ_of_le hk⟩ else T
  have hτ0 : τ 0 = 0 := by simpa only [τ,dif_pos (Nat.zero_le M)] using hcut0
  have hτM : τ M = T := by simpa only [τ,dif_pos (le_refl M)] using hcutM
  have hτmem (k : ℕ) (hk : k ≤ M) : τ k ∈ Icc 0 T := by
    dsimp [τ];rw [dif_pos hk];exact hcuts _
  let e := Fintype.equivFin Targets
  let index := fun i : ι => if hi : i ≠ comp then (e ⟨i,hi⟩).val else 0
  let WI := ∫ t in (0:ℝ)..T,W t
  let J := fun k i => if i = comp then (∫ t in τ k..τ (k+1),B t)/η else
    (∫ t in τ k..τ (k+1),C t)/η+if index i = k then WI/(η*M) else 0
  let Q := fun k (_ : ι) => R (τ k)/Real.sqrt n
  have hQ0 : Q 0 = fun _ => F := by
    funext i;dsimp [Q];rw [hτ0];dsimp [R,severeRadius]
    simp only [mul_zero,Real.exp_zero,mul_one,add_sub_cancel]
    field_simp
  have hstep (k : ℕ) (hk : k < M) (I : ι → ℝ) (hp : SharpPrefix F ρ η hη (τ k) (Q k) I) :
      SharpPrefix F ρ η hη (τ (k+1)) (Q (k+1)) (fun i => I i+J k i) := by
    let j : Fin M := ⟨k,hk⟩
    let center : Targets := e.symm j
    let u := severeAssemblyDirection A c b comp center
    have hu (i : ι) : 0 < u i := by
      dsimp [u,severeAssemblyDirection];split
      · exact hb
      · split
        · exact hc.trans hac
        · exact hc
    have hun : ∑ i,(u i)^2 = 1 := by rw [severeAssemblyDirection_square_sum _ _ _ _ _ center.property];exact hnorm
    have huH : ∑ i,u i = H := by rw [severeAssemblyDirection_sum _ _ _ _ _ center.property];rfl
    have hleft : τ k = cuts j.castSucc := by simp [τ,j,Nat.le_of_lt hk]
    have hright : τ (k+1) = cuts j.succ := by simp [τ,j,Nat.succ_le_of_lt hk]
    have hacut : τ k ≤ τ (k+1) := by
      rw [hleft,hright];exact (hmono (show j.castSucc < j.succ by exact_mod_cast Nat.lt_succ_self k)).le
    have hWI : (∫ t in τ k..τ (k+1),W t) = WI/M := by rw [hleft,hright];exact hcutI j
    have hrec (i : ι) : (∫ t in τ k..τ (k+1),(u i*R t)*(u i*R t-F)/η) = J k i := by
      by_cases hi : i = comp
      · subst i
        simp only [u,severeAssemblyDirection,ite_true,J,intervalIntegral.integral_div,B]
      · have heq : i = (center : ι) ↔ index i = k := by
          dsimp [index];rw [dif_pos hi]
          constructor
          · intro hh
            have hh' : (⟨i,hi⟩ : Targets) = center := Subtype.ext hh
            rw [hh']
            exact congrArg Fin.val (e.apply_symm_apply j)
          · intro hh
            have hh' : e ⟨i,hi⟩ = j := Fin.ext hh
            exact congrArg Subtype.val (e.injective (hh'.trans (e.apply_symm_apply j).symm))
        have hh := sharp_direction_interval_recovery F η A c R (center : ι) i (τ k) (τ (k+1)) (WI/M) hRC hWI
        have huEq : u i = sharpDirection A c (center : ι) i := by simp [u,severeAssemblyDirection,sharpDirection,hi]
        rw [huEq]
        dsimp [J]
        simp only [if_neg hi]
        simpa only [C,heq,div_div,mul_comm] using hh
    have hh := severeAssemblyPrefix_one_direction comp F ρ η H T hF hρ hη hN hH hHn hT u hu hun huH
      (τ k) (τ (k+1)) (hτmem k hk.le) (hτmem (k+1) (by omega)) hacut I hp
    change SharpPrefix F ρ η hη (τ (k+1)) (Q (k+1))
      (fun i => I i+∫ t in τ k..τ (k+1),(u i*R t)*(u i*R t-F)/η) at hh
    simpa only [hrec] using hh
  have hpref := sharpPrefix_sequence F ρ η hη M τ Q J hτ0 hQ0 hstep
  have hBsum : (∑ k ∈ Finset.range M,∫ t in τ k..τ (k+1),B t) = ∫ t in (0:ℝ)..T,B t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := B) (a := τ) (n := M)
      (fun k _ => hBC.intervalIntegrable (τ k) (τ (k+1)))
    simpa only [hτ0,hτM] using hh
  have hCsum : (∑ k ∈ Finset.range M,∫ t in τ k..τ (k+1),C t) = ∫ t in (0:ℝ)..T,C t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := C) (a := τ) (n := M)
      (fun k _ => hCC.intervalIntegrable (τ k) (τ (k+1)))
    simpa only [hτ0,hτM] using hh
  have hsum (i : ι) : (∑ k ∈ Finset.range M,J k i) =
      if i = comp then severeRecoveryPrimitive F ρ n H b T/η else (∫ t in (0:ℝ)..T,C t)/η+WI/(η*M) := by
    by_cases hi : i = comp
    · simp only [J,if_pos hi,←Finset.sum_div,hBsum]
      rw [severe_recovery_integral F ρ n H b T hρ.ne']
    · have hidx : index i < M := by dsimp [index];rw [dif_pos hi];exact (e ⟨i,hi⟩).isLt
      simp only [J,if_neg hi,Finset.sum_add_distrib,←Finset.sum_div,hCsum]
      simp [hidx]
  refine ⟨(∫ t in (0:ℝ)..T,C t)/η+WI/(η*M),?_⟩
  simpa only [Q,hτM,hsum] using hpref

set_option maxHeartbeats 800000 in
theorem severeAssembly_closed_path (comp : ι) (F ρ η c b T eps : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hc : 0 < c) (hb : 0 < b) (hT : 0 < T) (heps : 0 < eps)
    (hac : c < severeHigh (Fintype.card ι) c b)
    (hnorm : (severeHigh (Fintype.card ι) c b)^2+((Fintype.card ι : ℝ)-2)*c^2+b^2 = 1)
    (hH : 0 < severeDirectionSum (Fintype.card ι) c b)
    (hHn : severeDirectionSum (Fintype.card ι) c b ≤ Real.sqrt (Fintype.card ι))
    (hW : 1 < (severeHigh (Fintype.card ι) c b+c)*severeDirectionSum (Fintype.card ι) c b)
    (hrad : ((Fintype.card ι : ℝ)-1)*eps^2 <
      (severeRadius F ρ (Fintype.card ι) (severeDirectionSum (Fintype.card ι) c b) T)^2)
    (hledger : severeCompensatorLedger F ρ η (Fintype.card ι)
      (severeDirectionSum (Fintype.card ι) c b) b T eps = 0) :
    ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => constantResponse η hη) completePairedEdges,
      P.terminal.time = T ∧ (∀ i, i ≠ comp → P.terminal.prices i = eps) ∧
      P.terminal.prices comp = Real.sqrt
        ((severeRadius F ρ (Fintype.card ι) (severeDirectionSum (Fintype.card ι) c b) T)^2-
          ((Fintype.card ι : ℝ)-1)*eps^2) := by
  classical
  let n : ℝ := Fintype.card ι
  let H := severeDirectionSum n c b
  let R := severeRadius F ρ n H T
  let C := Real.sqrt (R^2-(n-1)*eps^2)
  let Q := sharpDirection C eps comp
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  have hC : 0 < C := Real.sqrt_pos.mpr (sub_pos.mpr hrad)
  have hCsq : C^2 = R^2-(n-1)*eps^2 := Real.sq_sqrt (sub_pos.mpr hrad).le
  obtain ⟨I,hpref⟩ := severeAssembly_symmetric_prefix comp F ρ η c b T hF hρ hη hN hc hb hT hac hnorm hH hHn hW
  have hR : 0 < R := (mul_pos hF hH).trans_le
    (severe_radius_bounds F ρ n H T hF hρ.le hH hHn hT.le).1
  have hQP (i : ι) : 0 < Q i := by dsimp [Q,sharpDirection];split <;> assumption
  have hQsum : ∑ i,(Q i)^2 = R^2 := by
    rw [sharpDirection_square_sum]
    dsimp [n] at hCsq ⊢
    linarith
  have hprefix := sharpPrefix_transport comp F ρ η T hF hη _ Q _
    (fun _ => div_pos hR (Real.sqrt_pos.mpr (by linarith : 0 < n))) hQP
    (by rw [sharp_isotropic_square_sum _ (by omega),hQsum]) hpref
  obtain ⟨s,t,path,hs0,hsP,hsH,hsL,htT,htP,hI⟩ := hprefix
  have hprices (i : ι) : t.prices i = Q i := congrFun htP i
  have hcoord (i : ι) : coordinate F (constantResponse η hη).impact (t.prices i) =
      ((t.prices i)^2-F^2)/(2*η) := by
    have hh := constantCoordinate_eq_integral F η hF hη (show t.prices i ∈ positivePrices by rw [hprices];exact hQP i)
    exact hh.symm
  have hnormal (i : ι) : t.dollars i = ((t.prices i)^2-F^2)/(2*η)+ρ*path.recoveryIntegral i := by
    have hh := path.recovery_normal_form i
    simp only [hsP,hsL,Pi.zero_apply,coordinate_at_benchmark,sub_zero,hcoord] at hh
    linarith
  have hcomp : t.dollars comp = 0 := by
    rw [hnormal,hI,hprices]
    simp only [Q,sharpDirection,ite_true]
    rw [hCsq]
    dsimp [severeCompensatorLedger] at hledger
    dsimp [R,H,n] at *
    convert hledger using 1 <;> ring
  let E := (eps^2-F^2)/(2*η)+ρ*I
  have hall (i : ι) : t.dollars i = if i = comp then 0 else E := by
    by_cases hi : i = comp
    · subst i;simpa using hcomp
    · rw [hnormal,hI,hprices]
      simp only [if_neg hi,Q,sharpDirection]
      rfl
  have hsum := path.dollar_sum_preserved
  simp only [hsL,Pi.zero_apply,Finset.sum_const_zero] at hsum
  have hsum' : ∑ i,t.dollars i = (n-1)*E := by
    simp_rw [hall]
    have hh := sharpDirection_sum (ι := ι) 0 E comp
    simpa only [sharpDirection,zero_add] using hh
  rw [hsum'] at hsum
  have hE : E = 0 := by nlinarith
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
    initial_dollars := fun i => congrFun hsL i
    terminal_dollars := fun i => by rw [hall,hE];split <;> rfl }
  refine ⟨P,htT,?_,?_⟩
  · intro i hi
    exact (hprices i).trans (by simp [Q,sharpDirection,hi])
  · exact (hprices comp).trans (by simp [Q,sharpDirection];rfl)

set_option maxHeartbeats 800000 in
theorem severeAssembly_original_family (comp : ι) (F ρ η : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι) :
    ∃ T eps0 : ℝ, 0 < T ∧ 0 < eps0 ∧ ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
        (fun _ => constantResponse η hη) completePairedEdges,
        P.terminal.time = T ∧ (∀ i, i ≠ comp → P.terminal.prices i = eps) ∧
        0 < P.terminal.prices comp := by
  let n : ℝ := Fintype.card ι
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  obtain ⟨c,T,eps0,hc,hcn,hcs,hT,heps0,hfamily⟩ := severe_parameter_family F ρ η n hF hρ hη hn
  let eps1 := min eps0 (F/(2*Real.sqrt n))
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have heps1 : 0 < eps1 := lt_min heps0 (by positivity)
  refine ⟨T,eps1,hT,heps1,?_⟩
  intro eps hep hepb
  have hepa : eps < eps0 := (lt_min_iff.mp hepb).1
  have hepsmall : eps < F/(2*Real.sqrt n) := (lt_min_iff.mp hepb).2
  obtain ⟨b,hb,hledger,hba,hnorm,hH,hHn,hW⟩ := hfamily eps hep.le hepa
  let A := severeHigh n c b
  let H := severeDirectionSum n c b
  let R := severeRadius F ρ n H T
  have hAc : (n-2)*c^2 ≤ 1/20000 := by
    have hD : (n-2)*c ≤ 1/100 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hD hc.le,hcs]
  have hA : 9/10 < A := by
    have hAp : 0 < A := hb.1.trans hba
    have hbq : b^2 < 1/25 := by nlinarith [hb.1,hb.2]
    dsimp [A] at *
    nlinarith only [hnorm,hAc,hbq,hAp]
  have hac : c < A := by linarith
  have hHA : A ≤ H := by
    have hh := mul_nonneg (by linarith : 0 ≤ n-2) hc.le
    dsimp [H,severeDirectionSum,A]
    linarith [hb.1]
  have hR : (9/10)*F < R := by
    have hh := (severe_radius_bounds F ρ n H T hF hρ.le hH hHn hT.le).1
    have haF := mul_lt_mul_of_pos_left (hA.trans_le hHA) hF
    dsimp [R]
    nlinarith only [hh,haF]
  have hεsqrt : eps*Real.sqrt n < F/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*Real.sqrt n)).mp hepsmall
    nlinarith
  have hεsq : n*eps^2 < F^2/4 := by
    have hh := mul_self_lt_mul_self (by positivity : 0 ≤ eps*Real.sqrt n) hεsqrt
    have hs := Real.sq_sqrt (by linarith : 0 ≤ n)
    nlinarith
  have hrad : (n-1)*eps^2 < R^2 := by
    have hRp : 0 < R := (mul_pos (by norm_num) hF).trans hR
    nlinarith only [hεsq,hR,hRp,hF,sq_nonneg eps]
  obtain ⟨P,hPT,hPS,hPC⟩ := severeAssembly_closed_path comp F ρ η c b T eps hF hρ hη hN hc hb.1 hT hep
    hac hnorm hH hHn hW hrad hledger
  refine ⟨P,hPT,hPS,?_⟩
  rw [hPC]
  exact Real.sqrt_pos.mpr (sub_pos.mpr hrad)

def SeverePrefix (F ρ η : ℝ) (hη : 0 < η) (τ : ℝ) (Q I : ι → ℝ) (M V J : ℝ) : Prop :=
  ∃ (s t : PhysicalMarketState ι)
    (path : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη)
      completePairedEdges s t),
    s.time = 0 ∧ s.prices = (fun _ => F) ∧ (∀ i, 0 ≤ s.shares i) ∧ s.dollars = 0 ∧
    t.time = τ ∧ t.prices = Q ∧ (∀ i, path.recoveryIntegral i = I i) ∧
    path.pairedTurnover ≤ M ∧ (∀ i, path.shareSales i ≤ V) ∧ (∀ i, s.shares i ≤ J)

theorem severePrefix_zero (F ρ η : ℝ) (hη : 0 < η) :
    SeverePrefix (ι := ι) F ρ η hη 0 (fun _ => F) 0 0 0 0 := by
  let s : PhysicalMarketState ι := ⟨0,fun _ => F,0,0⟩
  exact ⟨s,s,.refl s,rfl,rfl,fun _ => le_rfl,rfl,rfl,rfl,fun _ => rfl,le_rfl,fun _ => le_rfl,fun _ => le_rfl⟩

theorem severePrefix_forget (F ρ η : ℝ) (hη : 0 < η) (τ : ℝ) (Q I : ι → ℝ) (M V J : ℝ)
    (hp : SeverePrefix F ρ η hη τ Q I M V J) : SharpPrefix F ρ η hη τ Q I := by
  obtain ⟨s,t,p,hs0,hsP,hsH,hsL,htT,htP,hI,hM,hV,hJ⟩ := hp
  exact ⟨s,t,p,hs0,hsP,hsH,hsL,htT,htP,hI⟩

theorem severePrefix_relax (F ρ η : ℝ) (hη : 0 < η) (τ : ℝ) (Q I : ι → ℝ)
    (M V J M' V' J' : ℝ) (hp : SeverePrefix F ρ η hη τ Q I M V J)
    (hM : M ≤ M') (hV : V ≤ V') (hJ : J ≤ J') : SeverePrefix F ρ η hη τ Q I M' V' J' := by
  obtain ⟨s,t,p,hs0,hsP,hsH,hsL,htT,htP,hI,hpM,hpV,hpJ⟩ := hp
  exact ⟨s,t,p,hs0,hsP,hsH,hsL,htT,htP,hI,hpM.trans hM,fun i => (hpV i).trans hV,fun i => (hpJ i).trans hJ⟩

theorem severePrefix_append (F ρ η : ℝ) (hη : 0 < η) (τ σ : ℝ) (Q Q' I I' : ι → ℝ)
    (M V J M' V' J' : ℝ) (hp : SeverePrefix F ρ η hη τ Q I M V J)
    {u v : PhysicalMarketState ι}
    (arc : OriginalPhysicalReachable (fun _ => F) (fun _ => ρ) (fun _ => constantResponse η hη)
      completePairedEdges u v)
    (hut : u.time = τ) (hup : u.prices = Q) (hvt : v.time = σ) (hvp : v.prices = Q')
    (hrec : ∀ i, arc.recoveryIntegral i = I' i)
    (hM : arc.pairedTurnover ≤ M') (hV : ∀ i,arc.shareSales i ≤ V')
    (hJ : ∀ i,u.shares i ≤ J') (hJ' : 0 ≤ J') :
    SeverePrefix F ρ η hη σ Q' (fun i => I i+I' i) (M+M') (V+V') (J+J') := by
  obtain ⟨s,t,path,hs0,hsP,hsH,hsL,htT,htP,hI,hpM,hpV,hpJ⟩ := hp
  obtain ⟨H1,H2,L,hH1,hH2,hH1eq,hH2eq,joined,hjoin,hjoinM,hjoinV⟩ := concatenate_with_resources path arc
    (htT.trans hut.symm) (htP.trans hup.symm)
  refine ⟨physicalEconomicOffset s H1 0,physicalEconomicOffset v H2 L,joined,
    hs0,hsP,?_,?_,hvt,hvp,?_,?_,?_,?_⟩
  · intro i;exact add_nonneg (hH1 i) (hsH i)
  · change (fun i => 0+s.dollars i) = 0
    simp [hsL];rfl
  · intro i;rw [hjoin,hI,hrec]
  · rw [hjoinM];exact add_le_add hpM hM
  · intro i;rw [hjoinV];exact add_le_add (hpV i) (hV i)
  · intro i
    change H1 i+s.shares i ≤ J+J'
    have hn := path.endpoint_no_short hsH i
    have hh : H1 i ≤ J' := by rw [hH1eq];exact max_le (by linarith [hJ i]) hJ'
    linarith [hpJ i]

def severeRotationDollarBudget (η R : ℝ) : ℝ := (Fintype.card ι : ℝ)*R^2/η
def severeRotationShareBudget (η R : ℝ) : ℝ := 2*(Fintype.card ι : ℝ)*R/η

theorem severePrefix_transport (hub : ι) (F ρ η τ R : ℝ) (hF : 0 < F) (hη : 0 < η) (hR : 0 < R)
    (P Q I : ι → ℝ) (hP : ∀ i,0 < P i) (hQ : ∀ i,0 < Q i)
    (hsq : ∑ i,(P i)^2 = ∑ i,(Q i)^2) (hbound : ∑ i,(P i)^2 ≤ R^2)
    (M V J : ℝ) (hp : SeverePrefix F ρ η hη τ P I M V J) :
    SeverePrefix F ρ η hη τ Q I
      (M+severeRotationDollarBudget (ι := ι) η R) (V+severeRotationShareBudget (ι := ι) η R) (J+R/η) := by
  let x := fun i => (P i)^2/(2*η)
  let y := fun i => (Q i)^2/(2*η)
  let X := R^2/(2*η)
  have hx (i : ι) : 0 < x i := div_pos (sq_pos_of_pos (hP i)) (by positivity)
  have hy (i : ι) : 0 < y i := div_pos (sq_pos_of_pos (hQ i)) (by positivity)
  have hxy : ∑ i,x i = ∑ i,y i := by dsimp [x,y];rw [←Finset.sum_div,←Finset.sum_div,hsq]
  have hX : ∑ i,x i ≤ X := by dsimp [x,X];rw [←Finset.sum_div];exact div_le_div_of_nonneg_right hbound (by positivity)
  obtain ⟨arc,hM,hV⟩ := sharpTransport_uniform_resources hub τ F η hF hη (fun _ => ρ) 0 0 x y
    (fun _ => le_rfl) hx hy hxy X (by dsimp [X];positivity) hX
  have hsx (i : ι) : Real.sqrt (2*η*x i) = P i := by
    have he : 2*η*x i = (P i)^2 := by dsimp [x];field_simp
    rw [he,Real.sqrt_sq (hP i).le]
  have hsy (i : ι) : Real.sqrt (2*η*y i) = Q i := by
    have he : 2*η*y i = (Q i)^2 := by dsimp [y];field_simp
    rw [he,Real.sqrt_sq (hQ i).le]
  have hroot : Real.sqrt (2*η*X) = R := by
    have he : 2*η*X = R^2 := by dsimp [X];field_simp
    rw [he,Real.sqrt_sq hR.le]
  have hM' : arc.pairedTurnover ≤ severeRotationDollarBudget (ι := ι) η R := by
    convert hM using 1
    dsimp [X,severeRotationDollarBudget]
    push_cast
    ring
  have hV' (i : ι) : arc.shareSales i ≤ severeRotationShareBudget (ι := ι) η R := by
    have hh := hV i
    rw [hroot] at hh
    convert hh using 1
    dsimp [severeRotationShareBudget]
    push_cast
    ring
  have hstock (i : ι) : (squarePhysicalState τ η 0 0 x).shares i ≤ R/η := by
    change 0+Real.sqrt (2*η*x i)/η ≤ R/η
    rw [zero_add,hsx]
    apply (div_le_div_iff_of_pos_right hη).mpr
    have hPi := (Finset.single_le_sum (fun j _ => sq_nonneg (P j)) (Finset.mem_univ i)).trans hbound
    nlinarith [hP i]
  have hh := severePrefix_append F ρ η hη τ τ P Q I 0 M V J _ _ (R/η) hp arc rfl
    (funext hsx) rfl (funext hsy) (arc.recovery_zero_of_equal_time rfl) hM' hV' hstock (by positivity)
  simpa only [Pi.zero_apply,add_zero] using hh

theorem severePrefix_continuous_piece (F ρ η : ℝ) (hη : 0 < η)
    (m : PhysicalContinuousBVPiece (completePairedEdges (ι := ι)))
    (hF : m.F = fun _ => F) (hρ : m.rho = fun _ => ρ) (hg : m.response = fun _ => constantResponse η hη)
    (hBV : ∀ i, BoundedVariationOn (m.shares · i) (Icc m.a m.b))
    (I : ι → ℝ) (M V J M' V' J' : ℝ)
    (hp : SeverePrefix F ρ η hη m.a (m.prices m.a) I M V J)
    (hM : (∑ e,(m.execution.cumulative e m.b-m.execution.cumulative e m.a)) ≤ M')
    (hV : ∀ i,actualNegativeVariation (m.shares · i) m.a m.b ≤ V')
    (hJ : ∀ i,m.shares m.a i ≤ J') (hJ' : 0 ≤ J') :
    SeverePrefix F ρ η hη m.b (m.prices m.b) (fun i => I i+
      ∫ u in m.a..m.b,m.prices u i*(m.prices u i-F)/η) (M+M') (V+V') (J+J') := by
  let step := OriginalPhysicalStep.continuous m hF hρ hg hBV
  let arc := OriginalPhysicalReachable.append (.refl _) step
  apply severePrefix_append F ρ η hη m.a m.b _ _ I _ M V J M' V' J' hp arc rfl rfl rfl rfl
  · intro i
    simp [arc,step,OriginalPhysicalReachable.recoveryIntegral,OriginalPhysicalStep.recoveryIntegral,constantResponse]
  · simpa only [arc,step,OriginalPhysicalReachable.pairedTurnover,OriginalPhysicalStep.pairedTurnover,zero_add] using hM
  · intro i
    simpa only [arc,step,OriginalPhysicalReachable.shareSales,OriginalPhysicalStep.shareSales,zero_add] using hV i
  · exact hJ
  · exact hJ'

set_option maxHeartbeats 800000 in
theorem severePrefix_one_direction (hub : ι) (F ρ η H T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hH : 0 < H) (hHn : H ≤ Real.sqrt (Fintype.card ι)) (hT : 0 < T)
    (u : ι → ℝ) (hu : ∀ i,0 < u i) (hun : ∑ i,(u i)^2 = 1) (huH : ∑ i,u i = H)
    (a c : ℝ) (ha : a ∈ Icc 0 T) (hc : c ∈ Icc 0 T) (hac : a ≤ c)
    (I : ι → ℝ) (M V J : ℝ)
    (hp : SeverePrefix F ρ η hη a (fun _ => severeRadius F ρ (Fintype.card ι) H a/Real.sqrt (Fintype.card ι)) I M V J) :
    SeverePrefix F ρ η hη c (fun _ => severeRadius F ρ (Fintype.card ι) H c/Real.sqrt (Fintype.card ι))
      (fun i => I i+∫ t in a..c,(u i*severeRadius F ρ (Fintype.card ι) H t)*
        (u i*severeRadius F ρ (Fintype.card ι) H t-F)/η)
      (M+(2*severeRotationDollarBudget (ι := ι) η (F*Real.sqrt (Fintype.card ι))+
        severeDollarRateBudget F ρ η (Fintype.card ι) (Fintype.card ι)*(c-a)))
      (V+(2*severeRotationShareBudget (ι := ι) η (F*Real.sqrt (Fintype.card ι))+
        severeShareRateBudget F ρ η (Fintype.card ι)*(c-a)))
      (J+(2*(F*Real.sqrt (Fintype.card ι)/η)+1+2*severeShareRateBudget F ρ η (Fintype.card ι)*T)) := by
  have hn : (2:ℝ) ≤ Fintype.card ι := by exact_mod_cast hN
  let R := severeRadius F ρ (Fintype.card ι) H
  let Rmax := F*Real.sqrt (Fintype.card ι)
  have hroot : 0 < Real.sqrt (Fintype.card ι : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hRmax : 0 < Rmax := mul_pos hF hroot
  have hRP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < R t := (mul_pos hF hH).trans_le
    (severe_radius_bounds F ρ (Fintype.card ι) H t hF hρ.le hH hHn ht.1).1
  have hRbound (t : ℝ) (ht : t ∈ Icc 0 T) : (R t)^2 ≤ Rmax^2 := by
    have hh := (severe_radius_bounds F ρ (Fintype.card ι) H t hF hρ.le hH hHn ht.1).2
    exact sq_le_sq₀ (hRP t ht).le hRmax.le |>.mpr hh
  obtain ⟨m,hma,hmb,hmF,hmρ,hmg,hmS,hmL,hmBV,hmM,hmV,hmJ⟩ :=
    severe_radial_uniform_inventory_piece hub F ρ η (Fintype.card ι) H T hF hρ hη hn hH hHn hT u hu hun huH
  have hunit (t : ℝ) : ∑ i,(u i*R t)^2 = (R t)^2 := by
    simp_rw [mul_pow];rw [←Finset.sum_mul,hun,one_mul]
  have hmaP (i : ι) : 0 < m.prices a i := by rw [hmS];exact mul_pos (hu i) (hRP a ha)
  have hmcP (i : ι) : 0 < m.prices c i := by rw [hmS];exact mul_pos (hu i) (hRP c hc)
  have hstart := severePrefix_transport hub F ρ η a Rmax hF hη hRmax _ (m.prices a) I
    (fun _ => div_pos (hRP a ha) hroot) hmaP
    (by rw [hmS,sharp_isotropic_square_sum _ (by omega),hunit])
    (by rw [sharp_isotropic_square_sum _ (by omega)];exact hRbound a ha) M V J hp
  let q := restrictPhysicalPiece m a c (by rw [hma];exact ha.1) (by rw [hmb];exact hc.2) hac
  have hqBV (i : ι) : BoundedVariationOn (q.shares · i) (Icc q.a q.b) := by
    exact (hmBV i).mono (fun t ht => ⟨ha.1.trans ht.1,ht.2.trans hc.2⟩)
  have hVnon : 0 ≤ severeShareRateBudget F ρ η (Fintype.card ι) := by dsimp [severeShareRateBudget];positivity
  have hmid := severePrefix_continuous_piece F ρ η hη q hmF hmρ hmg hqBV I _ _ _
    (severeDollarRateBudget F ρ η (Fintype.card ι) (Fintype.card ι)*(c-a))
    (severeShareRateBudget F ρ η (Fintype.card ι)*(c-a))
    (1+2*severeShareRateBudget F ρ η (Fintype.card ι)*T) hstart
    (hmM a ha c hc hac) (hmV a ha c hc hac) (hmJ a ha) (by positivity)
  have hend := severePrefix_transport hub F ρ η c Rmax hF hη hRmax (m.prices c) _ _ hmcP
    (fun _ => div_pos (hRP c hc) hroot)
    (by rw [hmS,sharp_isotropic_square_sum _ (by omega),hunit])
    (by rw [hmS,hunit];exact hRbound c hc) _ _ _ hmid
  simp only [q,restrictPhysicalPiece,hmS] at hend
  convert hend using 1 <;> dsimp [R,Rmax] <;> ring

theorem severePrefix_sequence (F ρ η : ℝ) (hη : 0 < η) (N : ℕ)
    (τ : ℕ → ℝ) (Q : ℕ → ι → ℝ) (I : ℕ → ι → ℝ) (CM CV CJ : ℕ → ℝ)
    (hτ : τ 0 = 0) (hQ : Q 0 = fun _ => F) (hCM : CM 0 = 0) (hCV : CV 0 = 0) (hCJ : CJ 0 = 0)
    (hstep : ∀ k < N, ∀ J : ι → ℝ, SeverePrefix F ρ η hη (τ k) (Q k) J (CM k) (CV k) (CJ k) →
      SeverePrefix F ρ η hη (τ (k+1)) (Q (k+1)) (fun i => J i+I k i) (CM (k+1)) (CV (k+1)) (CJ (k+1))) :
    SeverePrefix F ρ η hη (τ N) (Q N) (fun i => ∑ k ∈ Finset.range N,I k i) (CM N) (CV N) (CJ N) := by
  have hall : ∀ k ≤ N, SeverePrefix F ρ η hη (τ k) (Q k)
      (fun i => ∑ j ∈ Finset.range k,I j i) (CM k) (CV k) (CJ k) := by
    intro k
    induction k with
    | zero => intro _;simpa only [hτ,hQ,hCM,hCV,hCJ,Finset.range_zero,Finset.sum_empty] using severePrefix_zero (ι := ι) F ρ η hη
    | succ k ih =>
      intro hk
      have hh := hstep k (by omega) _ (ih (by omega))
      simpa only [Finset.sum_range_succ] using hh
  exact hall N le_rfl

set_option maxHeartbeats 800000 in
theorem severePrefix_symmetric_prefix (comp : ι) (F ρ η c b T : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hc : 0 < c) (hb : 0 < b) (hT : 0 < T)
    (hac : c < severeHigh (Fintype.card ι) c b)
    (hnorm : (severeHigh (Fintype.card ι) c b)^2+((Fintype.card ι : ℝ)-2)*c^2+b^2 = 1)
    (hH : 0 < severeDirectionSum (Fintype.card ι) c b)
    (hHn : severeDirectionSum (Fintype.card ι) c b ≤ Real.sqrt (Fintype.card ι))
    (hW : 1 < (severeHigh (Fintype.card ι) c b+c)*severeDirectionSum (Fintype.card ι) c b) :
    ∃ I : ℝ, SeverePrefix F ρ η hη T
      (fun _ : ι => severeRadius F ρ (Fintype.card ι) (severeDirectionSum (Fintype.card ι) c b) T/Real.sqrt (Fintype.card ι))
      (fun i => if i = comp then severeRecoveryPrimitive F ρ (Fintype.card ι)
        (severeDirectionSum (Fintype.card ι) c b) b T/η else I)
      (((Fintype.card ι-1 : ℕ) : ℝ)*(2*severeRotationDollarBudget (ι := ι) η (F*Real.sqrt (Fintype.card ι)))+
        severeDollarRateBudget F ρ η (Fintype.card ι) (Fintype.card ι)*T)
      (((Fintype.card ι-1 : ℕ) : ℝ)*(2*severeRotationShareBudget (ι := ι) η (F*Real.sqrt (Fintype.card ι)))+
        severeShareRateBudget F ρ η (Fintype.card ι)*T)
      (((Fintype.card ι-1 : ℕ) : ℝ)*(2*(F*Real.sqrt (Fintype.card ι)/η)+1+2*severeShareRateBudget F ρ η (Fintype.card ι)*T)) := by
  classical
  let Targets := {i : ι // i ≠ comp}
  let M := Fintype.card Targets
  let n : ℝ := Fintype.card ι
  let H := severeDirectionSum n c b
  let A := severeHigh n c b
  let R := severeRadius F ρ n H
  have hNtarget : M = Fintype.card ι-1 := by dsimp [M,Targets];simp
  have hM : 0 < M := by omega
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  let C := fun t => (c*R t)*(c*R t-F)
  let B := fun t => (b*R t)*(b*R t-F)
  let W := fun t => (A-c)*R t*((A+c)*R t-F)
  have hRC : Continuous R := continuous_iff_continuousAt.mpr (fun t => (severeRadius_derivative F ρ n H t).continuousAt)
  have hCC : Continuous C := by dsimp [C];fun_prop
  have hBC : Continuous B := by dsimp [B];fun_prop
  have hWC : Continuous W := by dsimp [W];fun_prop
  have hWP (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < W t := by
    have hR := (severe_radius_bounds F ρ n H t hF hρ.le hH hHn ht.1).1
    have hRp : 0 < R t := (mul_pos hF hH).trans_le hR
    have hAc : 0 < A+c := by dsimp [A] at *;linarith
    have hmul := mul_le_mul_of_nonneg_left hR hAc.le
    have hlast : 0 < (A+c)*R t-F := by
      have hh := mul_lt_mul_of_pos_left hW hF
      dsimp [A,H] at *
      nlinarith
    exact mul_pos (mul_pos (sub_pos.mpr hac) hRp) hlast
  obtain ⟨cuts,hcuts,hmono,hcut0,hcutM,hcutI⟩ := exists_equal_weight_interval_partition W T hT hWC.continuousOn hWP M hM
  let τ := fun k : ℕ => if hk : k ≤ M then cuts ⟨k,Nat.lt_succ_of_le hk⟩ else T
  have hτ0 : τ 0 = 0 := by simpa only [τ,dif_pos (Nat.zero_le M)] using hcut0
  have hτM : τ M = T := by simpa only [τ,dif_pos (le_refl M)] using hcutM
  have hτmem (k : ℕ) (hk : k ≤ M) : τ k ∈ Icc 0 T := by
    dsimp [τ];rw [dif_pos hk];exact hcuts _
  let e := Fintype.equivFin Targets
  let index := fun i : ι => if hi : i ≠ comp then (e ⟨i,hi⟩).val else 0
  let WI := ∫ t in (0:ℝ)..T,W t
  let J := fun k i => if i = comp then (∫ t in τ k..τ (k+1),B t)/η else
    (∫ t in τ k..τ (k+1),C t)/η+if index i = k then WI/(η*M) else 0
  let Q := fun k (_ : ι) => R (τ k)/Real.sqrt n
  have hQ0 : Q 0 = fun _ => F := by
    funext i;dsimp [Q];rw [hτ0];dsimp [R,severeRadius]
    simp only [mul_zero,Real.exp_zero,mul_one,add_sub_cancel]
    field_simp
  let CM := fun k : ℕ => (k:ℝ)*(2*severeRotationDollarBudget (ι := ι) η (F*Real.sqrt n))+
    severeDollarRateBudget F ρ η n (Fintype.card ι)*(τ k)
  let CV := fun k : ℕ => (k:ℝ)*(2*severeRotationShareBudget (ι := ι) η (F*Real.sqrt n))+
    severeShareRateBudget F ρ η n*(τ k)
  let CJ := fun k : ℕ => (k:ℝ)*(2*(F*Real.sqrt n/η)+1+2*severeShareRateBudget F ρ η n*T)
  have hstep (k : ℕ) (hk : k < M) (I : ι → ℝ) (hp : SeverePrefix F ρ η hη (τ k) (Q k) I (CM k) (CV k) (CJ k)) :
      SeverePrefix F ρ η hη (τ (k+1)) (Q (k+1)) (fun i => I i+J k i) (CM (k+1)) (CV (k+1)) (CJ (k+1)) := by
    let j : Fin M := ⟨k,hk⟩
    let center : Targets := e.symm j
    let u := severeAssemblyDirection A c b comp center
    have hu (i : ι) : 0 < u i := by
      dsimp [u,severeAssemblyDirection];split
      · exact hb
      · split
        · exact hc.trans hac
        · exact hc
    have hun : ∑ i,(u i)^2 = 1 := by rw [severeAssemblyDirection_square_sum _ _ _ _ _ center.property];exact hnorm
    have huH : ∑ i,u i = H := by rw [severeAssemblyDirection_sum _ _ _ _ _ center.property];rfl
    have hleft : τ k = cuts j.castSucc := by simp [τ,j,Nat.le_of_lt hk]
    have hright : τ (k+1) = cuts j.succ := by simp [τ,j,Nat.succ_le_of_lt hk]
    have hacut : τ k ≤ τ (k+1) := by
      rw [hleft,hright];exact (hmono (show j.castSucc < j.succ by exact_mod_cast Nat.lt_succ_self k)).le
    have hWI : (∫ t in τ k..τ (k+1),W t) = WI/M := by rw [hleft,hright];exact hcutI j
    have hrec (i : ι) : (∫ t in τ k..τ (k+1),(u i*R t)*(u i*R t-F)/η) = J k i := by
      by_cases hi : i = comp
      · subst i
        simp only [u,severeAssemblyDirection,ite_true,J,intervalIntegral.integral_div,B]
      · have heq : i = (center : ι) ↔ index i = k := by
          dsimp [index];rw [dif_pos hi]
          constructor
          · intro hh
            have hh' : (⟨i,hi⟩ : Targets) = center := Subtype.ext hh
            rw [hh']
            exact congrArg Fin.val (e.apply_symm_apply j)
          · intro hh
            have hh' : e ⟨i,hi⟩ = j := Fin.ext hh
            exact congrArg Subtype.val (e.injective (hh'.trans (e.apply_symm_apply j).symm))
        have hh := sharp_direction_interval_recovery F η A c R (center : ι) i (τ k) (τ (k+1)) (WI/M) hRC hWI
        have huEq : u i = sharpDirection A c (center : ι) i := by simp [u,severeAssemblyDirection,sharpDirection,hi]
        rw [huEq]
        dsimp [J]
        simp only [if_neg hi]
        simpa only [C,heq,div_div,mul_comm] using hh
    have hh := severePrefix_one_direction comp F ρ η H T hF hρ hη hN hH hHn hT u hu hun huH
      (τ k) (τ (k+1)) (hτmem k hk.le) (hτmem (k+1) (by omega)) hacut I (CM k) (CV k) (CJ k) hp
    change SeverePrefix F ρ η hη (τ (k+1)) (Q (k+1))
      (fun i => I i+∫ t in τ k..τ (k+1),(u i*R t)*(u i*R t-F)/η) _ _ _ at hh
    simp only [hrec] at hh
    convert hh using 1 <;> dsimp [CM,CV,CJ,n] <;> push_cast <;> ring
  have hpref := severePrefix_sequence F ρ η hη M τ Q J CM CV CJ hτ0 hQ0
    (by simp [CM,hτ0]) (by simp [CV,hτ0]) (by simp [CJ]) hstep
  have hBsum : (∑ k ∈ Finset.range M,∫ t in τ k..τ (k+1),B t) = ∫ t in (0:ℝ)..T,B t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := B) (a := τ) (n := M)
      (fun k _ => hBC.intervalIntegrable (τ k) (τ (k+1)))
    simpa only [hτ0,hτM] using hh
  have hCsum : (∑ k ∈ Finset.range M,∫ t in τ k..τ (k+1),C t) = ∫ t in (0:ℝ)..T,C t := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := C) (a := τ) (n := M)
      (fun k _ => hCC.intervalIntegrable (τ k) (τ (k+1)))
    simpa only [hτ0,hτM] using hh
  have hsum (i : ι) : (∑ k ∈ Finset.range M,J k i) =
      if i = comp then severeRecoveryPrimitive F ρ n H b T/η else (∫ t in (0:ℝ)..T,C t)/η+WI/(η*M) := by
    by_cases hi : i = comp
    · simp only [J,if_pos hi,←Finset.sum_div,hBsum]
      rw [severe_recovery_integral F ρ n H b T hρ.ne']
    · have hidx : index i < M := by dsimp [index];rw [dif_pos hi];exact (e ⟨i,hi⟩).isLt
      simp only [J,if_neg hi,Finset.sum_add_distrib,←Finset.sum_div,hCsum]
      simp [hidx]
  refine ⟨(∫ t in (0:ℝ)..T,C t)/η+WI/(η*M),?_⟩
  simp only [Q,hτM,hsum,CM,CV,CJ] at hpref
  simpa only [hNtarget] using hpref


def severeTotalDollarBudget (F ρ η T : ℝ) : ℝ :=
  ((2*(Fintype.card ι-1)+1 : ℕ) : ℝ)*severeRotationDollarBudget (ι := ι) η (F*Real.sqrt (Fintype.card ι))+
    severeDollarRateBudget F ρ η (Fintype.card ι) (Fintype.card ι)*T

def severeTotalShareBudget (F ρ η T : ℝ) : ℝ :=
  ((2*(Fintype.card ι-1)+1 : ℕ) : ℝ)*severeRotationShareBudget (ι := ι) η (F*Real.sqrt (Fintype.card ι))+
    severeShareRateBudget F ρ η (Fintype.card ι)*T

def severeTotalInventoryBudget (F ρ η T : ℝ) : ℝ :=
  ((Fintype.card ι-1 : ℕ) : ℝ)*(2*(F*Real.sqrt (Fintype.card ι)/η)+1+2*severeShareRateBudget F ρ η (Fintype.card ι)*T)+
    F*Real.sqrt (Fintype.card ι)/η

set_option maxHeartbeats 800000 in
theorem severeAssembly_bounded_closed_path (comp : ι) (F ρ η c b T eps : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι)
    (hc : 0 < c) (hb : 0 < b) (hT : 0 < T) (heps : 0 < eps)
    (hac : c < severeHigh (Fintype.card ι) c b)
    (hnorm : (severeHigh (Fintype.card ι) c b)^2+((Fintype.card ι : ℝ)-2)*c^2+b^2 = 1)
    (hH : 0 < severeDirectionSum (Fintype.card ι) c b)
    (hHn : severeDirectionSum (Fintype.card ι) c b ≤ Real.sqrt (Fintype.card ι))
    (hW : 1 < (severeHigh (Fintype.card ι) c b+c)*severeDirectionSum (Fintype.card ι) c b)
    (hrad : ((Fintype.card ι : ℝ)-1)*eps^2 <
      (severeRadius F ρ (Fintype.card ι) (severeDirectionSum (Fintype.card ι) c b) T)^2)
    (hledger : severeCompensatorLedger F ρ η (Fintype.card ι)
      (severeDirectionSum (Fintype.card ι) c b) b T eps = 0) :
    ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
      (fun _ => constantResponse η hη) completePairedEdges,
      P.terminal.time = T ∧ (∀ i, i ≠ comp → P.terminal.prices i = eps) ∧
      P.terminal.prices comp = Real.sqrt
        ((severeRadius F ρ (Fintype.card ι) (severeDirectionSum (Fintype.card ι) c b) T)^2-
          ((Fintype.card ι : ℝ)-1)*eps^2) ∧
      P.trace.pairedTurnover ≤ severeTotalDollarBudget (ι := ι) F ρ η T ∧
      (∀ i,P.trace.shareSales i ≤ severeTotalShareBudget (ι := ι) F ρ η T) ∧
      (∀ i,P.initial.shares i ≤ severeTotalInventoryBudget (ι := ι) F ρ η T) := by
  classical
  let n : ℝ := Fintype.card ι
  let H := severeDirectionSum n c b
  let R := severeRadius F ρ n H T
  let C := Real.sqrt (R^2-(n-1)*eps^2)
  let Q := sharpDirection C eps comp
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  have hC : 0 < C := Real.sqrt_pos.mpr (sub_pos.mpr hrad)
  have hCsq : C^2 = R^2-(n-1)*eps^2 := Real.sq_sqrt (sub_pos.mpr hrad).le
  obtain ⟨I,hpref⟩ := severePrefix_symmetric_prefix comp F ρ η c b T hF hρ hη hN hc hb hT hac hnorm hH hHn hW
  have hR : 0 < R := (mul_pos hF hH).trans_le
    (severe_radius_bounds F ρ n H T hF hρ.le hH hHn hT.le).1
  have hQP (i : ι) : 0 < Q i := by dsimp [Q,sharpDirection];split <;> assumption
  have hQsum : ∑ i,(Q i)^2 = R^2 := by
    rw [sharpDirection_square_sum]
    dsimp [n] at hCsq ⊢
    linarith
  let Rmax := F*Real.sqrt n
  have hRmax : 0 < Rmax := mul_pos hF (Real.sqrt_pos.mpr (by linarith))
  have hRbound : R^2 ≤ Rmax^2 := by
    have hh := (severe_radius_bounds F ρ n H T hF hρ.le hH hHn hT.le).2
    exact (sq_le_sq₀ hR.le hRmax.le).mpr hh
  have hprefix := severePrefix_transport comp F ρ η T Rmax hF hη hRmax _ Q _
    (fun _ => div_pos hR (Real.sqrt_pos.mpr (by linarith : 0 < n))) hQP
    (by rw [sharp_isotropic_square_sum _ (by omega),hQsum])
    (by rw [sharp_isotropic_square_sum _ (by omega)];exact hRbound) _ _ _ hpref
  obtain ⟨s,t,path,hs0,hsP,hsH,hsL,htT,htP,hI,hM,hV,hJ⟩ := hprefix
  have hprices (i : ι) : t.prices i = Q i := congrFun htP i
  have hcoord (i : ι) : coordinate F (constantResponse η hη).impact (t.prices i) =
      ((t.prices i)^2-F^2)/(2*η) := by
    have hh := constantCoordinate_eq_integral F η hF hη (show t.prices i ∈ positivePrices by rw [hprices];exact hQP i)
    exact hh.symm
  have hnormal (i : ι) : t.dollars i = ((t.prices i)^2-F^2)/(2*η)+ρ*path.recoveryIntegral i := by
    have hh := path.recovery_normal_form i
    simp only [hsP,hsL,Pi.zero_apply,coordinate_at_benchmark,sub_zero,hcoord] at hh
    linarith
  have hcomp : t.dollars comp = 0 := by
    rw [hnormal,hI,hprices]
    simp only [Q,sharpDirection,ite_true]
    rw [hCsq]
    dsimp [severeCompensatorLedger] at hledger
    dsimp [R,H,n] at *
    convert hledger using 1 <;> ring
  let E := (eps^2-F^2)/(2*η)+ρ*I
  have hall (i : ι) : t.dollars i = if i = comp then 0 else E := by
    by_cases hi : i = comp
    · subst i;simpa using hcomp
    · rw [hnormal,hI,hprices]
      simp only [if_neg hi,Q,sharpDirection]
      rfl
  have hsum := path.dollar_sum_preserved
  simp only [hsL,Pi.zero_apply,Finset.sum_const_zero] at hsum
  have hsum' : ∑ i,t.dollars i = (n-1)*E := by
    simp_rw [hall]
    have hh := sharpDirection_sum (ι := ι) 0 E comp
    simpa only [sharpDirection,zero_add] using hh
  rw [hsum'] at hsum
  have hE : E = 0 := by nlinarith
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
    initial_dollars := fun i => congrFun hsL i
    terminal_dollars := fun i => by rw [hall,hE];split <;> rfl }
  refine ⟨P,htT,?_,?_,?_,?_,?_⟩
  · intro i hi
    exact (hprices i).trans (by simp [Q,sharpDirection,hi])
  · exact (hprices comp).trans (by simp [Q,sharpDirection];rfl)
  · convert hM using 1
    dsimp [severeTotalDollarBudget,Rmax,n]
    push_cast
    ring
  · intro i
    convert hV i using 1
    dsimp [severeTotalShareBudget,Rmax,n]
    push_cast
    ring
  · intro i
    exact hJ i

set_option maxHeartbeats 800000 in
theorem severeAssembly_uniform_original_family (comp : ι) (F ρ η : ℝ)
    (hF : 0 < F) (hρ : 0 < ρ) (hη : 0 < η) (hN : 2 ≤ Fintype.card ι) :
    ∃ T eps0 M0 H0 J0 : ℝ, 0 < T ∧ 0 < eps0 ∧ 0 ≤ M0 ∧ 0 ≤ H0 ∧ 0 ≤ J0 ∧
      ∀ eps : ℝ, 0 < eps → eps < eps0 →
      ∃ P : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ)
        (fun _ => constantResponse η hη) completePairedEdges,
        P.terminal.time = T ∧ (∀ i, i ≠ comp → P.terminal.prices i = eps) ∧
        P.terminal.prices comp ≤ F*Real.sqrt (Fintype.card ι) ∧
        P.trace.pairedTurnover ≤ M0 ∧ (∀ i,P.trace.shareSales i ≤ H0) ∧ (∀ i,P.initial.shares i ≤ J0) := by
  let n : ℝ := Fintype.card ι
  have hn : (2:ℝ) ≤ n := by dsimp [n];exact_mod_cast hN
  obtain ⟨c,T,eps0,hc,hcn,hcs,hT,heps0,hfamily⟩ := severe_parameter_family F ρ η n hF hρ hη hn
  let eps1 := min eps0 (F/(2*Real.sqrt n))
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by linarith)
  have heps1 : 0 < eps1 := lt_min heps0 (by positivity)
  have hM0 : 0 ≤ severeTotalDollarBudget (ι := ι) F ρ η T := by
    dsimp [severeTotalDollarBudget,severeRotationDollarBudget,severeDollarRateBudget]
    positivity
  have hH0 : 0 ≤ severeTotalShareBudget (ι := ι) F ρ η T := by
    dsimp [severeTotalShareBudget,severeRotationShareBudget,severeShareRateBudget]
    positivity
  have hJ0 : 0 ≤ severeTotalInventoryBudget (ι := ι) F ρ η T := by
    dsimp [severeTotalInventoryBudget,severeShareRateBudget]
    positivity
  refine ⟨T,eps1,severeTotalDollarBudget (ι := ι) F ρ η T,severeTotalShareBudget (ι := ι) F ρ η T,
    severeTotalInventoryBudget (ι := ι) F ρ η T,hT,heps1,hM0,hH0,hJ0,?_⟩
  intro eps hep hepb
  have hepa : eps < eps0 := (lt_min_iff.mp hepb).1
  have hepsmall : eps < F/(2*Real.sqrt n) := (lt_min_iff.mp hepb).2
  obtain ⟨b,hb,hledger,hba,hnorm,hH,hHn,hW⟩ := hfamily eps hep.le hepa
  let A := severeHigh n c b
  let H := severeDirectionSum n c b
  let R := severeRadius F ρ n H T
  have hAc : (n-2)*c^2 ≤ 1/20000 := by
    have hD : (n-2)*c ≤ 1/100 := by nlinarith
    nlinarith only [mul_le_mul_of_nonneg_right hD hc.le,hcs]
  have hA : 9/10 < A := by
    have hAp : 0 < A := hb.1.trans hba
    have hbq : b^2 < 1/25 := by nlinarith [hb.1,hb.2]
    dsimp [A] at *
    nlinarith only [hnorm,hAc,hbq,hAp]
  have hac : c < A := by linarith
  have hHA : A ≤ H := by
    have hh := mul_nonneg (by linarith : 0 ≤ n-2) hc.le
    dsimp [H,severeDirectionSum,A]
    linarith [hb.1]
  have hR : (9/10)*F < R := by
    have hh := (severe_radius_bounds F ρ n H T hF hρ.le hH hHn hT.le).1
    have haF := mul_lt_mul_of_pos_left (hA.trans_le hHA) hF
    dsimp [R]
    nlinarith only [hh,haF]
  have hεsqrt : eps*Real.sqrt n < F/2 := by
    have hh := (lt_div_iff₀ (by positivity : 0 < 2*Real.sqrt n)).mp hepsmall
    nlinarith
  have hεsq : n*eps^2 < F^2/4 := by
    have hh := mul_self_lt_mul_self (by positivity : 0 ≤ eps*Real.sqrt n) hεsqrt
    have hs := Real.sq_sqrt (by linarith : 0 ≤ n)
    nlinarith
  have hrad : (n-1)*eps^2 < R^2 := by
    have hRp : 0 < R := (mul_pos (by norm_num) hF).trans hR
    nlinarith only [hεsq,hR,hRp,hF,sq_nonneg eps]
  obtain ⟨P,hPT,hPS,hPC,hM,hV,hJ⟩ := severeAssembly_bounded_closed_path comp F ρ η c b T eps hF hρ hη hN hc hb.1 hT hep
    hac hnorm hH hHn hW hrad hledger
  refine ⟨P,hPT,hPS,?_,hM,hV,hJ⟩
  rw [hPC]
  have hRp : 0 < R := (mul_pos (by norm_num) hF).trans hR
  calc
    Real.sqrt (R^2-(n-1)*eps^2) ≤ Real.sqrt (R^2) :=
      Real.sqrt_le_sqrt (sub_le_self _ (mul_nonneg (by linarith) (sq_nonneg eps)))
    _ = R := Real.sqrt_sq hRp.le
    _ ≤ F*Real.sqrt n := (severe_radius_bounds F ρ n H T hF hρ.le hH hHn hT.le).2


end MarketCrash



















