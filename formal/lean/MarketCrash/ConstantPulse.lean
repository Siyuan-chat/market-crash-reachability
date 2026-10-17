import MarketCrash.PhysicalPulseConstruction
import MarketCrash.ResponseFamilies
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section
namespace MarketCrash
open Set

def constantPulsePrice (P eta B a : ℝ) : ℝ := Real.sqrt (P^2+2*eta*a*B)

theorem constantPulsePrice_derivative (P eta B a : ℝ)
    (hp : 0 < P^2+2*eta*a*B) :
    HasDerivAt (constantPulsePrice P eta B)
      (eta/constantPulsePrice P eta B a*B) a := by
  have hh := (Real.hasDerivAt_sqrt hp.ne').comp a
    (((hasDerivAt_id a).const_mul (2*eta)).mul_const B |>.const_add (P^2))
  convert hh using 1 <;> dsimp [constantPulsePrice] <;>
    field_simp [(Real.sqrt_pos.mpr hp).ne'] <;> ring

def constantOriginalEdgePulse {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta) (P H L : ι → ℝ)
    (hp : ∀ a ∈ Icc 0 z, ∀ i, 0 < (P i)^2+2*eta*a*pairedMatrix edges i e)
    (hH : ∀ i, P i/eta ≤ H i) : OriginalDollarParameterPulse edges := by
  let S := fun a i => constantPulsePrice (P i) eta (pairedMatrix edges i e) a
  have hs : ∀ i, Continuous (fun a => S a i) := by
    intro i
    dsimp [S,constantPulsePrice]
    fun_prop
  have hpos : ∀ a ∈ Icc 0 z, ∀ i, 0 < S a i :=
    fun a ha i => Real.sqrt_pos.mpr (hp a ha i)
  have hd : ∀ a ∈ Ioo 0 z, ∀ i, HasDerivAt (fun a => S a i)
      (eta/S a i*pairedMatrix edges i e) a :=
    fun a ha i => constantPulsePrice_derivative _ _ _ _ (hp a (Ioo_subset_Icc_self ha) i)
  refine {
    physicalTime := t
    edge := e
    z := z
    z_positive := hz
    F := fun _ => F
    response := fun _ => constantResponse eta hη
    benchmark_positive := fun _ => hF
    prices := S
    shares := fun a i => H i+(S a i-P i)/eta
    dollarLedger := fun a i => L i+a*pairedMatrix edges i e
    continuous_prices := fun i => (hs i).continuousOn
    continuous_shares := fun i => (continuous_const.add (((hs i).sub continuous_const).div_const eta)).continuousOn
    continuous_ledgers := fun i => by fun_prop
    positive_prices := hpos
    no_short_sales := ?_
    price_flow := hd
    share_flow := ?_
    ledger_flow := fun a _ i => by simpa using ((hasDerivAt_id a).mul_const (pairedMatrix edges i e)).const_add (L i) }
  · intro a ha i
    have hh := sub_nonneg.mpr (hH i)
    have hs := div_nonneg (hpos a ha i).le hη.le
    rw [sub_div]
    linarith
  · intro a ha i
    convert (((hd a ha i).sub_const (P i)).div_const eta).const_add (H i) using 1
    field_simp [hη.ne',(hpos a (Ioo_subset_Icc_self ha) i).ne'] <;> ring

theorem constantPulsePrice_positive_between (P eta B z : ℝ)
    (hP : 0 < P) (hend : 0 < P^2+2*eta*z*B) :
    ∀ a ∈ Icc 0 z, 0 < P^2+2*eta*a*B := by
  intro a ha
  by_cases h : 0 ≤ 2*eta*B
  · have hh := mul_nonneg ha.1 h
    nlinarith [sq_pos_of_pos hP]
  · have hh := mul_le_mul_of_nonpos_right ha.2 (le_of_not_ge h)
    nlinarith

theorem constantPulsePrice_start (P eta B : ℝ) (hP : 0 < P) :
    constantPulsePrice P eta B 0 = P := by
  simp only [constantPulsePrice,mul_zero,zero_mul,add_zero]
  exact Real.sqrt_sq hP.le

theorem constantPulsePrice_end (P Q eta B z : ℝ) (hQ : 0 < Q)
    (he : P^2+2*eta*z*B = Q^2) : constantPulsePrice P eta B z = Q := by
  rw [constantPulsePrice,he,Real.sqrt_sq hQ.le]

def squarePhysicalState {ι : Type*} (t eta : ℝ) (H L x : ι → ℝ) : PhysicalMarketState ι :=
  ⟨t,fun i => Real.sqrt (2*eta*x i),fun i => H i+Real.sqrt (2*eta*x i)/eta,fun i => L i+x i⟩

theorem square_single_edge_reachable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (e : κ) (z : ℝ) (hz : 0 < z)
    (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta) (rho H L x : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) (hx : ∀ i, 0 < x i)
    (hx' : ∀ i, 0 < x i+z*pairedMatrix edges i e) :
    Nonempty (OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) edges
      (squarePhysicalState t eta H L x)
      (squarePhysicalState t eta H L (fun i => x i+z*pairedMatrix edges i e))) := by
  let P := fun i => Real.sqrt (2*eta*x i)
  have hP : ∀ i, 0 < P i := fun i => Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) hη) (hx i))
  have hP2 : ∀ i, (P i)^2 = 2*eta*x i := fun i => Real.sq_sqrt (mul_pos (mul_pos (by norm_num) hη) (hx i)).le
  have hend : ∀ i, 0 < (P i)^2+2*eta*z*pairedMatrix edges i e := by
    intro i
    rw [hP2]
    nlinarith [mul_pos hη (hx' i)]
  let p := constantOriginalEdgePulse edges e z hz t F eta hF hη P
    (fun i => H i+P i/eta) (fun i => L i+x i)
    (fun a ha i => constantPulsePrice_positive_between _ _ _ _ (hP i) (hend i) a ha)
    (fun i => le_add_of_nonneg_left (hH i))
  have he : ∀ a i, p.prices a i = Real.sqrt (2*eta*(x i+a*pairedMatrix edges i e)) := by
    intro a i
    change constantPulsePrice (P i) eta (pairedMatrix edges i e) a = _
    rw [constantPulsePrice,hP2]
    congr 1
    ring
  have hS : ∀ a i, p.shares a i = H i+Real.sqrt (2*eta*(x i+a*pairedMatrix edges i e))/eta := by
    intro a i
    change H i+P i/eta+(p.prices a i-P i)/eta = _
    rw [he]
    ring
  have hstart : (⟨p.physicalTime,p.prices 0,p.shares 0,p.dollarLedger 0⟩ : PhysicalMarketState ι) =
      squarePhysicalState t eta H L x := by
    simp only [squarePhysicalState]
    congr 1
    · funext i;simpa only [zero_mul,add_zero] using he 0 i
    · funext i;simpa only [zero_mul,add_zero] using hS 0 i
    · funext i;change L i+x i+0*pairedMatrix edges i e = L i+x i;ring
  have hfinish : (⟨p.physicalTime,p.prices p.z,p.shares p.z,p.dollarLedger p.z⟩ : PhysicalMarketState ι) =
      squarePhysicalState t eta H L (fun i => x i+z*pairedMatrix edges i e) := by
    simp only [squarePhysicalState]
    congr 1
    · funext i;exact he z i
    · funext i;exact hS z i
    · funext i;change L i+x i+z*pairedMatrix edges i e = L i+(x i+z*pairedMatrix edges i e);ring
  have hs := p.toOriginalStep rho
  rw [hstart,hfinish] at hs
  exact ⟨.append (.refl _) hs⟩

def squareSchedulePositive {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) : (ι → ℝ) → List (κ × ℝ) → Prop
  | x, [] => ∀ i, 0 < x i
  | x, c :: cs => (∀ i, 0 < x i) ∧ 0 < c.2 ∧
      squareSchedulePositive edges (fun i => x i+c.2*pairedMatrix edges i c.1) cs

theorem squareSchedulePositive_start {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (x : ι → ℝ) (cs : List (κ × ℝ))
    (h : squareSchedulePositive edges x cs) : ∀ i, 0 < x i := by
  cases cs with
  | nil => exact h
  | cons c cs => exact h.1

theorem square_schedule_reachable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (t F eta : ℝ) (hF : 0 < F) (hη : 0 < eta)
    (rho H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i)
    (cs : List (κ × ℝ)) (x : ι → ℝ) (hc : squareSchedulePositive edges x cs) :
    Nonempty (OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) edges
      (squarePhysicalState t eta H L x)
      (squarePhysicalState t eta H L (chartControlEndpoint edges x cs))) := by
  induction cs generalizing x with
  | nil => exact ⟨.refl _⟩
  | cons c cs ih =>
    obtain ⟨hx,hz,htail⟩ := hc
    obtain ⟨hs⟩ := square_single_edge_reachable edges c.1 c.2 hz t F eta hF hη rho H L x
      hH hx (squareSchedulePositive_start edges _ cs htail)
    obtain ⟨hr⟩ := ih (fun i => x i+c.2*pairedMatrix edges i c.1) htail
    exact ⟨original_reachable_trans hs hr⟩

end MarketCrash
