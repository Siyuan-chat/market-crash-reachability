import MarketCrash.SquareTransportation
import MarketCrash.WeightedPartition
import MarketCrash.SharpConstruction
import MarketCrash.OriginalPreconditioning

noncomputable section
namespace MarketCrash
open Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
variable {s t : PhysicalMarketState ι}

theorem OriginalPhysicalStep.recovery_zero_of_equal_time
    (h : OriginalPhysicalStep F rho g edges s t) (ht : s.time = t.time) (i : ι) :
    h.recoveryIntegral i = 0 := by
  cases h with
  | continuous m _ _ _ _ =>
    change m.a = m.b at ht
    dsimp [OriginalPhysicalStep.recoveryIntegral]
    rw [ht]
    simp
  | pulse p _ _ _ => rfl

theorem OriginalPhysicalReachable.recovery_zero_of_equal_time
    (h : OriginalPhysicalReachable F rho g edges s t) :
    s.time = t.time → ∀ i, h.recoveryIntegral i = 0 := by
  induction h with
  | refl => intro _ i;rfl
  | append previous step ih =>
    intro ht i
    have hp := previous.chronological
    have hq := step.chronological
    rw [OriginalPhysicalReachable.recoveryIntegral,ih (by linarith) i,
      step.recovery_zero_of_equal_time (by linarith) i,add_zero]

theorem original_reachable_trans_recovery {m : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m)
    (h' : OriginalPhysicalReachable F rho g edges m t) (i : ι) :
    (original_reachable_trans h h').recoveryIntegral i = h.recoveryIntegral i+h'.recoveryIntegral i := by
  induction h' with
  | refl => simp [original_reachable_trans,OriginalPhysicalReachable.recoveryIntegral]
  | append previous step ih =>
    simp only [original_reachable_trans,OriginalPhysicalReachable.recoveryIntegral] at ih ⊢
    rw [ih]
    ring

def sharpDirection (a b : ℝ) (j i : ι) : ℝ := if i = j then a else b

theorem sharpDirection_sum (a b : ℝ) (j : ι) :
    ∑ i, sharpDirection a b j i = a+((Fintype.card ι : ℝ)-1)*b := by
  have he : ∀ i, sharpDirection a b j i = b+(if i = j then a-b else 0) := by
    intro i
    by_cases hi : i = j <;> simp [sharpDirection,hi] <;> ring
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp
  ring

theorem sharpDirection_square_sum (a b : ℝ) (j : ι) :
    ∑ i, (sharpDirection a b j i)^2 = a^2+((Fintype.card ι : ℝ)-1)*b^2 := by
  simpa only [sharpDirection,ite_pow] using sharpDirection_sum (ι := ι) (a^2) (b^2) j

theorem sharp_recovery_density_split (a b R F : ℝ) (j i : ι) :
    (sharpDirection a b j i*R)*(sharpDirection a b j i*R-F) =
      (b*R)*(b*R-F)+(if i = j then (a-b)*R*((a+b)*R-F) else 0) := by
  by_cases hi : i = j <;> simp only [sharpDirection,hi,ite_true,ite_false] <;> ring

def physicalEconomicOffset (s : PhysicalMarketState ι) (H L : ι → ℝ) : PhysicalMarketState ι :=
  ⟨s.time,s.prices,fun i => H i+s.shares i,fun i => L i+s.dollars i⟩

def offsetEconomicPiece (m : PhysicalContinuousBVPiece edges) (H L : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) : PhysicalContinuousBVPiece edges :=
  { m with
    shares := fun t i => H i+m.shares t i
    dollarLedger := fun t i => L i+m.dollarLedger t i
    no_short_sales := fun t ht i => add_nonneg (hH i) (m.no_short_sales t ht i)
    physical_share_primitive := by
      intro i s hs t ht
      simpa only [add_sub_add_left_eq_sub] using m.physical_share_primitive i s hs t ht
    marginal_dollar_primitive := by
      intro i s hs t ht
      simpa only [add_sub_add_left_eq_sub] using m.marginal_dollar_primitive i s hs t ht }

def offsetEconomicPulse (p : OriginalFlowCompletedPulse edges) (H L : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) : OriginalFlowCompletedPulse edges :=
  { p with
    shares := fun t i => H i+p.shares t i
    dollarLedger := fun t i => L i+p.dollarLedger t i
    no_short_sales := fun t ht i => add_nonneg (hH i) (p.no_short_sales t ht i)
    physical_share_primitive := by
      intro i t ht
      simpa only [add_sub_add_left_eq_sub] using p.physical_share_primitive i t ht
    marginal_dollar_primitive := by
      intro i t ht
      simpa only [add_sub_add_left_eq_sub] using p.marginal_dollar_primitive i t ht }

def offsetPhysicalStep (h : OriginalPhysicalStep F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) :
    OriginalPhysicalStep F rho g edges (physicalEconomicOffset s H L) (physicalEconomicOffset t H L) := by
  cases h with
  | continuous m hF hr hg hv =>
    exact .continuous (offsetEconomicPiece m H L hH) hF hr hg (fun i =>
      ((LipschitzWith.const (H i)).add LipschitzWith.id).comp_boundedVariationOn (hv i))
  | pulse p hF hg hv =>
    exact .pulse (offsetEconomicPulse p H L hH) hF hg (fun i =>
      ((LipschitzWith.const (H i)).add LipschitzWith.id).comp_boundedVariationOn (hv i))

def offsetPhysicalTrace (h : OriginalPhysicalReachable F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) :
    OriginalPhysicalReachable F rho g edges (physicalEconomicOffset s H L) (physicalEconomicOffset t H L) := by
  induction h with
  | refl => exact .refl _
  | append previous step ih => exact .append ih (offsetPhysicalStep step H L hH)

theorem offsetPhysicalStep_recovery (h : OriginalPhysicalStep F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) (i : ι) :
    (offsetPhysicalStep h H L hH).recoveryIntegral i = h.recoveryIntegral i := by
  cases h <;> rfl

theorem offsetPhysicalTrace_recovery (h : OriginalPhysicalReachable F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) (i : ι) :
    (offsetPhysicalTrace h H L hH).recoveryIntegral i = h.recoveryIntegral i := by
  induction h with
  | refl => rfl
  | append previous step ih =>
    change (offsetPhysicalTrace previous H L hH).recoveryIntegral i+
      (offsetPhysicalStep step H L hH).recoveryIntegral i = _
    rw [ih,offsetPhysicalStep_recovery]
    rfl

def restrictPhysicalPiece (m : PhysicalContinuousBVPiece edges) (a b : ℝ)
    (ha : m.a ≤ a) (hb : b ≤ m.b) (hab : a ≤ b) : PhysicalContinuousBVPiece edges := by
  have hs : Icc a b ⊆ Icc m.a m.b := fun t ht => ⟨ha.trans ht.1,ht.2.trans hb⟩
  exact {m with
    a := a
    b := b
    time_order := hab
    continuous_execution := fun e => (m.continuous_execution e).mono hs
    continuous_prices := fun i => (m.continuous_prices i).mono hs
    positive_prices := fun t ht => m.positive_prices t (hs ht)
    no_short_sales := fun t ht => m.no_short_sales t (hs ht)
    physical_price_primitive := fun i s hs' t ht => m.physical_price_primitive i s (hs hs') t (hs ht)
    physical_share_primitive := fun i s hs' t ht => m.physical_share_primitive i s (hs hs') t (hs ht)
    marginal_dollar_primitive := fun i s hs' t ht => m.marginal_dollar_primitive i s (hs hs') t (hs ht) }

theorem common_recovery_dollars_closed [Nonempty ι]
    (F rho : ℝ) (g : Response) (S I : ℝ)
    (h : OriginalPhysicalReachable (fun _ : ι => F) (fun _ => rho) (fun _ => g) edges s t)
    (hs : ∀ i, s.prices i = F) (ht : ∀ i, t.prices i = S)
    (h0 : ∀ i, s.dollars i = 0) (hI : ∀ i, h.recoveryIntegral i = I) :
    ∀ i, t.dollars i = 0 := by
  have hall : ∀ i, t.dollars i = coordinate F g.impact S+rho*I := by
    intro i
    have hh := h.recovery_normal_form i
    simp only [hs,ht,h0,hI,coordinate_at_benchmark,sub_zero] at hh
    linarith
  have hsum := h.dollar_sum_preserved
  simp_rw [hall,h0] at hsum
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_zero] at hsum
  have hn : (0:ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hz : coordinate F g.impact S+rho*I = 0 := by nlinarith
  intro i
  rw [hall,hz]

def original_reachable_trans_eq {m1 m2 : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m1)
    (h' : OriginalPhysicalReachable F rho g edges m2 t) (hm : m1 = m2) :
    OriginalPhysicalReachable F rho g edges s t := by
  subst m2
  exact original_reachable_trans h h'

theorem original_reachable_trans_eq_recovery {m1 m2 : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m1)
    (h' : OriginalPhysicalReachable F rho g edges m2 t) (hm : m1 = m2) (i : ι) :
    (original_reachable_trans_eq h h' hm).recoveryIntegral i =
      h.recoveryIntegral i+h'.recoveryIntegral i := by
  subst m2
  exact original_reachable_trans_recovery h h' i

theorem concatenate_with_finite_inventory {m1 m2 : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m1)
    (h' : OriginalPhysicalReachable F rho g edges m2 t)
    (htime : m1.time = m2.time) (hprice : m1.prices = m2.prices) :
    ∃ H1 H2 L : ι → ℝ, (∀ i, 0 ≤ H1 i) ∧ (∀ i, 0 ≤ H2 i) ∧
      ∃ path : OriginalPhysicalReachable F rho g edges
        (physicalEconomicOffset s H1 (fun _ => 0)) (physicalEconomicOffset t H2 L),
        ∀ i, path.recoveryIntegral i = h.recoveryIntegral i+h'.recoveryIntegral i := by
  let H1 := fun i => max (m2.shares i-m1.shares i) 0
  let H2 := fun i => max (m1.shares i-m2.shares i) 0
  let L := fun i => m1.dollars i-m2.dollars i
  have hH1 : ∀ i, 0 ≤ H1 i := fun i => le_max_right _ _
  have hH2 : ∀ i, 0 ≤ H2 i := fun i => le_max_right _ _
  have hjoin : physicalEconomicOffset m1 H1 (fun _ => 0) = physicalEconomicOffset m2 H2 L := by
    dsimp [physicalEconomicOffset]
    congr 1
    · funext i
      dsimp [H1,H2]
      rcases le_total (m1.shares i) (m2.shares i) with hh | hh
      · rw [max_eq_left (by linarith),max_eq_right (by linarith)];ring
      · rw [max_eq_right (by linarith),max_eq_left (by linarith)];ring
    · funext i
      dsimp [L]
      ring
  refine ⟨H1,H2,L,hH1,hH2,original_reachable_trans_eq
    (offsetPhysicalTrace h H1 (fun _ => 0) hH1) (offsetPhysicalTrace h' H2 L hH2) hjoin,?_⟩
  intro i
  rw [original_reachable_trans_eq_recovery,offsetPhysicalTrace_recovery,offsetPhysicalTrace_recovery]

end MarketCrash
