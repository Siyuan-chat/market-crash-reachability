import MarketCrash.SharpTraceConstruction
import MarketCrash.OriginalResources

noncomputable section
namespace MarketCrash
open Set

theorem actualNegativeVariation_const_add (f : ℝ → ℝ) (a b c : ℝ) :
    actualNegativeVariation (fun t => c+f t) a b = actualNegativeVariation f a b := by
  simp only [actualNegativeVariation,variationOnFromTo,eVariationOn,
    edist_add_left,add_sub_add_left_eq_sub]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {F rho : ι → ℝ} {g : ι → Response} {edges : κ → PairedEdge ι}
variable {s t : PhysicalMarketState ι}

theorem offsetPhysicalStep_turnover (h : OriginalPhysicalStep F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) :
    (offsetPhysicalStep h H L hH).pairedTurnover = h.pairedTurnover := by
  cases h <;> rfl

theorem offsetPhysicalStep_sales (h : OriginalPhysicalStep F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) (i : ι) :
    (offsetPhysicalStep h H L hH).shareSales i = h.shareSales i := by
  cases h <;> exact actualNegativeVariation_const_add _ _ _ _

theorem offsetPhysicalTrace_turnover (h : OriginalPhysicalReachable F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) :
    (offsetPhysicalTrace h H L hH).pairedTurnover = h.pairedTurnover := by
  induction h with
  | refl => rfl
  | append previous step ih =>
    change (offsetPhysicalTrace previous H L hH).pairedTurnover+
      (offsetPhysicalStep step H L hH).pairedTurnover = _
    rw [ih,offsetPhysicalStep_turnover]
    rfl

theorem offsetPhysicalTrace_sales (h : OriginalPhysicalReachable F rho g edges s t)
    (H L : ι → ℝ) (hH : ∀ i, 0 ≤ H i) (i : ι) :
    (offsetPhysicalTrace h H L hH).shareSales i = h.shareSales i := by
  induction h with
  | refl => rfl
  | append previous step ih =>
    change (offsetPhysicalTrace previous H L hH).shareSales i+
      (offsetPhysicalStep step H L hH).shareSales i = _
    rw [ih,offsetPhysicalStep_sales]
    rfl

theorem original_reachable_trans_turnover {m : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m)
    (h' : OriginalPhysicalReachable F rho g edges m t) :
    (original_reachable_trans h h').pairedTurnover = h.pairedTurnover+h'.pairedTurnover := by
  induction h' with
  | refl => simp [original_reachable_trans,OriginalPhysicalReachable.pairedTurnover]
  | append previous step ih =>
    simp only [original_reachable_trans,OriginalPhysicalReachable.pairedTurnover] at ih ⊢
    rw [ih]
    ring

theorem original_reachable_trans_sales {m : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m)
    (h' : OriginalPhysicalReachable F rho g edges m t) (i : ι) :
    (original_reachable_trans h h').shareSales i = h.shareSales i+h'.shareSales i := by
  induction h' with
  | refl => simp [original_reachable_trans,OriginalPhysicalReachable.shareSales]
  | append previous step ih =>
    simp only [original_reachable_trans,OriginalPhysicalReachable.shareSales] at ih ⊢
    rw [ih]
    ring

theorem original_reachable_trans_eq_turnover {m1 m2 : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m1)
    (h' : OriginalPhysicalReachable F rho g edges m2 t) (hm : m1 = m2) :
    (original_reachable_trans_eq h h' hm).pairedTurnover = h.pairedTurnover+h'.pairedTurnover := by
  subst m2
  exact original_reachable_trans_turnover h h'

theorem original_reachable_trans_eq_sales {m1 m2 : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m1)
    (h' : OriginalPhysicalReachable F rho g edges m2 t) (hm : m1 = m2) (i : ι) :
    (original_reachable_trans_eq h h' hm).shareSales i = h.shareSales i+h'.shareSales i := by
  subst m2
  exact original_reachable_trans_sales h h' i

theorem concatenate_with_resources {m1 m2 : PhysicalMarketState ι}
    (h : OriginalPhysicalReachable F rho g edges s m1)
    (h' : OriginalPhysicalReachable F rho g edges m2 t)
    (htime : m1.time = m2.time) (hprice : m1.prices = m2.prices) :
    ∃ H1 H2 L : ι → ℝ, (∀ i, 0 ≤ H1 i) ∧ (∀ i, 0 ≤ H2 i) ∧
      (∀ i, H1 i = max (m2.shares i-m1.shares i) 0) ∧
      (∀ i, H2 i = max (m1.shares i-m2.shares i) 0) ∧
      ∃ path : OriginalPhysicalReachable F rho g edges
        (physicalEconomicOffset s H1 (fun _ => 0)) (physicalEconomicOffset t H2 L),
        (∀ i, path.recoveryIntegral i = h.recoveryIntegral i+h'.recoveryIntegral i) ∧
        path.pairedTurnover = h.pairedTurnover+h'.pairedTurnover ∧
        (∀ i, path.shareSales i = h.shareSales i+h'.shareSales i) := by
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
  let path := original_reachable_trans_eq
    (offsetPhysicalTrace h H1 (fun _ => 0) hH1) (offsetPhysicalTrace h' H2 L hH2) hjoin
  refine ⟨H1,H2,L,hH1,hH2,(fun _ => rfl),(fun _ => rfl),path,?_,?_,?_⟩
  · intro i
    dsimp [path]
    rw [original_reachable_trans_eq_recovery,offsetPhysicalTrace_recovery,offsetPhysicalTrace_recovery]
  · dsimp [path]
    rw [original_reachable_trans_eq_turnover,offsetPhysicalTrace_turnover,offsetPhysicalTrace_turnover]
  · intro i
    dsimp [path]
    rw [original_reachable_trans_eq_sales,offsetPhysicalTrace_sales,offsetPhysicalTrace_sales]

end MarketCrash
