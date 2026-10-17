import MarketCrash.PhysicalPulseConstruction

noncomputable section
namespace MarketCrash
open Set MeasureTheory

theorem positive_weight_primitive (W : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn W (Icc 0 T)) (hp : ∀ t ∈ Icc 0 T, 0 < W t) :
    ContinuousOn (fun t => ∫ u in (0:ℝ)..t, W u) (Icc 0 T) ∧
    StrictMonoOn (fun t => ∫ u in (0:ℝ)..t, W u) (Icc 0 T) ∧
    0 < ∫ u in (0:ℝ)..T, W u := by
  have hi : IntervalIntegrable W volume 0 T := hc.intervalIntegrable_of_Icc hT.le
  have hC : ContinuousOn (fun t => ∫ u in (0:ℝ)..t, W u) (Icc 0 T) := by
    simpa only [uIcc_of_le hT.le] using intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hd : ∀ t ∈ Ioo 0 T, HasDerivAt (fun t => ∫ u in (0:ℝ)..t, W u) (W t) t := by
    intro t ht
    apply intervalIntegral.integral_hasDerivAt_right
    · exact (hc.mono (fun x hx => ⟨hx.1,hx.2.trans ht.2.le⟩)).intervalIntegrable_of_Icc ht.1.le
    · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Icc_self) t ht
    · exact hc.continuousAt (Icc_mem_nhds ht.1 ht.2)
  have hm : StrictMonoOn (fun t => ∫ u in (0:ℝ)..t, W u) (Icc 0 T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hC
    intro t ht
    rw [interior_Icc] at ht
    rw [(hd t ht).deriv]
    exact hp t (Ioo_subset_Icc_self ht)
  refine ⟨hC,hm,?_⟩
  simpa using hm ⟨le_rfl,hT.le⟩ ⟨hT.le,le_rfl⟩ hT

theorem exists_weight_cut (W : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn W (Icc 0 T)) (hp : ∀ t ∈ Icc 0 T, 0 < W t)
    (y : ℝ) (hy : y ∈ Icc 0 (∫ u in (0:ℝ)..T, W u)) :
    ∃ t ∈ Icc 0 T, (∫ u in (0:ℝ)..t, W u) = y := by
  have hh := intermediate_value_Icc hT.le (positive_weight_primitive W T hT hc hp).1
  have he : y ∈ Icc (∫ u in (0:ℝ)..0, W u) (∫ u in (0:ℝ)..T, W u) := by simpa using hy
  obtain ⟨t,ht,he⟩ := hh he
  exact ⟨t,ht,he⟩

theorem exists_equal_weight_partition (W : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn W (Icc 0 T)) (hp : ∀ t ∈ Icc 0 T, 0 < W t)
    (N : ℕ) (hN : 0 < N) :
    ∃ t : Fin (N+1) → ℝ, (∀ i, t i ∈ Icc 0 T) ∧
      StrictMono t ∧ t 0 = 0 ∧ t (Fin.last N) = T ∧
      ∀ i, (∫ u in (0:ℝ)..t i, W u) =
        (i.val : ℝ)/(N : ℝ)*(∫ u in (0:ℝ)..T, W u) := by
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hw := positive_weight_primitive W T hT hc hp
  let I := ∫ u in (0:ℝ)..T, W u
  have hI : 0 < I := hw.2.2
  have hex : ∀ i : Fin (N+1), ∃ t ∈ Icc 0 T,
      (∫ u in (0:ℝ)..t, W u) = (i.val : ℝ)/(N : ℝ)*I := by
    intro i
    apply exists_weight_cut W T hT hc hp
    have hi : (i.val : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
    exact ⟨mul_nonneg (div_nonneg (Nat.cast_nonneg _) hn.le) hI.le,
      (mul_le_mul_of_nonneg_right ((div_le_one hn).mpr hi) hI.le).trans_eq (one_mul I)⟩
  choose t ht he using hex
  have hm : StrictMono t := by
    intro i j hij
    have hval : (i.val : ℝ) < j.val := by exact_mod_cast hij
    have htarget : (i.val : ℝ)/(N : ℝ)*I < (j.val : ℝ)/(N : ℝ)*I :=
      mul_lt_mul_of_pos_right (div_lt_div_of_pos_right hval hn) hI
    have hprim : (∫ u in (0:ℝ)..t i, W u) < ∫ u in (0:ℝ)..t j, W u := by
      rw [he i,he j];exact htarget
    exact lt_of_not_ge (fun hh => (not_lt_of_ge (hw.2.1.monotoneOn (ht j) (ht i) hh)) hprim)
  refine ⟨t,ht,hm,?_,?_,he⟩
  · apply hw.2.1.injOn (ht 0) ⟨le_rfl,hT.le⟩
    simpa using he 0
  · apply hw.2.1.injOn (ht (Fin.last N)) ⟨hT.le,le_rfl⟩
    simpa [I,hn.ne'] using he (Fin.last N)

theorem exists_equal_weight_interval_partition (W : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hc : ContinuousOn W (Icc 0 T)) (hp : ∀ t ∈ Icc 0 T, 0 < W t)
    (N : ℕ) (hN : 0 < N) :
    ∃ t : Fin (N+1) → ℝ, (∀ i, t i ∈ Icc 0 T) ∧ StrictMono t ∧
      t 0 = 0 ∧ t (Fin.last N) = T ∧
      ∀ i : Fin N, (∫ u in t i.castSucc..t i.succ, W u) =
        (∫ u in (0:ℝ)..T, W u)/(N : ℝ) := by
  obtain ⟨t,ht,hm,h0,hend,he⟩ := exists_equal_weight_partition W T hT hc hp N hN
  refine ⟨t,ht,hm,h0,hend,?_⟩
  intro i
  have htij : t i.castSucc ≤ t i.succ := (hm (by exact_mod_cast Nat.lt_succ_self i.val)).le
  have hi : IntervalIntegrable W volume 0 (t i.castSucc) :=
    (hc.mono (fun x hx => ⟨hx.1,hx.2.trans (ht i.castSucc).2⟩)).intervalIntegrable_of_Icc (ht i.castSucc).1
  have hij : IntervalIntegrable W volume (t i.castSucc) (t i.succ) :=
    (hc.mono (fun x hx => ⟨(ht i.castSucc).1.trans hx.1,hx.2.trans (ht i.succ).2⟩)).intervalIntegrable_of_Icc htij
  have hh := intervalIntegral.integral_add_adjacent_intervals hi hij
  rw [he i.castSucc,he i.succ] at hh
  simp only [Fin.coe_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] at hh
  have he' : ((i.val:ℝ)+1)/(N:ℝ)*(∫ u in (0:ℝ)..T, W u) =
      (i.val:ℝ)/(N:ℝ)*(∫ u in (0:ℝ)..T, W u)+(∫ u in (0:ℝ)..T, W u)/(N:ℝ) := by ring
  rw [he'] at hh
  linarith

end MarketCrash
