import MarketCrash.ConstantPulse
import MarketCrash.CompletePairedEmbedding

noncomputable section
namespace MarketCrash
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def squareDonorEdge (hub : ι) (i : {i : ι // i ≠ hub}) : CompleteEdgeIndex ι :=
  ⟨(i,hub),i.property⟩

def squareReceiverEdge (hub : ι) (i : {i : ι // i ≠ hub}) : CompleteEdgeIndex ι :=
  ⟨(hub,i),i.property.symm⟩

def squareDonorSchedule (hub : ι) (a : ι → ℝ) (J : List {i : ι // i ≠ hub}) :=
  J.map (fun i => (squareDonorEdge hub i,a i))

theorem square_donor_schedule_positive (hub : ι) (a x : ι → ℝ)
    (J : List {i : ι // i ≠ hub}) (hJ : J.Nodup)
    (hx : ∀ i, 0 < x i) (ha : ∀ i ∈ J, 0 < a i ∧ a i < x i) :
    squareSchedulePositive completePairedEdges x (squareDonorSchedule hub a J) := by
  induction J generalizing x with
  | nil => exact hx
  | cons j J ih =>
    have hj := ha j (by simp)
    let x' := fun i => x i+a j*pairedMatrix completePairedEdges i (squareDonorEdge hub j)
    have hxp : ∀ i, 0 < x' i := by
      intro i
      by_cases hh : i = hub
      · subst i
        simp only [x',pairedMatrix,completePairedEdges,squareDonorEdge]
        simp only [j.property.symm,not_false_eq_true,ite_false,ite_true,sub_zero,mul_one]
        linarith [hx hub]
      · by_cases hjj : i = (j : ι)
        · subst i
          simp [x',pairedMatrix,completePairedEdges,squareDonorEdge,j.property]
          linarith
        · simpa [x',pairedMatrix,completePairedEdges,squareDonorEdge,hh,hjj] using hx i
    have ht : ∀ i ∈ J, 0 < a i ∧ a i < x' i := by
      intro i hi
      have hh := ha i (by simp [hi])
      have hne : (i : ι) ≠ j := by
        intro he
        have he' : i = j := Subtype.ext he
        subst i
        exact (List.nodup_cons.mp hJ).1 hi
      simpa [x',pairedMatrix,completePairedEdges,squareDonorEdge,i.property,hne] using hh
    exact ⟨hx,hj.1,ih x' (List.nodup_cons.mp hJ).2 hxp ht⟩

def squareReceiverSchedule (hub : ι) (a : ι → ℝ) (J : List {i : ι // i ≠ hub}) :=
  J.map (fun i => (squareReceiverEdge hub i,a i))

theorem square_receiver_schedule_positive (hub : ι) (a x : ι → ℝ)
    (J : List {i : ι // i ≠ hub}) (hx : ∀ i, 0 < x i)
    (ha : ∀ i ∈ J, 0 < a i) (hcap : (J.map (fun i : {i : ι // i ≠ hub} => a i)).sum < x hub) :
    squareSchedulePositive completePairedEdges x (squareReceiverSchedule hub a J) := by
  induction J generalizing x with
  | nil => exact hx
  | cons j J ih =>
    have hj := ha j (by simp)
    have htail : 0 ≤ (J.map (fun i : {i : ι // i ≠ hub} => a i)).sum :=
      List.sum_nonneg (by intro y hy;obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hy;exact (ha i (by simp [hi])).le)
    have hsum : a j+(J.map (fun i : {i : ι // i ≠ hub} => a i)).sum < x hub := by simpa using hcap
    let x' := fun i => x i+a j*pairedMatrix completePairedEdges i (squareReceiverEdge hub j)
    have hxp : ∀ i, 0 < x' i := by
      intro i
      by_cases hh : i = hub
      · subst i
        simp only [x',pairedMatrix,completePairedEdges,squareReceiverEdge]
        simp only [j.property.symm,not_false_eq_true,ite_false,ite_true,zero_sub,mul_neg,mul_one]
        linarith
      · by_cases hjj : i = (j : ι)
        · subst i
          simp [x',pairedMatrix,completePairedEdges,squareReceiverEdge,j.property]
          linarith [hx j]
        · simpa [x',pairedMatrix,completePairedEdges,squareReceiverEdge,hh,hjj] using hx i
    have hcap' : (J.map (fun i : {i : ι // i ≠ hub} => a i)).sum < x' hub := by
      dsimp [x']
      rw [show pairedMatrix completePairedEdges hub (squareReceiverEdge hub j) = -1 by
        simp [pairedMatrix,completePairedEdges,squareReceiverEdge,j.property.symm]]
      linarith
    exact ⟨hx,hj,ih x' hxp (fun i hi => ha i (by simp [hi])) hcap'⟩

theorem square_donor_endpoint (hub : ι) (a x : ι → ℝ)
    (J : Finset {i : ι // i ≠ hub}) (i : ι) :
    chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a J.toList) i =
      x i+∑ j ∈ J, a j*pairedMatrix completePairedEdges i (squareDonorEdge hub j) := by
  rw [chartControlEndpoint_eq]
  simp only [squareDonorSchedule,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ J.nodup_toList]
  simp

theorem square_donor_endpoint_hub (hub : ι) (a x : ι → ℝ)
    (J : Finset {i : ι // i ≠ hub}) :
    chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a J.toList) hub =
      x hub+∑ j ∈ J, a j := by
  rw [square_donor_endpoint]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp [pairedMatrix,completePairedEdges,squareDonorEdge,j.property.symm]

theorem square_donor_endpoint_nonhub (hub : ι) (a x : ι → ℝ)
    (J : Finset {i : ι // i ≠ hub}) (i : {i : ι // i ≠ hub}) :
    chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a J.toList) i =
      x i-(if i ∈ J then a i else 0) := by
  rw [square_donor_endpoint]
  have hf : ∀ j : {j : ι // j ≠ hub},
      a j*pairedMatrix completePairedEdges (i : ι) (squareDonorEdge hub j) =
      if j = i then -a i else 0 := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [pairedMatrix,completePairedEdges,squareDonorEdge,i.property]
    · have hij : (i : ι) ≠ j := fun he => hj (Subtype.ext he.symm)
      simp [pairedMatrix,completePairedEdges,squareDonorEdge,i.property,hij,hj]
  simp_rw [hf]
  by_cases hi : i ∈ J <;> simp [hi,sub_eq_add_neg]

theorem square_receiver_endpoint (hub : ι) (a x : ι → ℝ)
    (J : Finset {i : ι // i ≠ hub}) (i : ι) :
    chartControlEndpoint completePairedEdges x (squareReceiverSchedule hub a J.toList) i =
      x i+∑ j ∈ J, a j*pairedMatrix completePairedEdges i (squareReceiverEdge hub j) := by
  rw [chartControlEndpoint_eq]
  simp only [squareReceiverSchedule,List.map_map,Function.comp_def]
  rw [← List.sum_toFinset _ J.nodup_toList]
  simp

theorem square_receiver_endpoint_hub (hub : ι) (a x : ι → ℝ)
    (J : Finset {i : ι // i ≠ hub}) :
    chartControlEndpoint completePairedEdges x (squareReceiverSchedule hub a J.toList) hub =
      x hub-∑ j ∈ J, a j := by
  rw [square_receiver_endpoint]
  have hf : ∀ j : {i : ι // i ≠ hub}, a j*pairedMatrix completePairedEdges hub (squareReceiverEdge hub j) = -a j := by
    intro j
    simp [pairedMatrix,completePairedEdges,squareReceiverEdge,j.property.symm]
  simp_rw [hf]
  rw [Finset.sum_neg_distrib,sub_eq_add_neg]

theorem square_receiver_endpoint_nonhub (hub : ι) (a x : ι → ℝ)
    (J : Finset {i : ι // i ≠ hub}) (i : {i : ι // i ≠ hub}) :
    chartControlEndpoint completePairedEdges x (squareReceiverSchedule hub a J.toList) i =
      x i+(if i ∈ J then a i else 0) := by
  rw [square_receiver_endpoint]
  have hf : ∀ j : {j : ι // j ≠ hub},
      a j*pairedMatrix completePairedEdges (i : ι) (squareReceiverEdge hub j) =
      if j = i then a i else 0 := by
    intro j
    by_cases hj : j = i
    · subst j
      simp [pairedMatrix,completePairedEdges,squareReceiverEdge,i.property]
    · have hij : (i : ι) ≠ j := fun he => hj (Subtype.ext he.symm)
      simp [pairedMatrix,completePairedEdges,squareReceiverEdge,i.property,hij,hj]
  simp_rw [hf]
  simp

theorem squareSchedulePositive_append {κ : Type*} [Fintype κ]
    (edges : κ → PairedEdge ι) (x : ι → ℝ) (a b : List (κ × ℝ))
    (ha : squareSchedulePositive edges x a)
    (hb : squareSchedulePositive edges (chartControlEndpoint edges x a) b) :
    squareSchedulePositive edges x (a++b) := by
  induction a generalizing x with
  | nil => exact hb
  | cons c a ih => exact ⟨ha.1,ha.2.1,ih _ ha.2.2 hb⟩

theorem chartControlEndpoint_append {κ : Type*}
    (edges : κ → PairedEdge ι) (x : ι → ℝ) (a b : List (κ × ℝ)) :
    chartControlEndpoint edges x (a++b) = chartControlEndpoint edges (chartControlEndpoint edges x a) b := by
  induction a generalizing x with
  | nil => rfl
  | cons c a ih => exact ih _

theorem positive_entries_sum {α : Type*} [Fintype α] [DecidableEq α]
    (a : α → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i ∈ Finset.univ.filter (fun i => 0 < a i), a i = ∑ i, a i := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : 0 < a i
  · simp [hi]
  · have hz : a i = 0 := le_antisymm (not_lt.mp hi) (ha i)
    simp [hz]

theorem squareSchedulePositive_end {κ : Type*} [Fintype κ]
    (edges : κ → PairedEdge ι) (x : ι → ℝ) (cs : List (κ × ℝ))
    (h : squareSchedulePositive edges x cs) :
    ∀ i, 0 < chartControlEndpoint edges x cs i := by
  induction cs generalizing x with
  | nil => exact h
  | cons c cs ih => exact ih _ h.2.2

theorem exists_positive_square_transport (hub : ι) (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hsum : ∑ i, x i = ∑ i, y i) :
    ∃ cs : List (CompleteEdgeIndex ι × ℝ),
      squareSchedulePositive completePairedEdges x cs ∧ chartControlEndpoint completePairedEdges x cs = y := by
  classical
  let a := fun i => max (x i-y i) 0
  let b := fun i => max (y i-x i) 0
  have ha : ∀ i, 0 ≤ a i := fun i => le_max_right _ _
  have hb : ∀ i, 0 ≤ b i := fun i => le_max_right _ _
  have hab : ∀ i, a i-b i = x i-y i := by
    intro i
    dsimp [a,b]
    rcases le_total (x i) (y i) with hh | hh
    · rw [max_eq_right (by linarith),max_eq_left (by linarith)];ring
    · rw [max_eq_left (by linarith),max_eq_right (by linarith)];ring
  let D : Finset {i : ι // i ≠ hub} := Finset.univ.filter (fun i => 0 < a i)
  let R : Finset {i : ι // i ≠ hub} := Finset.univ.filter (fun i => 0 < b i)
  let ds := squareDonorSchedule hub a D.toList
  let xd := chartControlEndpoint completePairedEdges x ds
  have hd : squareSchedulePositive completePairedEdges x ds := by
    apply square_donor_schedule_positive hub a x D.toList D.nodup_toList hx
    intro i hi
    have hai : 0 < a i := (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2
    refine ⟨hai,?_⟩
    exact max_lt_iff.mpr ⟨by linarith [hy i],hx i⟩
  have hxd : ∀ i, 0 < xd i := squareSchedulePositive_end completePairedEdges x ds hd
  have haD : ∀ i : {i : ι // i ≠ hub}, (if i ∈ D then a i else 0) = a i := by
    intro i
    by_cases hi : 0 < a i
    · simp [D,hi]
    · have hz : a i = 0 := le_antisymm (not_lt.mp hi) (ha i)
      simp [D,hz]
  have hbR : ∀ i : {i : ι // i ≠ hub}, (if i ∈ R then b i else 0) = b i := by
    intro i
    by_cases hi : 0 < b i
    · simp [R,hi]
    · have hz : b i = 0 := le_antisymm (not_lt.mp hi) (hb i)
      simp [R,hz]
  have hdh : xd hub = x hub+∑ i : {i : ι // i ≠ hub}, a i := by
    rw [show xd hub = chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a D.toList) hub from rfl,
      square_donor_endpoint_hub]
    rw [positive_entries_sum (fun i : {i : ι // i ≠ hub} => a i) (fun i => ha i)]
  have hbal : x hub+(∑ i : {i : ι // i ≠ hub}, a i) =
      y hub+(∑ i : {i : ι // i ≠ hub}, b i) := by
    have hh := hsum
    rw [Fintype.sum_eq_add_sum_subtype_ne x hub,Fintype.sum_eq_add_sum_subtype_ne y hub] at hh
    have he : (∑ i : {i : ι // i ≠ hub}, a i)-(∑ i : {i : ι // i ≠ hub}, b i) =
        (∑ i : {i : ι // i ≠ hub}, x i)-(∑ i : {i : ι // i ≠ hub}, y i) := by
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun i _ => hab i)
    linarith
  have hRsum : (R.toList.map (fun i : {i : ι // i ≠ hub} => b i)).sum =
      ∑ i : {i : ι // i ≠ hub}, b i := by
    rw [← List.sum_toFinset _ R.nodup_toList]
    rw [Finset.toList_toFinset]
    exact positive_entries_sum (fun i : {i : ι // i ≠ hub} => b i) (fun i => hb i)
  have hrcap : (R.toList.map (fun i : {i : ι // i ≠ hub} => b i)).sum < xd hub := by
    rw [hRsum,hdh]
    linarith [hy hub]
  let rs := squareReceiverSchedule hub b R.toList
  have hr : squareSchedulePositive completePairedEdges xd rs :=
    square_receiver_schedule_positive hub b xd R.toList hxd (by
      intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2) hrcap
  refine ⟨ds++rs,squareSchedulePositive_append _ x ds rs hd hr,?_⟩
  rw [chartControlEndpoint_append]
  funext i
  by_cases hi : i = hub
  · subst i
    rw [square_receiver_endpoint_hub]
    change xd hub-(∑ i ∈ R, b i) = y hub
    rw [show (∑ i ∈ R, b i) = ∑ i : {i : ι // i ≠ hub}, b i from
      positive_entries_sum (fun i : {i : ι // i ≠ hub} => b i) (fun i => hb i),hdh]
    linarith
  · change chartControlEndpoint completePairedEdges xd (squareReceiverSchedule hub b R.toList) (⟨i,hi⟩ : {i : ι // i ≠ hub}) = y i
    rw [square_receiver_endpoint_nonhub,hbR]
    change xd i+b i = y i
    rw [show xd i = x i-a i by
      change chartControlEndpoint completePairedEdges x (squareDonorSchedule hub a D.toList) (⟨i,hi⟩ : {i : ι // i ≠ hub}) = _
      rw [square_donor_endpoint_nonhub,haD]]
    linarith [hab i]

theorem positive_square_transport_reachable (hub : ι) (t F eta : ℝ)
    (hF : 0 < F) (hη : 0 < eta) (rho H L x y : ι → ℝ)
    (hH : ∀ i, 0 ≤ H i) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    (hsum : ∑ i, x i = ∑ i, y i) :
    Nonempty (OriginalPhysicalReachable (fun _ => F) rho (fun _ => constantResponse eta hη) completePairedEdges
      (squarePhysicalState t eta H L x) (squarePhysicalState t eta H L y)) := by
  obtain ⟨cs,hc,he⟩ := exists_positive_square_transport hub x y hx hy hsum
  simpa only [he] using square_schedule_reachable completePairedEdges t F eta hF hη rho H L hH cs x hc

end MarketCrash
