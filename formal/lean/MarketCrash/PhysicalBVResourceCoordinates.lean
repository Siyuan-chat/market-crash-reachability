import MarketCrash.OriginalPulse
import MarketCrash.LipschitzFTC
import MarketCrash.PhysicalBVNormalForm

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

def shareResponseCoordinate (F : ℝ) (g : ℝ → ℝ) (S : ℝ) : ℝ :=
  ∫ u in F..S, 1 / g u

def inventoryCostCoordinate (F : ℝ) (g : ℝ → ℝ) (S : ℝ) : ℝ :=
  coordinate F g S - F * shareResponseCoordinate F g S

theorem shareResponseCoordinate_at_benchmark (F : ℝ) (g : ℝ → ℝ) :
    shareResponseCoordinate F g F = 0 := by simp [shareResponseCoordinate]

theorem shareResponseCoordinate_hasDerivAt (F : ℝ) (g : Response) (hF : 0 < F)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (shareResponseCoordinate F g.impact) (1 / g.impact S) S := by
  have hc : ContinuousOn (fun u : ℝ => 1 / g.impact u) (Ioi 0) :=
    continuousOn_const.div g.continuousOn_positive (fun u hu => (g.positive u hu).ne')
  have hsub : uIcc F S ⊆ Ioi (0 : ℝ) := fun u hu => (lt_min hF hS).trans_le hu.1
  exact intervalIntegral.integral_hasDerivAt_right (hc.mono hsub).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc S hS)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hS))

theorem shareResponseCoordinate_strictMonoOn (F : ℝ) (g : Response) (hF : 0 < F) :
    StrictMonoOn (shareResponseCoordinate F g.impact) positivePrices := by
  apply strictMonoOn_of_deriv_pos (convex_Ioi 0)
  · intro S hS
    exact (shareResponseCoordinate_hasDerivAt F g hF hS).continuousAt.continuousWithinAt
  · intro S hS
    have hs : 0 < S := by simpa [positivePrices, interior_Ioi] using hS
    rw [(shareResponseCoordinate_hasDerivAt F g hF hs).deriv]
    exact div_pos one_pos (g.positive _ hs)

theorem inventoryCostCoordinate_hasDerivAt (F : ℝ) (g : Response) (hF : 0 < F)
    {S : ℝ} (hS : 0 < S) :
    HasDerivAt (inventoryCostCoordinate F g.impact) ((S - F) / g.impact S) S := by
  convert (coordinate_hasDerivAt F g hF hS).sub
    ((shareResponseCoordinate_hasDerivAt F g hF hS).const_mul F) using 1
  dsimp [inventoryCostCoordinate]
  ring

theorem inventoryCostCoordinate_integral (F S : ℝ) (g : Response) (hF : 0 < F) (hS : 0 < S) :
    inventoryCostCoordinate F g.impact S = ∫ u in F..S, (u - F) / g.impact u := by
  have hsub : uIcc F S ⊆ positivePrices := fun u hu => (lt_min hF hS).trans_le hu.1
  have hc := g.continuousOn_positive.mono hsub
  have hi : IntervalIntegrable (fun u => 1 / g.impact u) volume F S :=
    (continuousOn_const.div hc (fun u hu => (g.positive _ (hsub hu)).ne')).intervalIntegrable
  have hj : IntervalIntegrable (fun u => u / g.impact u) volume F S :=
    (continuousOn_id.div hc (fun u hu => (g.positive _ (hsub hu)).ne')).intervalIntegrable
  unfold inventoryCostCoordinate coordinate shareResponseCoordinate
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hj (hi.const_mul F)]
  apply intervalIntegral.integral_congr
  intro u _
  ring

theorem inventoryCostCoordinate_nonnegative (F S : ℝ) (g : Response) (hF : 0 < F) (hS : 0 < S) :
    0 ≤ inventoryCostCoordinate F g.impact S := by
  rw [inventoryCostCoordinate_integral F S g hF hS]
  rcases le_total F S with hFS | hSF
  · apply intervalIntegral.integral_nonneg hFS
    intro u hu
    exact div_nonneg (sub_nonneg.mpr hu.1) (g.positive _ (hF.trans_le hu.1)).le
  · rw [intervalIntegral.integral_symm]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_nonneg hSF
    intro u hu
    exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hu.2) (g.positive _ (hS.trans_le hu.1)).le)

theorem inventoryCostCoordinate_antitone_below (F : ℝ) (g : Response) (hF : 0 < F) :
    AntitoneOn (inventoryCostCoordinate F g.impact) (Ioc 0 F) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 F)
  · intro S hS
    exact (inventoryCostCoordinate_hasDerivAt F g hF hS.1).continuousAt.continuousWithinAt
  · intro S hS
    have hs : S ∈ Ioc (0 : ℝ) F := interior_subset hS
    exact (inventoryCostCoordinate_hasDerivAt F g hF hs.1).differentiableAt.differentiableWithinAt
  · intro S hS
    have hs : S ∈ Ioc (0 : ℝ) F := interior_subset hS
    rw [(inventoryCostCoordinate_hasDerivAt F g hF hs.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2) (g.positive _ hs.1).le

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

theorem OriginalFlowCompletedPulse.share_flow_interior
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (i : ι) :
    HasDerivAt (fun u => p.shares u i)
      (tradingInput (pairedMatrix edges) p.dollars i / p.prices a i) a := by
  apply unit_interval_primitive_hasDerivAt _ _ _ (p.physical_share_primitive i) a ha
  exact continuousOn_const.div (p.continuous_prices i) (fun u hu => (p.positive_prices u hu i).ne')

theorem OriginalFlowCompletedPulse.share_coordinate_flow_interior
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Ioo (0 : ℝ) 1) (i : ι) :
    HasDerivAt (fun u => shareResponseCoordinate (p.F i) (p.response i).impact (p.prices u i))
      (tradingInput (pairedMatrix edges) p.dollars i / p.prices a i) a := by
  have hp := p.positive_prices a ⟨ha.1.le, ha.2.le⟩ i
  have hg := (p.response i).positive _ hp
  have hd := (shareResponseCoordinate_hasDerivAt (p.F i) (p.response i) (p.benchmark_positive i) hp).comp a
    (p.price_flow_interior a ha i)
  convert hd using 1 <;> dsimp [Function.comp] <;> field_simp [hp.ne', hg.ne'] <;> ring

theorem OriginalFlowCompletedPulse.share_coordinate_at_parameter
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (i : ι) :
    shareResponseCoordinate (p.F i) (p.response i).impact (p.prices a i) -
      shareResponseCoordinate (p.F i) (p.response i).impact (p.prices 0 i) = p.shares a i - p.shares 0 i := by
  have hc : ContinuousOn (shareResponseCoordinate (p.F i) (p.response i).impact) positivePrices := by
    intro s hs
    exact (shareResponseCoordinate_hasDerivAt _ _ (p.benchmark_positive i) hs).continuousAt.continuousWithinAt
  have hcp := hc.comp (p.continuous_prices i) (fun u hu => p.positive_prices u hu i)
  have hwi : ContinuousOn (fun u => tradingInput (pairedMatrix edges) p.dollars i / p.prices u i)
      (Icc 0 a) := continuousOn_const.div
        ((p.continuous_prices i).mono (fun _ hu => ⟨hu.1, hu.2.trans ha.2⟩))
        (fun u hu => (p.positive_prices u ⟨hu.1, hu.2.trans ha.2⟩ i).ne')
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha.1
    (hcont := hcp.mono (fun u hu => ⟨hu.1, hu.2.trans ha.2⟩))
    (hderiv := fun u hu => p.share_coordinate_flow_interior u ⟨hu.1, hu.2.trans_le ha.2⟩ i)
    (hint := hwi.intervalIntegrable_of_Icc ha.1)
  simpa only [Function.comp_apply, ← p.physical_share_primitive i a ha] using hftc.symm

theorem OriginalFlowCompletedPulse.cost_at_parameter
    (p : OriginalFlowCompletedPulse edges) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (i : ι) :
    p.F i * p.shares a i + inventoryCostCoordinate (p.F i) (p.response i).impact (p.prices a i) - p.dollarLedger a i =
    p.F i * p.shares 0 i + inventoryCostCoordinate (p.F i) (p.response i).impact (p.prices 0 i) - p.dollarLedger 0 i := by
  have hc := p.coordinate_at_parameter a ha i
  have hs := p.share_coordinate_at_parameter a ha i
  have hl := p.marginal_dollar_primitive i a ha
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hl
  unfold inventoryCostCoordinate
  nlinarith [congrArg (fun x : ℝ => p.F i * x) hs]

/-- Compact positive price bounds make any C1 response coordinate
Lipschitz on the actual Lipschitz execution trajectory. -/
theorem resourceCoordinate_comp_lipschitz (P slope S : ℝ → ℝ)
    (a b : ℝ) (hab : a ≤ b) {C : ℝ≥0} (hS : LipschitzWith C S)
    (hp : ∀ u ∈ Icc a b, 0 < S u)
    (hslope : ContinuousOn slope positivePrices)
    (hP : ∀ x, 0 < x → HasDerivAt P (slope x) x) :
    ∃ D : ℝ≥0, LipschitzOnWith D (fun u => P (S u)) (Icc a b) := by
  have hc := hS.continuous.continuousOn (s := Icc a b)
  have hne : (Icc a b).Nonempty := ⟨a, le_rfl, hab⟩
  obtain ⟨l, hl, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  have hsub : Icc (S l) (S u) ⊆ positivePrices := fun x hx => (hp l hl).trans_le hx.1
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image (hslope.mono hsub).norm
  let E : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hcoord : LipschitzOnWith E P (Icc (S l) (S u)) := by
    apply (convex_Icc (S l) (S u)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hP x (hsub hx)).hasDerivWithinAt)
    intro x hx
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  exact ⟨E * C, hcoord.comp hS.lipschitzOnWith (fun t ht => ⟨hmin ht, hmax ht⟩)⟩

variable {m : PhysicalContinuousBVPiece edges} {scale : ℝ}

theorem PhysicalBVClock.share_coordinate_lipschitz (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun u => shareResponseCoordinate (m.F i) (m.response i).impact (m.prices (c.time u) i))
      (Icc c.A c.B) := by
  obtain ⟨C, hC⟩ := c.global_prices_lipschitz hs i
  exact resourceCoordinate_comp_lipschitz _ (fun S => 1 / (m.response i).impact S) _ c.A c.B
    ((m.execution.variationClock_strictMono scale hs.le).monotone m.time_order) hC
    (fun u _ => m.positive_prices _ (c.time_range u) i)
    (continuousOn_const.div (m.response i).continuousOn_positive (fun S hS => ((m.response i).positive _ hS).ne'))
    (fun S hS => shareResponseCoordinate_hasDerivAt _ _ (m.benchmark_positive i) hS)

theorem PhysicalBVClock.share_coordinate_derivative_ae (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∀ᵐ u ∂volume, u ∈ Icc c.A c.B →
      HasDerivAt (fun v => shareResponseCoordinate (m.F i) (m.response i).impact (m.prices (c.time v) i))
        (tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i / m.prices (c.time u) i -
          m.rho i * (m.prices (c.time u) i - m.F i) / (m.response i).impact (m.prices (c.time u) i) *
            deriv c.timeIntegrator u) u := by
  filter_upwards [c.physical_ode_ae hs] with u hu hmem
  have hp := m.positive_prices _ (c.time_range u) i
  have hg := (m.response i).positive _ hp
  have hd := (shareResponseCoordinate_hasDerivAt (m.F i) (m.response i) (m.benchmark_positive i) hp).comp u
    ((hu hmem).2.2.1 i)
  convert hd using 1 <;> dsimp [Function.comp] <;> field_simp [hp.ne', hg.ne'] <;> ring

theorem PhysicalBVClock.cost_score_lipschitz (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun u => m.F i * m.shares (c.time u) i +
        inventoryCostCoordinate (m.F i) (m.response i).impact (m.prices (c.time u) i) -
          m.dollarLedger (c.time u) i) (Icc c.A c.B) := by
  obtain ⟨Cp, hCp⟩ := c.global_prices_lipschitz hs i
  obtain ⟨CE, hCE⟩ := resourceCoordinate_comp_lipschitz
    (inventoryCostCoordinate (m.F i) (m.response i).impact)
    (fun S => (S - m.F i) / (m.response i).impact S) _ c.A c.B
    ((m.execution.variationClock_strictMono scale hs.le).monotone m.time_order) hCp
    (fun u _ => m.positive_prices _ (c.time_range u) i)
    ((continuousOn_id.sub continuousOn_const).div (m.response i).continuousOn_positive
      (fun S hS => ((m.response i).positive _ hS).ne'))
    (fun S hS => inventoryCostCoordinate_hasDerivAt _ _ (m.benchmark_positive i) hS)
  obtain ⟨Csh, hCsh⟩ := c.global_shares_lipschitz hs i
  obtain ⟨Cf, hCf⟩ := rateBand_lipschitz_mul
    ((LipschitzWith.const (m.F i)).lipschitzOnWith) hCsh.lipschitzOnWith
  obtain ⟨Cl, hCl⟩ := c.global_ledger_lipschitz hs i
  exact ⟨Cf + CE + Cl, (hCf.add hCE).sub hCl.lipschitzOnWith⟩

theorem PhysicalBVClock.cost_score_derivative_ae (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∀ᵐ u ∂volume, u ∈ Icc c.A c.B →
      HasDerivAt (fun v => m.F i * m.shares (c.time v) i +
        inventoryCostCoordinate (m.F i) (m.response i).impact (m.prices (c.time v) i) -
          m.dollarLedger (c.time v) i)
        (-m.rho i * (m.prices (c.time u) i - m.F i) ^ 2 /
          (m.response i).impact (m.prices (c.time u) i) * deriv c.timeIntegrator u) u := by
  filter_upwards [c.physical_ode_ae hs] with u hu hmem
  have hp := m.positive_prices _ (c.time_range u) i
  have hg := (m.response i).positive _ hp
  have hE := (inventoryCostCoordinate_hasDerivAt (m.F i) (m.response i) (m.benchmark_positive i) hp).comp u
    ((hu hmem).2.2.1 i)
  have hd := ((((hu hmem).2.2.2.1 i).const_mul (m.F i)).add hE).sub ((hu hmem).2.2.2.2 i)
  convert hd using 1 <;> dsimp [Function.comp] <;> field_simp [hp.ne', hg.ne'] <;> ring

theorem PhysicalContinuousBVPiece.inventory_cost_nonincreasing
    (m : PhysicalContinuousBVPiece edges) (i : ι) :
    m.F i * m.shares m.b i + inventoryCostCoordinate (m.F i) (m.response i).impact (m.prices m.b i) -
      m.dollarLedger m.b i ≤
    m.F i * m.shares m.a i + inventoryCostCoordinate (m.F i) (m.response i).impact (m.prices m.a i) -
      m.dollarLedger m.a i := by
  obtain ⟨c⟩ := m.exists_physicalBVClock 1 (by norm_num)
  obtain ⟨C, hC⟩ := c.cost_score_lipschitz (by norm_num) i
  have horder : c.A ≤ c.B := (m.execution.variationClock_strictMono 1 (by norm_num)).monotone m.time_order
  have hftc := (lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hC horder (by
    filter_upwards [c.cost_score_derivative_ae (by norm_num) i] with u hu hmem
    exact hu ⟨hmem.1.le, hmem.2.le⟩)).2
  have hnonpos : (∫ u in c.A..c.B,
      -m.rho i * (m.prices (c.time u) i - m.F i) ^ 2 /
        (m.response i).impact (m.prices (c.time u) i) * deriv c.timeIntegrator u) ≤ 0 := by
    have hh : 0 ≤ ∫ u in c.A..c.B,
        -(-m.rho i * (m.prices (c.time u) i - m.F i) ^ 2 /
          (m.response i).impact (m.prices (c.time u) i) * deriv c.timeIntegrator u) := by
      apply intervalIntegral.integral_nonneg horder
      intro u _
      have hp := m.positive_prices _ (c.time_range u) i
      have hg := (m.response i).positive _ hp
      have hn := c.actual_speeds_nonnegative u
      exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (m.resilience_nonnegative i)) (sq_nonneg _)) hg.le) hn.1)
    rw [intervalIntegral.integral_neg] at hh
    linarith
  rw [hftc] at hnonpos
  have hta : c.time c.A = m.a := c.time_clock m.a ⟨le_rfl, m.time_order⟩
  have htb : c.time c.B = m.b := c.time_clock m.b ⟨m.time_order, le_rfl⟩
  rw [hta, htb] at hnonpos
  linarith

end MarketCrash
