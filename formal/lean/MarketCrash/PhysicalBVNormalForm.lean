import MarketCrash.PhysicalBVProjection
import MarketCrash.AEPhysicalFTC
import MarketCrash.WeakBVPriceBarrier

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal

theorem stieltjes_measure_ac_of_lipschitz (G : StieltjesFunction) {C : ℝ≥0}
    (hG : LipschitzWith C G) : G.measure ≪ volume := by
  let H : StieltjesFunction := {
    toFun := fun x => C * x - G x
    mono' := by
      intro x y hxy
      have hh := hG.dist_le_mul x y
      rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy)] at hh
      have h := (abs_le.mp hh).1
      dsimp
      nlinarith
    right_continuous' := fun _ => ((continuous_const.mul continuous_id).sub hG.continuous).continuousAt.continuousWithinAt }
  exact lipschitzFTC_stieltjes_ac_of_complement G H C (by intro x; dsimp [H]; ring)

theorem stieltjes_lipschitz_integral_density (G : StieltjesFunction) {C : ℝ≥0}
    (hG : LipschitzWith C G) (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) :
    (∫ u in a..b, w u ∂G.measure) = ∫ u in a..b, w u * deriv G u := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  have hh := setIntegral_rnDeriv_smul (stieltjes_measure_ac_of_lipschitz G hG)
    (f := w) (s := Ioc a b) measurableSet_Ioc
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae G.ae_hasDerivAt] with u hu
  rw [hu.deriv]
  simp [smul_eq_mul, mul_comm]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι} {m : PhysicalContinuousBVPiece edges} {scale : ℝ}

theorem PhysicalBVClock.coordinate_lipschitz_asset (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun u => coordinate (m.F i) (m.response i).impact (m.prices (c.time u) i)) (Icc c.A c.B) := by
  obtain ⟨C, hC⟩ := c.global_prices_lipschitz hs i
  have hc := hC.continuous.continuousOn (s := Icc c.A c.B)
  have horder := (m.execution.variationClock_strictMono scale hs.le).monotone m.time_order
  have hne : (Icc c.A c.B).Nonempty := ⟨c.A, le_rfl, horder⟩
  obtain ⟨l, hl, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  let L := m.prices (c.time l) i
  let U := m.prices (c.time u) i
  have hL : 0 < L := m.positive_prices _ (c.time_range l) i
  have hsub : Icc L U ⊆ positivePrices := fun x hx => hL.trans_le hx.1
  have hg := (m.response i).continuousOn_positive.mono hsub
  have hn : ContinuousOn (fun x : ℝ => ‖x / (m.response i).impact x‖) (Icc L U) :=
    (continuousOn_id.div hg (fun x hx => ((m.response i).positive x (hsub hx)).ne')).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hn
  let D : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hphi : LipschitzOnWith D (coordinate (m.F i) (m.response i).impact) (Icc L U) := by
    apply (convex_Icc L U).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (coordinate_hasDerivAt _ _ (m.benchmark_positive i) (hsub hx)).hasDerivWithinAt)
    intro x hx
    change ‖x / (m.response i).impact x‖ ≤ max B 0
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  exact ⟨D * C, hphi.comp hC.lipschitzOnWith (fun t ht => ⟨hmin ht, hmax ht⟩)⟩

/-- Heterogeneous per-asset normal form from raw physical BV primitives. -/
theorem PhysicalBVClock.coordinate_endpoint (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (i : ι) :
    coordinate (m.F i) (m.response i).impact (m.prices m.b i) -
      coordinate (m.F i) (m.response i).impact (m.prices m.a i) =
      m.dollarLedger m.b i - m.dollarLedger m.a i -
        m.rho i * ∫ t in m.a..m.b,
          m.prices t i * (m.prices t i - m.F i) / (m.response i).impact (m.prices t i) := by
  let R := fun u => m.prices (c.time u) i * (m.prices (c.time u) i - m.F i) /
    (m.response i).impact (m.prices (c.time u) i)
  have hRc : Continuous R :=
    (m.recovery_integrand_continuous i).comp_continuous c.continuous_time c.time_range
  have horder : c.A ≤ c.B := (m.execution.variationClock_strictMono scale hs.le).monotone m.time_order
  have hT : LipschitzWith 1 c.timeIntegrator := (c.global_time_edge_lipschitz hs).1
  have hTi := (lipschitz_integral_deriv_eq_sub hT c.A c.B horder).1
  have hRi : IntervalIntegrable (fun u => R u * deriv c.timeIntegrator u) volume c.A c.B :=
    hTi.continuousOn_mul hRc.continuousOn
  obtain ⟨D, hD⟩ := c.global_ledger_lipschitz hs i
  have hflow := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hD.lipschitzOnWith horder (by
    filter_upwards [c.physical_ode_ae hs] with u hu hmem
    exact (hu ⟨hmem.1.le, hmem.2.le⟩).2.2.2.2 i)
  obtain ⟨C, hC⟩ := c.coordinate_lipschitz_asset hs i
  have hd := lipschitzOn_integral_eq_sub_of_hasDerivAt_ae hC horder
    (w := fun u => tradingInput (pairedMatrix edges) (fun e => deriv (c.edge e) u) i -
      m.rho i * (R u * deriv c.timeIntegrator u)) (by
      filter_upwards [c.physical_ode_ae hs] with u hu hmem
      have hp := m.positive_prices _ (c.time_range u) i
      have hg := (m.response i).positive _ hp
      have hh := (coordinate_hasDerivAt (m.F i) (m.response i) (m.benchmark_positive i) hp).comp u
        ((hu ⟨hmem.1.le, hmem.2.le⟩).2.2.1 i)
      convert hh using 1
      dsimp [Function.comp, R]
      field_simp [hp.ne', hg.ne']
      ring)
  have hdeq := hd.2
  rw [intervalIntegral.integral_sub hflow.1 (hRi.const_mul (m.rho i)),
    intervalIntegral.integral_const_mul, hflow.2] at hdeq
  have hback := c.integral_prefix hs StieltjesFunction.id continuousOn_id
    (fun t => m.prices t i * (m.prices t i - m.F i) / (m.response i).impact (m.prices t i))
    (m.recovery_integrand_continuous i)
    c.B ⟨horder, le_rfl⟩
  have hta : c.time c.A = m.a := c.time_clock m.a ⟨le_rfl, m.time_order⟩
  have htb : c.time c.B = m.b := c.time_clock m.b ⟨m.time_order, le_rfl⟩
  rw [identity_stieltjes_measure_eq_volume, htb] at hback
  have hdensity := stieltjes_lipschitz_integral_density c.timeIntegrator hT R c.A c.B horder
  change (∫ t in m.a..m.b, m.prices t i * (m.prices t i - m.F i) / (m.response i).impact (m.prices t i)) =
    ∫ u in c.A..c.B, R u ∂c.timeIntegrator.measure at hback
  have hphys : (∫ u in c.A..c.B, R u * deriv c.timeIntegrator u) =
      ∫ t in m.a..m.b, m.prices t i * (m.prices t i - m.F i) / (m.response i).impact (m.prices t i) :=
    hdensity.symm.trans hback.symm
  rw [hphys] at hdeq
  change _ = coordinate (m.F i) (m.response i).impact (m.prices (c.time c.B) i) -
    coordinate (m.F i) (m.response i).impact (m.prices (c.time c.A) i) at hdeq
  rw [hta, htb] at hdeq
  linarith

/-- Restriction of raw primitives, without any transformed-equation premise. -/
def PhysicalContinuousBVPiece.prefix (m : PhysicalContinuousBVPiece edges)
    (t : ℝ) (ht : t ∈ Icc m.a m.b) : PhysicalContinuousBVPiece edges where
  a := m.a
  b := t
  time_order := ht.1
  F := m.F
  rho := m.rho
  response := m.response
  benchmark_positive := m.benchmark_positive
  resilience_nonnegative := m.resilience_nonnegative
  execution := m.execution
  continuous_execution := fun e => (m.continuous_execution e).mono (fun _ hx => ⟨hx.1, hx.2.trans ht.2⟩)
  prices := m.prices
  shares := m.shares
  dollarLedger := m.dollarLedger
  continuous_prices := fun i => (m.continuous_prices i).mono (fun _ hx => ⟨hx.1, hx.2.trans ht.2⟩)
  positive_prices := fun s hs => m.positive_prices s ⟨hs.1, hs.2.trans ht.2⟩
  no_short_sales := fun s hs => m.no_short_sales s ⟨hs.1, hs.2.trans ht.2⟩
  physical_price_primitive := fun i s hs u hu =>
    m.physical_price_primitive i s ⟨hs.1, hs.2.trans ht.2⟩ u ⟨hu.1, hu.2.trans ht.2⟩
  physical_share_primitive := fun i s hs u hu =>
    m.physical_share_primitive i s ⟨hs.1, hs.2.trans ht.2⟩ u ⟨hu.1, hu.2.trans ht.2⟩
  marginal_dollar_primitive := fun i s hs u hu =>
    m.marginal_dollar_primitive i s ⟨hs.1, hs.2.trans ht.2⟩ u ⟨hu.1, hu.2.trans ht.2⟩

/-- All physical-time endpoints, retaining asset-specific F, rho and g. -/
theorem PhysicalContinuousBVPiece.normal_form (m : PhysicalContinuousBVPiece edges)
    (t : ℝ) (ht : t ∈ Icc m.a m.b) (i : ι) :
    coordinate (m.F i) (m.response i).impact (m.prices t i) =
      coordinate (m.F i) (m.response i).impact (m.prices m.a i) +
        tradingInput (pairedMatrix edges)
          (fun e => (m.execution.cumulative e) t - (m.execution.cumulative e) m.a) i -
        m.rho i * ∫ u in m.a..t,
          m.prices u i * (m.prices u i - m.F i) / (m.response i).impact (m.prices u i) := by
  obtain ⟨c⟩ := (m.prefix t ht).exists_physicalBVClock 1 (by norm_num)
  have hh := c.coordinate_endpoint (by norm_num) i
  change coordinate (m.F i) (m.response i).impact (m.prices t i) -
      coordinate (m.F i) (m.response i).impact (m.prices m.a i) =
      m.dollarLedger t i - m.dollarLedger m.a i -
        m.rho i * ∫ u in m.a..t,
          m.prices u i * (m.prices u i - m.F i) / (m.response i).impact (m.prices u i) at hh
  have hl := m.marginal_dollar_primitive i m.a ⟨le_rfl, m.time_order⟩ t ht
  linarith

/-- The original common-parameter weak semantics is now a derived projection.
Recovery extension is supplied by the physical piece's clamped construction. -/
def PhysicalContinuousBVPiece.toWeak (m : PhysicalContinuousBVPiece edges)
    (F rho : ℝ) (g : Response) (hF : ∀ i, m.F i = F)
    (hr : ∀ i, m.rho i = rho) (hg : ∀ i, m.response i = g) :
    ContinuousWeakBVPriceSegment F rho g edges where
  a := m.a
  b := m.b
  time_order := m.time_order
  cumulative := m.execution.cumulative
  prices := m.prices
  prices_continuous := m.continuous_prices
  positive_prices := m.positive_prices
  recoveryForce := m.recoveryExtension
  recoveryForce_continuous := m.recoveryExtension_continuous
  recoveryForce_eq := by
    intro t ht i
    simpa only [hF, hg] using m.recoveryExtension_eq t ht i
  weak_physical_price_response := by
    intro t ht i
    have hh := m.normal_form t ht i
    have he : (∫ u in m.a..t, m.recoveryExtension u i) =
        ∫ u in m.a..t, m.prices u i * (m.prices u i - m.F i) /
          (m.response i).impact (m.prices u i) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with u hu
      rw [uIoc_of_le ht.1] at hu
      exact m.recoveryExtension_eq u ⟨hu.1.le, hu.2.trans ht.2⟩ i
    rw [he]
    simpa only [hF, hr, hg] using hh

end MarketCrash
