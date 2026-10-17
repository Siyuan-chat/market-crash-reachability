import MarketCrash.PhysicalBVOperationalODE
import MarketCrash.PhysicalBVReparamLipschitz
import MarketCrash.OperationalClockAE

noncomputable section
namespace MarketCrash
open Set MeasureTheory
open scoped NNReal
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι} {m : PhysicalContinuousBVPiece edges} {scale : ℝ}

theorem PhysicalBVClock.time_clamp (c : PhysicalBVClock m scale) (hs : 0 < scale) (u : ℝ) :
    c.time u = c.time (projIcc c.A c.B
      ((m.execution.variationClock_strictMono scale hs.le).monotone m.time_order) u) := by
  apply (m.execution.variationClock_strictMono scale hs.le).injective
  rw [c.clock_time, c.clock_time_on _ (projIcc _ _ _ u).property]
  rfl

theorem PhysicalBVClock.global_lipschitz_of_reparam (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (f : ℝ → ℝ) {C : ℝ≥0}
    (hf : LipschitzWith C (fun u : Icc c.A c.B => f (c.time u))) :
    LipschitzWith C (fun u => f (c.time u)) := by
  have hh := hf.comp (LipschitzWith.projIcc
    ((m.execution.variationClock_strictMono scale hs.le).monotone m.time_order))
  have heq : (fun u => f (c.time u)) =
      (fun u => f (c.time (projIcc c.A c.B
        ((m.execution.variationClock_strictMono scale hs.le).monotone m.time_order) u))) := by
    funext u
    exact congrArg f (c.time_clamp hs u)
  rw [heq]
  simpa only [mul_one, Function.comp_def] using hh

theorem PhysicalBVClock.global_time_edge_lipschitz (c : PhysicalBVClock m scale) (hs : 0 < scale) :
    LipschitzWith 1 c.time ∧ ∀ e, ∃ C : ℝ≥0, LipschitzWith C (c.edge e) := by
  obtain ⟨T, hright, _, _, _, _, hT, hE⟩ :=
    m.execution.continuous_clock_inverse scale m.a m.b hs m.time_order m.continuous_execution
  have heq (u : Icc c.A c.B) : (T u : ℝ) = c.time u := by
    apply (m.execution.variationClock_strictMono scale hs.le).injective
    rw [hright, c.clock_time_on _ u.property]
  have htime : LipschitzWith 1 (fun u : Icc c.A c.B => c.time u) := by simpa only [heq] using hT
  refine ⟨c.global_lipschitz_of_reparam hs id htime, ?_⟩
  intro e
  refine ⟨⟨1 / scale, by positivity⟩, ?_⟩
  have hedge : LipschitzWith (⟨1 / scale, by positivity⟩ : ℝ≥0)
      (fun u : Icc c.A c.B => (m.execution.cumulative e) (c.time u)) := by
    simpa only [heq] using hE e
  exact c.global_lipschitz_of_reparam hs (m.execution.cumulative e) hedge

theorem PhysicalBVClock.global_prices_lipschitz (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C (fun u => m.prices (c.time u) i) := by
  let T : Icc c.A c.B → Icc m.a m.b := fun u => ⟨c.time u, c.time_range u⟩
  obtain ⟨C, hC⟩ := m.reparam_prices_lipschitz scale hs T (fun u => c.clock_time_on u u.property) i
  exact ⟨C, c.global_lipschitz_of_reparam hs (fun t => m.prices t i) hC⟩

theorem PhysicalBVClock.global_shares_lipschitz (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C (fun u => m.shares (c.time u) i) := by
  let T : Icc c.A c.B → Icc m.a m.b := fun u => ⟨c.time u, c.time_range u⟩
  obtain ⟨C, hC⟩ := m.reparam_shares_lipschitz scale hs T (fun u => c.clock_time_on u u.property) i
  exact ⟨C, c.global_lipschitz_of_reparam hs (fun t => m.shares t i) hC⟩

theorem PhysicalBVClock.global_ledger_lipschitz (c : PhysicalBVClock m scale)
    (hs : 0 < scale) (i : ι) :
    ∃ C : ℝ≥0, LipschitzWith C (fun u => m.dollarLedger (c.time u) i) := by
  let T : Icc c.A c.B → Icc m.a m.b := fun u => ⟨c.time u, c.time_range u⟩
  obtain ⟨C, hC⟩ := physicalBV_primitive_reparam_lipschitz m.execution m.a m.b scale hs
    (fun t => m.dollarLedger t i) (fun _ => 0) (fun _ => 1) (pairedMatrix edges i)
    continuousOn_const continuousOn_const (by
      intro s hs t ht
      simpa only [intervalIntegral.integral_zero, zero_add, stieltjes_integral_one_increment]
        using m.marginal_dollar_primitive i s hs t ht) T (fun u => c.clock_time_on u u.property)
  exact ⟨C, c.global_lipschitz_of_reparam hs (fun t => m.dollarLedger t i) hC⟩

/-- Genuine projection: every ODE field is a theorem of the primitive physical piece. -/
def PhysicalBVClock.toAE (c : PhysicalBVClock m scale) (hs : 0 < scale)
    (F rho : ℝ) (g : Response) (hF : ∀ i, m.F i = F)
    (hr : ∀ i, m.rho i = rho) (hg : ∀ i, m.response i = g) :
    AEOperationalClockSegment F rho g edges where
  a := c.A
  b := c.B
  time_order := (m.execution.variationClock_strictMono scale hs.le).monotone m.time_order
  physicalTime := c.time
  timeSpeed := deriv c.timeIntegrator
  edgeDollars := fun u e => c.edge e u
  edgeRates := fun u e => deriv (c.edge e) u
  prices := fun u i => m.prices (c.time u) i
  shares := fun u i => m.shares (c.time u) i
  dollarLedger := fun u i => m.dollarLedger (c.time u) i
  physical_time_lipschitz := ⟨1, (c.global_time_edge_lipschitz hs).1⟩
  edge_dollars_lipschitz := (c.global_time_edge_lipschitz hs).2
  prices_lipschitz := c.global_prices_lipschitz hs
  shares_lipschitz := c.global_shares_lipschitz hs
  ledgers_lipschitz := c.global_ledger_lipschitz hs
  positive_prices := fun u _ i => m.positive_prices _ (c.time_range u) i
  no_short_sales := fun u _ i => m.no_short_sales _ (c.time_range u) i
  nonnegative_time_speed := fun u _ => (c.actual_speeds_nonnegative u).1
  nonnegative_edge_rates := fun u _ => (c.actual_speeds_nonnegative u).2
  physical_time_flow_ae := (c.physical_ode_ae hs).mono (fun _ h hu => (h hu).1.1)
  cumulative_edge_flow_ae := (c.physical_ode_ae hs).mono (fun _ h hu e => ((h hu).2.1 e).1)
  physical_price_flow_ae := by
    filter_upwards [c.physical_ode_ae hs] with u h hu i
    simpa only [hF, hr, hg] using (h hu).2.2.1 i
  physical_share_flow_ae := (c.physical_ode_ae hs).mono (fun _ h hu i => (h hu).2.2.2.1 i)
  physical_ledger_flow_ae := (c.physical_ode_ae hs).mono (fun _ h hu i => (h hu).2.2.2.2 i)

end MarketCrash
