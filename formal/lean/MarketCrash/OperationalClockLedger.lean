import MarketCrash.OperationalClockAttainable

/-!
Exact endpoint dollar-ledger bookkeeping from the COMMON operational clock.

Unlike merely assuming aggregate dollar conservation, each asset's
physical marginal-settlement ledger is linked to the ACTUAL cumulative
dollars of all directed trading edges by a derived differential identity.
The total signed dollar ledger increment cancels, whereas the stronger
per-asset terminal closure remains an explicit independent condition.

All proofs here use the smooth operational-clock physical subclass. The
a.e. graph-completion bridge to arbitrary BV clocks remains open.
-/
noncomputable section
namespace MarketCrash

/-- Cumulative incidence-weighted edge dollars (without baseline subtraction). -/
def OperationalClockSegment.cumulativeLedger
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges)
    (v : ℝ) (i : ι) : ℝ :=
  tradingInput (pairedMatrix edges) (fun e => m.edgeDollars v e) i

/-- The derivative of actual accumulated edge dollars is exactly the
same paired-dollar rate that drives the physical settlement ledger. -/
theorem OperationalClockSegment.cumulativeLedger_ode
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges)
    (u : ℝ) (hu : u ∈ Set.Icc m.a m.b) (i : ι) :
    HasDerivAt (fun v => m.cumulativeLedger v i)
      (tradingInput (pairedMatrix edges) (m.edgeRates u) i) u := by
  change HasDerivAt
    (fun v : ℝ => ∑ e, pairedMatrix edges i e * m.edgeDollars v e)
    (∑ e, pairedMatrix edges i e * m.edgeRates u e) u
  exact HasDerivAt.sum (u := Finset.univ) (fun e _ =>
    (m.cumulative_edge_flow u hu e).const_mul (pairedMatrix edges i e))

/-- The physical dollar ledger and the cumulative executed-edge-dollar
ledger can differ only by a constant along the operational interval. -/
theorem OperationalClockSegment.ledger_balance_deriv_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges)
    (u : ℝ) (hu : u ∈ Set.Icc m.a m.b) (i : ι) :
    HasDerivAt (fun v => m.dollarLedger v i - m.cumulativeLedger v i)
      0 u := by
  have h := (m.physical_ledger_flow u hu i).sub
    (m.cumulativeLedger_ode u hu i)
  convert h using 1 <;> dsimp <;> ring

/-- For ANY ordered subinterval, the change in the physical ledger
equals the difference in cumulative, incidence-weighted edge dollars.
No model-level conservation of the coordinate is assumed. -/
theorem OperationalClockSegment.ledger_increment_eq_cumulative
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges)
    (s t : ℝ) (hs : s ∈ Set.Icc m.a m.b)
    (ht : t ∈ Set.Icc m.a m.b) (hst : s ≤ t) (i : ι) :
    m.dollarLedger t i - m.dollarLedger s i =
      tradingInput (pairedMatrix edges)
        (fun e => m.edgeDollars t e - m.edgeDollars s e) i := by
  have hFTC :
      (∫ v in s..t, (0 : ℝ)) =
        (m.dollarLedger t i - m.cumulativeLedger t i) -
          (m.dollarLedger s i - m.cumulativeLedger s i) := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun v => m.dollarLedger v i - m.cumulativeLedger v i)
      (f' := fun _ : ℝ => (0 : ℝ))
      (a := s) (b := t)
      (fun v hv => by
        have hstMem : v ∈ Set.Icc s t := by
          simpa only [Set.uIcc_of_le hst] using hv
        have hmem : v ∈ Set.Icc m.a m.b :=
          ⟨hs.1.trans hstMem.1, hstMem.2.trans ht.2⟩
        exact m.ledger_balance_deriv_zero v hmem i)
      intervalIntegrable_const
  simp only [intervalIntegral.integral_zero] at hFTC
  have hnet :
      m.cumulativeLedger t i - m.cumulativeLedger s i =
        tradingInput (pairedMatrix edges)
          (fun e => m.edgeDollars t e - m.edgeDollars s e) i := by
    unfold OperationalClockSegment.cumulativeLedger tradingInput
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e _
    ring
  linarith

/-- The physical ledger's total signed dollar increment sums to zero
for any execution interval, even when recovery acts concurrently. -/
theorem OperationalClockSegment.total_ledger_increment_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges)
    (s t : ℝ) (hs : s ∈ Set.Icc m.a m.b)
    (ht : t ∈ Set.Icc m.a m.b) (hst : s ≤ t) :
    (∑ i, (m.dollarLedger t i - m.dollarLedger s i)) = 0 := by
  calc
    (∑ i, (m.dollarLedger t i - m.dollarLedger s i)) =
        ∑ i, tradingInput (pairedMatrix edges)
          (fun e => m.edgeDollars t e - m.edgeDollars s e) i := by
            apply Finset.sum_congr rfl
            intro i _
            exact m.ledger_increment_eq_cumulative s t hs ht hst i
    _ = 0 := paired_trading_sum_zero edges _

/-- Given zero initial per-asset dollar ledgers, exact terminal closure
is equivalent to zero cumulative net executed dollars of EVERY asset.
Aggregate cancellation alone never suffices for this conclusion. -/
theorem OperationalClockSegment.terminalClosure_iff
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges)
    (hinit : ∀ i, m.dollarLedger m.a i = 0) :
    (∀ i, m.dollarLedger m.b i = 0) ↔
      (∀ i, tradingInput (pairedMatrix edges)
        (fun e => m.edgeDollars m.b e - m.edgeDollars m.a e) i = 0) := by
  constructor
  · intro hterm i
    have h := m.ledger_increment_eq_cumulative
      m.a m.b ⟨le_rfl, m.order⟩ ⟨m.order, le_rfl⟩ m.order i
    rw [hterm i, hinit i] at h
    simpa using h.symm
  · intro hnet i
    have h := m.ledger_increment_eq_cumulative
      m.a m.b ⟨le_rfl, m.order⟩ ⟨m.order, le_rfl⟩ m.order i
    rw [hnet i, hinit i] at h
    linarith

/-- Finite variation of each operational-clock cumulative dollar edge
is a mathematical consequence of its nonnegative physical edge rate,
rather than an independent regularity axiom in this smooth subclass. -/
theorem OperationalClockSegment.edgeDollars_finite_variation
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    {F rho : ℝ} {g : Response} {edges : κ → PairedEdge ι}
    (m : OperationalClockSegment F rho g edges) (e : κ) :
    BoundedVariationOn (fun u => m.edgeDollars u e) (Set.Icc m.a m.b) := by
  have hlocal := (m.edgeDollars_monotoneOn e).locallyBoundedVariationOn
  simpa only [Set.inter_self] using
    hlocal m.a m.b ⟨le_rfl, m.order⟩ ⟨m.order, le_rfl⟩

end MarketCrash
