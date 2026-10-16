import MarketCrash.OperationalClockLedger

/-!
A traceable admissible market-path **regular subclass** of manuscript M1-M5.

States include prices, actual executed-share holdings, per-asset signed-dollar
ledgers and physical time. Steps include price-space smooth segments, one-edge flow-completed
pulses, and joint multi-edge/resilience segments with a common physical
operational clock that can pause physical time.
Concatenation matches ALL state fields and enforces chronological ordering.

Finite execution variation is recorded per step; the inductive reachability
derivation has finitely many steps. A path starts at benchmark prices and
zero executed-dollar ledgers and ends with every dollar ledger closed.

LIMITATION: clocked segments and pulses still require differentiability in
operational dollars; arbitrary a.e. differentiable BV graph completions and
faithful inclusion of every manuscript-admissible path are NOT yet proved.
-/
noncomputable section
namespace MarketCrash

structure PhysicalMarketState (ι : Type*) where
  time : ℝ
  prices : ι → ℝ
  shares : ι → ℝ
  dollars : ι → ℝ

/-- Physical elementary steps: real price/share/dollar differential
equations, not assumed generalized-coordinate conservation. -/
inductive PhysicalMarketStep
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) :
    PhysicalMarketState ι → PhysicalMarketState ι → Prop where
  | smooth (seg : PhysicalSmoothSegment F rho g edges) :
      PhysicalMarketStep F rho g edges
        ⟨seg.a, seg.prices seg.a, seg.shares seg.a, seg.dollarLedger seg.a⟩
        ⟨seg.b, seg.prices seg.b, seg.shares seg.b, seg.dollarLedger seg.b⟩
  | pulse (atTime : ℝ) (p : FlowCompletedPulse F g edges) :
      PhysicalMarketStep F rho g edges
        ⟨atTime, p.prices 0, p.shares 0, p.dollarLedger 0⟩
        ⟨atTime, p.prices p.mass, p.shares p.mass, p.dollarLedger p.mass⟩
  | clocked (seg : OperationalClockSegment F rho g edges) :
      PhysicalMarketStep F rho g edges
        ⟨seg.physicalTime seg.a, seg.prices seg.a,
          seg.shares seg.a, seg.dollarLedger seg.a⟩
        ⟨seg.physicalTime seg.b, seg.prices seg.b,
          seg.shares seg.b, seg.dollarLedger seg.b⟩

/-- Finite execution trace with exact state continuity at every join. -/
inductive PhysicalMarketReachable
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) :
    PhysicalMarketState ι → PhysicalMarketState ι → Prop where
  | refl (s : PhysicalMarketState ι) :
      PhysicalMarketReachable F rho g edges s s
  | append {s mid t : PhysicalMarketState ι}
      (prev : PhysicalMarketReachable F rho g edges s mid)
      (step : PhysicalMarketStep F rho g edges mid t) :
      PhysicalMarketReachable F rho g edges s t

/-- M1–M5 bookkeeping for a FINITE REGULAR physical path:
positive initial benchmark prices, no short sales at the initial point,
nonnegative edge-dollar rates / holdings within each genuine physical step,
finite execution variation per step and exact zero terminal per-asset
signed-dollar ledgers. No additional positivity invariant is postulated. -/
structure AdmissibleMarketPath
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ℝ) (g : Response) (edges : κ → PairedEdge ι) where
  initial : PhysicalMarketState ι
  terminal : PhysicalMarketState ι
  trace : PhysicalMarketReachable F rho g edges initial terminal
  at_zero : initial.time = 0
  initial_prices : ∀ i, initial.prices i = F
  initial_holdings : ∀ i, 0 ≤ initial.shares i
  initial_dollars : ∀ i, initial.dollars i = 0
  terminal_dollars : ∀ i, terminal.dollars i = 0

end MarketCrash
