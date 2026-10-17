import MarketCrash.AdmissibleMarketPath
import MarketCrash.PhysicalContinuousBV
import MarketCrash.OriginalPulse
import Mathlib.Analysis.BoundedVariation

/-! Finite chronological economic traces built from original physical
continuous-BV primitives and integral flow-completed pulses. All joins match
time, prices, shares and dollar ledgers by a common state index. No response
coordinate identity or physical-to-weak projection is assumed here. -/
noncomputable section
namespace MarketCrash
open Set
universe u v

inductive OriginalPhysicalStep
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ι → ℝ) (response : ι → Response) (edges : κ → PairedEdge ι) :
    PhysicalMarketState ι → PhysicalMarketState ι → Type (max u v) where
  | continuous (m : PhysicalContinuousBVPiece edges)
      (fixed_benchmarks : m.F = F) (fixed_resilience : m.rho = rho)
      (fixed_response : m.response = response)
      (finite_share_variation : ∀ i,
        BoundedVariationOn (fun t => m.shares t i) (Icc m.a m.b)) :
      OriginalPhysicalStep F rho response edges
        ⟨m.a, m.prices m.a, m.shares m.a, m.dollarLedger m.a⟩
        ⟨m.b, m.prices m.b, m.shares m.b, m.dollarLedger m.b⟩
  | pulse (p : OriginalFlowCompletedPulse edges)
      (fixed_benchmarks : p.F = F) (fixed_response : p.response = response)
      (finite_share_variation : ∀ i,
        BoundedVariationOn (fun a => p.shares a i) (Icc 0 1)) :
      OriginalPhysicalStep F rho response edges
        ⟨p.physicalTime, p.prices 0, p.shares 0, p.dollarLedger 0⟩
        ⟨p.physicalTime, p.prices 1, p.shares 1, p.dollarLedger 1⟩

inductive OriginalPhysicalReachable
    {ι : Type u} {κ : Type v} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ι → ℝ) (response : ι → Response) (edges : κ → PairedEdge ι) :
    PhysicalMarketState ι → PhysicalMarketState ι → Type (max u v) where
  | refl (s : PhysicalMarketState ι) : OriginalPhysicalReachable F rho response edges s s
  | append {s mid t : PhysicalMarketState ι}
      (previous : OriginalPhysicalReachable F rho response edges s mid)
      (step : OriginalPhysicalStep F rho response edges mid t) :
      OriginalPhysicalReachable F rho response edges s t

structure OriginalAdmissiblePhysicalPath
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (F rho : ι → ℝ) (response : ι → Response) (edges : κ → PairedEdge ι) where
  benchmark_positive : ∀ i, 0 < F i
  resilience_nonnegative : ∀ i, 0 ≤ rho i
  initial : PhysicalMarketState ι
  terminal : PhysicalMarketState ι
  trace : OriginalPhysicalReachable F rho response edges initial terminal
  at_zero : initial.time = 0
  initial_prices : ∀ i, initial.prices i = F i
  initial_holdings : ∀ i, 0 ≤ initial.shares i
  initial_dollars : ∀ i, initial.dollars i = 0
  terminal_dollars : ∀ i, terminal.dollars i = 0

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {F rho : ι → ℝ} {response : ι → Response} {edges : κ → PairedEdge ι}
variable {s t u : PhysicalMarketState ι}

theorem OriginalPhysicalStep.chronological
    (h : OriginalPhysicalStep F rho response edges s t) : s.time ≤ t.time := by
  cases h with
  | continuous m _ _ _ _ => exact m.time_order
  | pulse p _ _ _ => exact le_rfl

theorem OriginalPhysicalStep.endpoint_positive
    (h : OriginalPhysicalStep F rho response edges s t) :
    (∀ i, 0 < s.prices i) ∧ ∀ i, 0 < t.prices i := by
  cases h with
  | continuous m _ _ _ _ =>
    exact ⟨m.positive_prices m.a ⟨le_rfl, m.time_order⟩,
      m.positive_prices m.b ⟨m.time_order, le_rfl⟩⟩
  | pulse p _ _ _ =>
    exact ⟨p.positive_prices 0 ⟨le_rfl, by norm_num⟩,
      p.positive_prices 1 ⟨by norm_num, le_rfl⟩⟩

theorem OriginalPhysicalStep.endpoint_no_short
    (h : OriginalPhysicalStep F rho response edges s t) :
    (∀ i, 0 ≤ s.shares i) ∧ ∀ i, 0 ≤ t.shares i := by
  cases h with
  | continuous m _ _ _ _ =>
    exact ⟨m.no_short_sales m.a ⟨le_rfl, m.time_order⟩,
      m.no_short_sales m.b ⟨m.time_order, le_rfl⟩⟩
  | pulse p _ _ _ =>
    exact ⟨p.no_short_sales 0 ⟨le_rfl, by norm_num⟩,
      p.no_short_sales 1 ⟨by norm_num, le_rfl⟩⟩

theorem OriginalPhysicalStep.dollar_sum_preserved
    (h : OriginalPhysicalStep F rho response edges s t) :
    (∑ i, t.dollars i) = ∑ i, s.dollars i := by
  cases h with
  | continuous m _ _ _ _ =>
    change (∑ i, m.dollarLedger m.b i) = ∑ i, m.dollarLedger m.a i
    have hh : (∑ i, (m.dollarLedger m.b i - m.dollarLedger m.a i)) = 0 := by
      simp_rw [m.marginal_dollar_primitive _ m.a ⟨le_rfl, m.time_order⟩ m.b ⟨m.time_order, le_rfl⟩]
      exact paired_trading_sum_zero edges _
    rw [Finset.sum_sub_distrib] at hh
    linarith
  | pulse p _ _ _ =>
    change (∑ i, p.dollarLedger 1 i) = ∑ i, p.dollarLedger 0 i
    simp_rw [p.ledger_endpoint]
    rw [Finset.sum_add_distrib, paired_trading_sum_zero, add_zero]

theorem OriginalPhysicalReachable.chronological
    (h : OriginalPhysicalReachable F rho response edges s t) : s.time ≤ t.time := by
  induction h with
  | refl => exact le_rfl
  | append previous step ih => exact ih.trans step.chronological

theorem OriginalPhysicalReachable.endpoint_positive
    (h : OriginalPhysicalReachable F rho response edges s t)
    (hs : ∀ i, 0 < s.prices i) : ∀ i, 0 < t.prices i := by
  induction h with
  | refl => exact hs
  | append previous step ih => exact step.endpoint_positive.2

theorem OriginalPhysicalReachable.endpoint_no_short
    (h : OriginalPhysicalReachable F rho response edges s t)
    (hs : ∀ i, 0 ≤ s.shares i) : ∀ i, 0 ≤ t.shares i := by
  induction h with
  | refl => exact hs
  | append previous step ih => exact step.endpoint_no_short.2

theorem OriginalPhysicalReachable.dollar_sum_preserved
    (h : OriginalPhysicalReachable F rho response edges s t) :
    (∑ i, t.dollars i) = ∑ i, s.dollars i := by
  induction h with
  | refl => rfl
  | append previous step ih => exact step.dollar_sum_preserved.trans ih

theorem OriginalAdmissiblePhysicalPath.endpoint_conditions
    (p : OriginalAdmissiblePhysicalPath F rho response edges) :
    0 ≤ p.terminal.time ∧ (∀ i, 0 < p.terminal.prices i) ∧
      (∀ i, 0 ≤ p.terminal.shares i) ∧ (∑ i, p.terminal.dollars i) = 0 := by
  refine ⟨?_, p.trace.endpoint_positive ?_, p.trace.endpoint_no_short p.initial_holdings, ?_⟩
  · simpa [p.at_zero] using p.trace.chronological
  · intro i
    rw [p.initial_prices i]
    exact p.benchmark_positive i
  · rw [p.trace.dollar_sum_preserved]
    simp [p.initial_dollars]

end MarketCrash
