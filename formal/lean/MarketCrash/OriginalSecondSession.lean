import MarketCrash.PhysicalBVNormalForm
import MarketCrash.OriginalVisitedPrices

noncomputable section
namespace MarketCrash
open Set MeasureTheory
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

theorem PhysicalContinuousBVPiece.sum_coordinate_nondecreasing_below
    (m : PhysicalContinuousBVPiece edges)
    (hbelow : ∀ u ∈ Icc m.a m.b, ∀ i, m.prices u i ≤ m.F i) :
    (∑ i, coordinate (m.F i) (m.response i).impact (m.prices m.a i)) ≤
      ∑ i, coordinate (m.F i) (m.response i).impact (m.prices m.b i) := by
  have hn : ∀ i, m.rho i * (∫ u in m.a..m.b,
      m.prices u i * (m.prices u i - m.F i) / (m.response i).impact (m.prices u i)) ≤ 0 := by
    intro i
    apply mul_nonpos_of_nonneg_of_nonpos (m.resilience_nonnegative i)
    have hh : 0 ≤ ∫ u in m.a..m.b,
        -(m.prices u i * (m.prices u i - m.F i) / (m.response i).impact (m.prices u i)) := by
      apply intervalIntegral.integral_nonneg m.time_order
      intro u hu
      apply neg_nonneg.mpr
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (m.positive_prices u hu i).le (sub_nonpos.mpr (hbelow u hu i)))
        ((m.response i).positive _ (m.positive_prices u hu i)).le
    rw [intervalIntegral.integral_neg] at hh
    linarith
  have hzero := paired_trading_sum_zero edges
    (fun e => (m.execution.cumulative e) m.b - (m.execution.cumulative e) m.a)
  have hall := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn i)
  simp_rw [m.normal_form m.b ⟨m.time_order, le_rfl⟩]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hzero, add_zero]
  linarith

variable {F rho : ι → ℝ} {response : ι → Response}
variable {s t : PhysicalMarketState ι}

theorem OriginalPhysicalReachable.sum_coordinate_nondecreasing_below
    (trace : OriginalPhysicalReachable F rho response edges s t)
    (hbelow : ∀ i x, trace.Visited i x → x ≤ F i) :
    (∑ i, coordinate (F i) (response i).impact (s.prices i)) ≤
      ∑ i, coordinate (F i) (response i).impact (t.prices i) := by
  induction trace with
  | refl => exact le_rfl
  | @append mid t previous step ih =>
    have hprev := ih (fun i x hx => hbelow i x (Or.inl hx))
    apply hprev.trans
    cases step with
    | continuous m hF hr hg hv =>
      have hh := m.sum_coordinate_nondecreasing_below (fun u hu i => by
        rw [hF]
        exact hbelow i _ (Or.inr ⟨u, hu, rfl⟩))
      simpa only [hF, hg] using hh
    | pulse p hF hg hv =>
      have hh := p.potential_preserved
      change (∑ i, coordinate (p.F i) (p.response i).impact (p.prices 1 i)) =
        ∑ i, coordinate (p.F i) (p.response i).impact (p.prices 0 i) at hh
      simpa only [hF, hg] using hh.ge

/-- Theorem 7.3. The second session may have arbitrary continuous BV execution
and finitely many original pulses, asset-specific responses and benchmarks.
There is no rate cap or terminal-dollar closure premise. -/
theorem theorem_7_3_original [Nonempty ι]
    (hF : ∀ i, 0 < F i) (_hrho : ∀ i, 0 < rho i)
    (trace : OriginalPhysicalReachable F rho response edges s t)
    (q beta : ι → ℝ)
    (_hq : ∀ i, 0 < q i ∧ q i < 1)
    (hstart : ∀ i, s.prices i = q i * F i)
    (hband : ∀ i x, trace.Visited i x → x ≤ (1 + beta i) * s.prices i)
    (hcapacity : ∀ i, (1 + beta i) * q i ≤ 1) :
    ¬ ∀ i, t.prices i < s.prices i := by
  have hbelow : ∀ i x, trace.Visited i x → x ≤ F i := by
    intro i x hx
    have hc := mul_le_mul_of_nonneg_right (hcapacity i) (hF i).le
    have hb := hband i x hx
    rw [hstart] at hb
    nlinarith
  have hpot := trace.sum_coordinate_nondecreasing_below hbelow
  intro hfall
  have hp := trace.endpoint_positive (fun i => by rw [hstart]; exact mul_pos (_hq i).1 (hF i))
  have hstrict : (∑ i, coordinate (F i) (response i).impact (t.prices i)) <
      ∑ i, coordinate (F i) (response i).impact (s.prices i) := by
    apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
    intro i _
    exact coordinate_strictMonoOn (F i) (response i) (hF i) (hp i)
      (by rw [hstart]; exact mul_pos (_hq i).1 (hF i)) (hfall i)
  exact (not_lt_of_ge hpot) hstrict

end MarketCrash
