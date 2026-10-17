import MarketCrash.Coordinates
import MarketCrash.Conservation
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.Rademacher

/-!
Physical integral formulation of an absolutely continuous session.
The primitive equation is for the ORIGINAL level price, not Phi(price).
Parameters may depend on the asset. No transformed endpoint identity is
assumed. Holdings and terminal closure are immaterial to the necessary cut
bound, so this projection deliberately includes paths without those rules.

Absolute continuity is represented by its integrable-primitive
characterization. The a.e. physical differential law is retained explicitly;
it does not replace the primitive equation (which excludes Cantor paths).
-/
noncomputable section
namespace MarketCrash
open MeasureTheory Set
open scoped NNReal

structure ACPhysicalSession {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (edges : κ → PairedEdge ι) where
  a : ℝ
  b : ℝ
  time_order : a < b
  F : ι → ℝ
  rho : ι → ℝ
  response : ι → Response
  benchmark_positive : ∀ i, 0 < F i
  resilience_nonnegative : ∀ i, 0 ≤ rho i
  prices : ℝ → ι → ℝ
  rates : ℝ → κ → ℝ
  edgeDollars : ℝ → κ → ℝ
  continuous_prices : ∀ i, ContinuousOn (fun t => prices t i) (Icc a b)
  positive_prices : ∀ t ∈ Icc a b, ∀ i, 0 < prices t i
  rates_integrable : ∀ e, IntervalIntegrable (fun t => rates t e) volume a b
  nonnegative_rates : ∀ᵐ t ∂volume, t ∈ Icc a b → ∀ e, 0 ≤ rates t e
  edge_primitive : ∀ e, ∀ t ∈ Icc a b,
    edgeDollars t e - edgeDollars a e = ∫ u in a..t, rates u e
  edge_derivative : ∀ᵐ t ∂volume, t ∈ Icc a b → ∀ e,
    HasDerivAt (fun u => edgeDollars u e) (rates t e) t
  physical_primitive : ∀ i, ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
    prices t i - prices s i =
      ∫ u in s..t, (-rho i * (prices u i - F i) +
        (response i).impact (prices u i) *
          (tradingInput (pairedMatrix edges) (rates u) i / prices u i))
  physical_derivative : ∀ᵐ t ∂volume, t ∈ Icc a b → ∀ i,
    HasDerivAt (fun u => prices u i)
      (-rho i * (prices t i - F i) +
        (response i).impact (prices t i) *
          (tradingInput (pairedMatrix edges) (rates t) i / prices t i)) t

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {edges : κ → PairedEdge ι}

/-- Dollars executed on directed edges, counted once. -/
def ACPhysicalSession.turnover (m : ACPhysicalSession edges) : ℝ :=
  ∫ t in m.a..m.b, ∑ e, m.rates t e

/-- The actual per-asset ledger from marginal matched-dollar execution. -/
def ACPhysicalSession.ledger (m : ACPhysicalSession edges) (t : ℝ) (i : ι) : ℝ :=
  tradingInput (pairedMatrix edges) (fun e => m.edgeDollars t e - m.edgeDollars m.a e) i

/-- Gross shares count each incident edge, before netting opposing trades. -/
def ACPhysicalSession.gross (m : ACPhysicalSession edges) (t : ℝ) (i : ι) : ℝ :=
  (∑ e, |pairedMatrix edges i e| * m.rates t e) / m.prices t i

def ACPhysicalSession.RateBounded (m : ACPhysicalSession edges) (v : ℝ) : Prop :=
  0 ≤ v ∧ ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → ∀ i, m.gross t i ≤ v

/-- The signed marginal dollar rate cannot exceed gross dollars. -/
theorem ACPhysicalSession.local_capacity (m : ACPhysicalSession edges) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → ∀ i,
      0 ≤ m.gross t i ∧
      |tradingInput (pairedMatrix edges) (m.rates t) i| ≤
        m.prices t i * m.gross t i := by
  filter_upwards [m.nonnegative_rates] with t ht hmem i
  have hp := m.positive_prices t hmem i
  have hn : 0 ≤ ∑ e, |pairedMatrix edges i e| * m.rates t e :=
    Finset.sum_nonneg fun e _ => mul_nonneg (abs_nonneg _) (ht hmem e)
  refine ⟨div_nonneg hn hp.le, ?_⟩
  calc
    |tradingInput (pairedMatrix edges) (m.rates t) i| ≤
        ∑ e, |pairedMatrix edges i e * m.rates t e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ e, |pairedMatrix edges i e| * m.rates t e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [abs_mul, abs_of_nonneg (ht hmem e)]
    _ = m.prices t i * m.gross t i := by
      dsimp [ACPhysicalSession.gross]
      field_simp

/-- The manuscript instantaneous inequality for the genuine executed-dollar
rates of every integral-form AC physical session. -/
theorem ACPhysicalSession.cut_rate_ae (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (J : Finset ι) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b →
      |∑ i ∈ J, tradingInput (pairedMatrix edges) (m.rates t) i| ≤
        v * min (∑ i ∈ J, m.prices t i)
          (∑ i ∈ Finset.univ \ J, m.prices t i) := by
  filter_upwards [m.local_capacity, hv.2] with t ht hcap hmem
  exact market_cut_instantaneous_bound _ (paired_column_sum edges)
    (m.rates t) J (m.prices t) (m.gross t) v hv.1
    (fun i => (m.positive_prices t hmem i).le)
    (fun i => ⟨(ht hmem i).1, hcap hmem i⟩)
    (fun i => (ht hmem i).2)

/-- A bounded integrable primitive has a Lipschitz restriction. This
derivation uses interval integrals, not inference from a.e. derivatives. -/
theorem lipschitzOn_of_bounded_primitive (f w : ℝ → ℝ) (a b : ℝ)
    (C : ℝ≥0)
    (hprim : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      f t - f s = ∫ u in s..t, w u)
    (hbound : ∀ᵐ u ∂volume, u ∈ Icc a b → |w u| ≤ C) :
    LipschitzOnWith C f (Icc a b) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs t ht
  rw [Real.dist_eq, hprim t ht s hs, Real.dist_eq]
  have hb : ∀ᵐ u ∂volume, u ∈ uIoc t s → ‖w u‖ ≤ C := by
    filter_upwards [hbound] with u hu hmem
    exact hu ⟨le_trans (le_min ht.1 hs.1) hmem.1.le,
      le_trans hmem.2 (max_le ht.2 hs.2)⟩
  simpa only [Real.norm_eq_abs] using
    intervalIntegral.norm_integral_le_of_norm_le_const_ae hb

/-- Under the original gross-rate bound, Lipschitz regularity of prices
is a CONSEQUENCE of the physical integral equation and compactness. -/
theorem ACPhysicalSession.prices_lipschitz (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (i : ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C (fun t => m.prices t i) (Icc m.a m.b) := by
  have hg : ContinuousOn (fun t => (m.response i).impact (m.prices t i))
      (Icc m.a m.b) :=
    (m.response i).continuousOn_positive.comp (m.continuous_prices i)
      (fun t ht => m.positive_prices t ht i)
  let bound : ℝ → ℝ := fun t =>
    m.rho i * |m.prices t i - m.F i| + (m.response i).impact (m.prices t i) * v
  have hc : ContinuousOn bound (Icc m.a m.b) :=
    (continuousOn_const.mul ((m.continuous_prices i).sub continuousOn_const).abs).add
      (hg.mul continuousOn_const)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  let C : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  refine ⟨C, lipschitzOn_of_bounded_primitive _ _ m.a m.b C
    (m.physical_primitive i) ?_⟩
  filter_upwards [m.local_capacity, hv.2] with t ht hcap hmem
  have hp := m.positive_prices t hmem i
  have him := (m.response i).positive _ hp
  have hnet : |tradingInput (pairedMatrix edges) (m.rates t) i / m.prices t i| ≤ v := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact (ht hmem i).2.trans (by nlinarith [hcap hmem i])
  calc
    |-m.rho i * (m.prices t i - m.F i) +
      (m.response i).impact (m.prices t i) *
        (tradingInput (pairedMatrix edges) (m.rates t) i / m.prices t i)|
        ≤ |-m.rho i * (m.prices t i - m.F i)| +
          |(m.response i).impact (m.prices t i) *
            (tradingInput (pairedMatrix edges) (m.rates t) i / m.prices t i)| := abs_add_le _ _
    _ ≤ bound t := by
      rw [abs_mul, abs_neg, abs_of_nonneg (m.resilience_nonnegative i),
        abs_mul, abs_of_pos him]
      exact add_le_add_left (mul_le_mul_of_nonneg_left hnet him.le) _
    _ ≤ B := hB (mem_image_of_mem _ hmem)
    _ ≤ C := le_max_left _ _

/-- Phi composed with a rate-bounded physical price is Lipschitz on the
session. Compact positive price bounds are derived, not extra premises. -/
theorem ACPhysicalSession.coordinate_lipschitz (m : ACPhysicalSession edges)
    (v : ℝ) (hv : m.RateBounded v) (i : ι) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun t => coordinate (m.F i) (m.response i).impact (m.prices t i))
      (Icc m.a m.b) := by
  have hne : (Icc m.a m.b).Nonempty := ⟨m.a, le_rfl, m.time_order.le⟩
  obtain ⟨l, hl, hmin⟩ := isCompact_Icc.exists_isMinOn hne (m.continuous_prices i)
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn hne (m.continuous_prices i)
  let L := m.prices l i
  let U := m.prices u i
  have hL : 0 < L := m.positive_prices l hl i
  have hsub : Icc L U ⊆ positivePrices := fun x hx => hL.trans_le hx.1
  have hg := (m.response i).continuousOn_positive.mono hsub
  have hc : ContinuousOn (fun x : ℝ => ‖x / (m.response i).impact x‖) (Icc L U) :=
    (continuousOn_id.div hg (fun x hx => ((m.response i).positive x (hsub hx)).ne')).norm
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hc
  let D : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hphi : LipschitzOnWith D (coordinate (m.F i) (m.response i).impact) (Icc L U) := by
    apply (convex_Icc L U).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (coordinate_hasDerivAt _ _ (m.benchmark_positive i) (hsub hx)).hasDerivWithinAt)
    intro x hx
    change ‖x / (m.response i).impact x‖ ≤ max B 0
    exact (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  obtain ⟨C, hC⟩ := m.prices_lipschitz v hv i
  refine ⟨D * C, ?_⟩
  exact hphi.comp hC (fun t ht => ⟨hmin ht, hmax ht⟩)

/-- Chain rule is deduced from the physical level-price equation a.e. -/
theorem ACPhysicalSession.coordinate_derivative (m : ACPhysicalSession edges) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → ∀ i,
      HasDerivAt (fun u => coordinate (m.F i) (m.response i).impact (m.prices u i))
        (tradingInput (pairedMatrix edges) (m.rates t) i -
          m.rho i * (m.prices t i * (m.prices t i - m.F i) /
            (m.response i).impact (m.prices t i))) t := by
  filter_upwards [m.physical_derivative] with t ht hmem i
  have hp := (m.positive_prices t hmem i).ne'
  have hg := ((m.response i).positive _ (m.positive_prices t hmem i)).ne'
  have hd := (coordinate_hasDerivAt (m.F i) (m.response i) (m.benchmark_positive i)
    (m.positive_prices t hmem i)).comp t (ht hmem i)
  convert hd using 1 <;> dsimp [Function.comp] <;> field_simp [hp, hg] <;> ring

/-- The rate is the derivative of the actual physical dollar ledger. -/
theorem ACPhysicalSession.ledger_derivative (m : ACPhysicalSession edges) :
    ∀ᵐ t ∂volume, t ∈ Icc m.a m.b → ∀ i,
      HasDerivAt (fun u => m.ledger u i)
        (tradingInput (pairedMatrix edges) (m.rates t) i) t := by
  filter_upwards [m.edge_derivative] with t ht hmem i
  exact HasDerivAt.sum (u := Finset.univ) (fun e _ =>
    ((ht hmem e).sub_const (m.edgeDollars m.a e)).const_mul (pairedMatrix edges i e))

end MarketCrash
