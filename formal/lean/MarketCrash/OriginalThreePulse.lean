import MarketCrash.PhysicalPulseConstruction
import MarketCrash.ScalarSecondJet
import MarketCrash.TwoPulseScalar
import MarketCrash.PairedControlConstruction
import MarketCrash.CompletePairedEmbedding

noncomputable section
open Set MeasureTheory
namespace MarketCrash

def recoveryPrices {ι : Type*} (F rho S : ι → ℝ) (a t : ℝ) (i : ι) : ℝ :=
  F i + (S i - F i) * Real.exp (-rho i * (t - a))

theorem recoveryPrices_hasDerivAt {ι : Type*} (F rho S : ι → ℝ) (a t : ℝ) (i : ι) :
    HasDerivAt (fun u => recoveryPrices F rho S a u i)
      (-rho i * (recoveryPrices F rho S a t i - F i)) t := by
  have hh := (((hasDerivAt_id t).sub_const a).const_mul (-rho i)).exp
  convert (hh.const_mul (S i - F i)).const_add (F i) using 1
  dsimp [recoveryPrices]
  ring

def originalRecoveryPiece {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (a b : ℝ) (hab : a ≤ b)
    (F rho S θ ℓ : ι → ℝ) (g : ι → Response)
    (hF : ∀ i, 0 < F i) (hρ : ∀ i, 0 ≤ rho i)
    (hS : ∀ i, 0 < S i) (hθ : ∀ i, 0 ≤ θ i) : PhysicalContinuousBVPiece edges := by
  let Z : StieltjesPairedExecution edges := ⟨fun _ => StieltjesFunction.const 0⟩
  have hcont : ∀ i, Continuous (fun t => recoveryPrices F rho S a t i) := by
    intro i
    unfold recoveryPrices
    fun_prop
  refine {
    a := a
    b := b
    time_order := hab
    F := F
    rho := rho
    response := g
    benchmark_positive := hF
    resilience_nonnegative := hρ
    execution := Z
    continuous_execution := fun _ => continuousOn_const
    prices := recoveryPrices F rho S a
    shares := fun _ => θ
    dollarLedger := fun _ => ℓ
    continuous_prices := fun i => (hcont i).continuousOn
    positive_prices := ?_
    no_short_sales := fun _ _ => hθ
    physical_price_primitive := ?_
    physical_share_primitive := ?_
    marginal_dollar_primitive := ?_ }
  · intro t ht i
    have hr := Real.exp_pos (-rho i * (t - a))
    have hr1 : Real.exp (-rho i * (t - a)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [hρ i, ht.1])
    unfold recoveryPrices
    nlinarith [hF i, hS i, mul_pos (hS i) hr,
      mul_nonneg (hF i).le (sub_nonneg.mpr hr1)]
  · intro i s _ t _
    have hi : Continuous (fun u => -rho i * (recoveryPrices F rho S a u i - F i)) :=
      continuous_const.mul ((hcont i).sub continuous_const)
    have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => recoveryPrices_hasDerivAt F rho S a u i) (hi.intervalIntegrable s t)
    simpa [Z, StieltjesFunction.measure_const, intervalIntegral] using hh.symm
  · intro i s _ t _
    simp [Z, StieltjesFunction.measure_const, intervalIntegral]
  · intro i s _ t _
    simp [Z, tradingInput]

theorem original_recovery_reachable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (a b : ℝ) (hab : a ≤ b)
    (F rho S θ ℓ : ι → ℝ) (g : ι → Response)
    (hF : ∀ i, 0 < F i) (hρ : ∀ i, 0 ≤ rho i)
    (hS : ∀ i, 0 < S i) (hθ : ∀ i, 0 ≤ θ i) :
    Nonempty (OriginalPhysicalReachable F rho g edges ⟨a, S, θ, ℓ⟩
      ⟨b, recoveryPrices F rho S a b, θ, ℓ⟩) := by
  let m := originalRecoveryPiece edges a b hab F rho S θ ℓ g hF hρ hS hθ
  have hBV : ∀ i, BoundedVariationOn (fun t => m.shares t i) (Icc m.a m.b) := by
    intro i
    unfold BoundedVariationOn
    rw [eVariationOn.constant_on (by
      rintro y ⟨x, hx, rfl⟩ z ⟨w, hw, rfl⟩
      rfl)]
    exact ENNReal.zero_ne_top
  have hs := OriginalPhysicalStep.continuous m rfl rfl rfl hBV
  have hstart : recoveryPrices F rho S a a = S := by
    funext i
    simp [recoveryPrices]
  have hs' : OriginalPhysicalStep F rho g edges ⟨a, S, θ, ℓ⟩
      ⟨b, recoveryPrices F rho S a b, θ, ℓ⟩ := by
    simpa only [m, originalRecoveryPiece, hstart] using hs
  exact ⟨.append (.refl _) hs'⟩

theorem chart_recovery_reachable
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (a b : ℝ) (hab : a ≤ b)
    (F rho : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i) (hρ : ∀ i, 0 ≤ rho i)
    (R : ι → ℝ → ℝ) (ε H x y ℓ : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hR : ∀ i, ContinuousOn (R i) (Metric.ball 0 (2 * ε i)))
    (hp : ∀ i, ∀ u ∈ Metric.ball 0 (2 * ε i), 0 < R i u ∧
      coordinate (F i) (g i).impact (R i u) = u)
    (hx : ∀ i, x i ∈ Icc (-ε i) (ε i)) (hy : ∀ i, y i ∈ Icc (-ε i) (ε i))
    (hstock : ∀ i, chartInventoryReserve (R i) (ε i) ≤ H i)
    (hycoord : ∀ i, y i = coordinate (F i) (g i).impact
      (recoveryPrices F rho (fun j => R j (x j)) a b i)) :
    Nonempty (OriginalPhysicalReachable F rho g edges (chartState a R H x ℓ)
      (chartState b R
        (fun i => H i + chartSharePrimitive (R i) (x i) - chartSharePrimitive (R i) (y i)) y ℓ)) := by
  have hs : ∀ i, Icc (-ε i) (ε i) ⊆ Metric.ball 0 (2 * ε i) := by
    intro i u hu
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [hu.1, hu.2, hε i]
  have hS : ∀ i, 0 < R i (x i) := fun i => (hp i _ (hs i (hx i))).1
  have hθ : ∀ i, 0 ≤ H i + chartSharePrimitive (R i) (x i) := by
    intro i
    have hh := (chart_share_regular (R i) (ε i) (hε i) (hR i)
      (fun u hu => (hp i u hu).1)).2.2 _ (hx i)
    linarith [hstock i]
  have hrec := original_recovery_reachable edges a b hab F rho (fun i => R i (x i))
    (fun i => H i + chartSharePrimitive (R i) (x i)) ℓ g hF hρ hS hθ
  have hSrec : ∀ i, 0 < recoveryPrices F rho (fun j => R j (x j)) a b i := by
    intro i
    have hr := Real.exp_pos (-rho i * (b - a))
    have hr1 := Real.exp_le_one_iff.mpr (show -rho i * (b - a) ≤ 0 by nlinarith [hρ i])
    dsimp [recoveryPrices]
    nlinarith [hF i, hS i, mul_pos (hS i) hr,
      mul_nonneg (hF i).le (sub_nonneg.mpr hr1)]
  have hRy : ∀ i, R i (y i) = recoveryPrices F rho (fun j => R j (x j)) a b i := by
    intro i
    apply (coordinate_strictMonoOn (F i) (g i) (hF i)).injOn
      (hp i _ (hs i (hy i))).1 (hSrec i)
    exact (hp i _ (hs i (hy i))).2.trans (hycoord i)
  have he : chartState b R
        (fun i => H i + chartSharePrimitive (R i) (x i) - chartSharePrimitive (R i) (y i)) y ℓ =
      (⟨b, recoveryPrices F rho (fun i => R i (x i)) a b,
        (fun i => H i + chartSharePrimitive (R i) (x i)), ℓ⟩ : PhysicalMarketState ι) := by
    unfold chartState
    congr 1
    · funext i
      exact hRy i
    · funext i
      ring
  rw [he]
  exact hrec

def vectorRecoveryCoordinate {ι : Type*} (F rho : ι → ℝ) (g : ι → Response)
    (R : ι → ℝ → ℝ) (a b : ℝ) (x : ι → ℝ) (i : ι) : ℝ :=
  coordinate (F i) (g i).impact (recoveryPrices F rho (fun j => R j (x j)) a b i)

theorem vectorRecoveryCoordinate_tendsto_zero {ι : Type*}
    (F rho : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i)
    (R : ι → ℝ → ℝ) (hR0 : ∀ i, R i 0 = F i)
    (hR : ∀ i, ContinuousAt (R i) 0) (a b : ℝ) (x : ℝ → ι → ℝ)
    (hx : ∀ i, Filter.Tendsto (fun h => x h i) (nhds 0) (nhds 0)) :
    ∀ i, Filter.Tendsto (fun h => vectorRecoveryCoordinate F rho g R a b (x h) i)
      (nhds 0) (nhds 0) := by
  intro i
  have ht := (hR i).tendsto.comp (hx i)
  have ht' : Filter.Tendsto (fun h => recoveryPrices F rho (fun j => R j (x h j)) a b i)
      (nhds 0) (nhds (F i)) := by
    simpa [recoveryPrices, hR0 i] using
      Filter.Tendsto.const_add (F i)
        (((ht.sub_const (F i)).mul_const (Real.exp (-rho i * (b-a)))))
  simpa only [coordinate_at_benchmark] using
    (coordinate_hasDerivAt (F i) (g i) (hF i) (hF i)).continuousAt.tendsto.comp ht'

def threeVectorFinalCoordinate {ι : Type*} (F rho : ι → ℝ) (g : ι → Response)
    (R : ι → ℝ → ℝ) (b c : ℝ) (v₁ v₂ v₃ : ι → ℝ) (h : ℝ) : ι → ℝ :=
  fun i => vectorRecoveryCoordinate F rho g R b c
    (fun j => vectorRecoveryCoordinate F rho g R 0 b (fun k => h * v₁ k) j + h * v₂ j) i + h * v₃ i

theorem three_vector_original_path
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (edges : κ → PairedEdge ι) (b c : ℝ) (hb : 0 ≤ b) (hbc : b ≤ c)
    (F rho : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i) (hρ : ∀ i, 0 ≤ rho i)
    (R : ι → ℝ → ℝ) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i)
    (hR0 : ∀ i, R i 0 = F i)
    (hR : ∀ i, ContinuousOn (R i) (Metric.ball 0 (2 * ε i)))
    (hp : ∀ i, ∀ y ∈ Metric.ball 0 (2 * ε i), 0 < R i y ∧
      coordinate (F i) (g i).impact (R i y) = y ∧
      HasDerivAt (R i) ((g i).impact (R i y) / R i y) y)
    (d₁ d₂ d₃ : κ → ℝ) (hd₁ : ∀ e, 0 ≤ d₁ e) (hd₂ : ∀ e, 0 ≤ d₂ e) (hd₃ : ∀ e, 0 ≤ d₃ e)
    (hclosed : ∀ i, tradingInput (pairedMatrix edges) d₁ i +
      tradingInput (pairedMatrix edges) d₂ i + tradingInput (pairedMatrix edges) d₃ i = 0) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0),
      ∃ p : OriginalAdmissiblePhysicalPath F rho g edges,
        p.terminal.time = c ∧ ∀ i, p.terminal.prices i =
          R i (threeVectorFinalCoordinate F rho g R b c
            (tradingInput (pairedMatrix edges) d₁) (tradingInput (pairedMatrix edges) d₂)
            (tradingInput (pairedMatrix edges) d₃) h i) := by
  let v₁ := tradingInput (pairedMatrix edges) d₁
  let v₂ := tradingInput (pairedMatrix edges) d₂
  let v₃ := tradingInput (pairedMatrix edges) d₃
  let H : ι → ℝ := fun i => chartInventoryReserve (R i) (ε i) + 1
  let x₁ : ℝ → ι → ℝ := fun h i => h * v₁ i
  let y₁ : ℝ → ι → ℝ := fun h => vectorRecoveryCoordinate F rho g R 0 b (x₁ h)
  let x₂ : ℝ → ι → ℝ := fun h i => y₁ h i + h * v₂ i
  let y₂ : ℝ → ι → ℝ := fun h => vectorRecoveryCoordinate F rho g R b c (x₂ h)
  let x₃ : ℝ → ι → ℝ := fun h i => y₂ h i + h * v₃ i
  let H₂ : ℝ → ι → ℝ := fun h i => H i + chartSharePrimitive (R i) (x₁ h i) - chartSharePrimitive (R i) (y₁ h i)
  let H₃ : ℝ → ι → ℝ := fun h i => H₂ h i + chartSharePrimitive (R i) (x₂ h i) - chartSharePrimitive (R i) (y₂ h i)
  have hRcont : ∀ i, ContinuousAt (R i) 0 := fun i =>
    (hR i).continuousAt (Metric.isOpen_ball.mem_nhds (by simpa using (show (0 : ℝ) < 2 * ε i by linarith [hε i])))
  have hx₁ : ∀ i, Filter.Tendsto (fun h => x₁ h i) (nhds 0) (nhds 0) := fun i => by
    simpa [x₁] using (show Filter.Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) from Filter.tendsto_id).mul_const (v₁ i)
  have hy₁ := vectorRecoveryCoordinate_tendsto_zero F rho g hF R hR0 hRcont 0 b x₁ hx₁
  have hx₂ : ∀ i, Filter.Tendsto (fun h => x₂ h i) (nhds 0) (nhds 0) := fun i => by
    simpa [x₂] using (hy₁ i).add (Filter.tendsto_id.mul_const (v₂ i))
  have hy₂ := vectorRecoveryCoordinate_tendsto_zero F rho g hF R hR0 hRcont b c x₂ hx₂
  have hA (x : ℝ → ι → ℝ) (hx : ∀ i, Filter.Tendsto (fun h => x h i) (nhds 0) (nhds 0)) (i : ι) :=
    chartSharePrimitive_tendsto_zero (R i) (ε i) (hε i) (hR i) (fun u hu => (hp i u hu).1) (fun h => x h i) (hx i)
  have hH₂ : ∀ i, Filter.Tendsto (fun h => H₂ h i) (nhds 0) (nhds (H i)) := fun i => by
    simpa [H₂] using ((hA x₁ hx₁ i).const_add (H i)).sub (hA y₁ hy₁ i)
  have hH₃ : ∀ i, Filter.Tendsto (fun h => H₃ h i) (nhds 0) (nhds (H i)) := fun i => by
    simpa [H₃] using ((hH₂ i).add (hA x₂ hx₂ i)).sub (hA y₂ hy₂ i)
  have hH : ∀ i, chartInventoryReserve (R i) (ε i) < H i := fun i => by dsimp [H]; linarith
  have hstock₂ := eventual_chart_inventory_reserve R ε H hH H₂ hH₂
  have hstock₃ := eventual_chart_inventory_reserve R ε H hH H₃ hH₃
  have hinside (x : ℝ → ι → ℝ) (hx : ∀ i, Filter.Tendsto (fun h => x h i) (nhds 0) (nhds 0)) :
      ∀ᶠ h in nhds 0, ∀ i, x h i ∈ Icc (-ε i) (ε i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact ((hx i).eventually (Ioo_mem_nhds (by linarith [hε i]) (hε i))).mono (fun _ hu => ⟨hu.1.le, hu.2.le⟩)
  have htrace₁ := small_dollar_vector_reachable edges 0 F rho g hF R ε hε hR hp d₁ hd₁
    (fun _ _ => 0) (fun _ => tendsto_const_nhds)
  have htrace₂ := small_dollar_vector_reachable edges b F rho g hF R ε hε hR hp d₂ hd₂ y₁ hy₁
  have htrace₃ := small_dollar_vector_reachable edges c F rho g hF R ε hε hR hp d₃ hd₃ y₂ hy₂
  filter_upwards [htrace₁, htrace₂, htrace₃,
    hstock₂.filter_mono nhdsWithin_le_nhds, hstock₃.filter_mono nhdsWithin_le_nhds,
    (hinside x₁ hx₁).filter_mono nhdsWithin_le_nhds,
    (hinside y₁ hy₁).filter_mono nhdsWithin_le_nhds,
    (hinside x₂ hx₂).filter_mono nhdsWithin_le_nhds,
    (hinside y₂ hy₂).filter_mono nhdsWithin_le_nhds] with h ht₁ ht₂ ht₃ hs₂ hs₃ hi₁ hj₁ hi₂ hj₂
  let ℓ₁ : ι → ℝ := fun i => h * v₁ i
  let ℓ₂ : ι → ℝ := fun i => h * v₁ i + h * v₂ i
  obtain ⟨p₁⟩ := ht₁ H (fun _ => 0) (fun i => (hH i).le)
  have p₁' : OriginalPhysicalReachable F rho g edges
      (chartState 0 R H (fun _ => 0) (fun _ => 0)) (chartState 0 R H (x₁ h) ℓ₁) := by
    simpa only [zero_add] using p₁
  obtain ⟨r₁⟩ := chart_recovery_reachable edges 0 b hb F rho g hF hρ R ε H (x₁ h) (y₁ h) ℓ₁ hε hR
    (fun i u hu => ⟨(hp i u hu).1, (hp i u hu).2.1⟩) hi₁ hj₁ (fun i => (hH i).le) (fun _ => rfl)
  obtain ⟨p₂⟩ := ht₂ (H₂ h) ℓ₁ hs₂
  have p₂' : OriginalPhysicalReachable F rho g edges
      (chartState b R (H₂ h) (y₁ h) ℓ₁) (chartState b R (H₂ h) (x₂ h) ℓ₂) := p₂
  obtain ⟨r₂⟩ := chart_recovery_reachable edges b c hbc F rho g hF hρ R ε (H₂ h) (x₂ h) (y₂ h) ℓ₂ hε hR
    (fun i u hu => ⟨(hp i u hu).1, (hp i u hu).2.1⟩) hi₂ hj₂ hs₂ (fun _ => rfl)
  obtain ⟨p₃⟩ := ht₃ (H₃ h) ℓ₂ hs₃
  have hℓ : (fun i => ℓ₂ i + h * tradingInput (pairedMatrix edges) d₃ i) = fun _ => 0 := by
    funext i
    have hh := congrArg (fun z => h * z) (hclosed i)
    dsimp [ℓ₂, v₁, v₂] at *
    nlinarith
  rw [hℓ] at p₃
  let trace := original_reachable_trans (original_reachable_trans
    (original_reachable_trans (original_reachable_trans p₁' r₁) p₂') r₂) p₃
  have hinit : ∀ i, 0 ≤ H i + chartSharePrimitive (R i) 0 := by
    intro i
    have hh := (chart_share_regular (R i) (ε i) (hε i) (hR i)
      (fun u hu => (hp i u hu).1)).2.2 0 ⟨by linarith [hε i], (hε i).le⟩
    linarith [hH i]
  let p : OriginalAdmissiblePhysicalPath F rho g edges := {
    benchmark_positive := hF
    resilience_nonnegative := hρ
    initial := chartState 0 R H (fun _ => 0) (fun _ => 0)
    terminal := chartState c R (H₃ h) (x₃ h) (fun _ => 0)
    trace := trace
    at_zero := rfl
    initial_prices := hR0
    initial_holdings := hinit
    initial_dollars := fun _ => rfl
    terminal_dollars := fun _ => rfl }
  exact ⟨p, rfl, fun _ => rfl⟩

theorem exists_asset_response_charts {ι : Type*}
    (F : ι → ℝ) (g : ι → Response) (hF : ∀ i, 0 < F i)
    (hg : ∀ i, ContDiffAt ℝ 3 (g i).impact (F i)) :
    ∃ (R : ι → ℝ → ℝ) (ε : ι → ℝ),
      (∀ i, 0 < ε i) ∧ (∀ i, R i 0 = F i) ∧
      (∀ i, ContDiffOn ℝ 3 (R i) (Metric.ball 0 (2 * ε i))) ∧
      ∀ i, ∀ y ∈ Metric.ball 0 (2 * ε i), 0 < R i y ∧
        coordinate (F i) (g i).impact (R i y) = y ∧
        HasDerivAt (R i) ((g i).impact (R i y) / R i y) y := by
  choose R δ hδ hR0 hR hp using fun i => exists_local_response_chart (F i) (g i) (hF i) (hg i)
  refine ⟨R, fun i => δ i / 2, fun i => half_pos (hδ i), hR0, ?_, ?_⟩
  · intro i
    have he : 2 * (δ i / 2) = δ i := by ring
    rw [he]
    exact hR i
  · intro i y hy
    apply hp i y
    have he : 2 * (δ i / 2) = δ i := by ring
    rwa [he] at hy

def threePulseEndpoint (Phi R : ℝ → ℝ) (F r u h : ℝ) : ℝ :=
  R (Phi (F + r * (R (Phi (F + r * (R (u * h) - F)) - (1 + r) * u * h) - F)) + r * u * h)

theorem threePulseEndpoint_second_jet (Phi R : ℝ → ℝ) (F A B r u : ℝ)
    (hA : A ≠ 0) (hR : ScalarSecondJet R 0 F A B)
    (hPhi : ScalarSecondJet Phi F 0 (1/A) (-B/A^3)) :
    ScalarSecondJet (threePulseEndpoint Phi R F r u) 0 F 0
      (B * r * (1-r^2) * u^2) := by
  let Q : ℝ → ℝ := fun y => Phi (F + r * (R y - F))
  have jq : ScalarSecondJet Q 0 0 r ((B/A)*r*(1-r)) := by
    have j0 := (scalarSecondJet_const F 0).add ((hR.sub (scalarSecondJet_const F 0)).scale r)
    have j0' : ScalarSecondJet (fun y => F + r * (R y - F)) 0 F (r*A) (r*B) := by
      convert j0 using 1 <;> ring
    have j1 := hPhi.comp j0'
    convert j1 using 1 <;> dsimp [Q, Function.comp_def]
    · field_simp [hA]
    · field_simp [hA]
      ring
  have jl : ScalarSecondJet (fun h => u*h) 0 0 u 0 := by
    simpa using scalarSecondJet_affine u 0 0
  have j1 := jq.comp jl
  have jm : ScalarSecondJet (fun h => (1+r)*u*h) 0 0 ((1+r)*u) 0 := by
    simpa using scalarSecondJet_affine ((1+r)*u) 0 0
  have j2 : ScalarSecondJet (fun h => Q (u*h) - (1+r)*u*h) 0 0 (-u)
      ((B/A)*r*(1-r)*u^2) := by
    convert j1.sub jm using 1 <;> dsimp only [Function.comp_def] <;> ring
  have j3 := jq.comp j2
  have jp : ScalarSecondJet (fun h => r*u*h) 0 0 (r*u) 0 := by
    simpa using scalarSecondJet_affine (r*u) 0 0
  have j4 : ScalarSecondJet (fun h => Q (Q (u*h) - (1+r)*u*h) + r*u*h) 0 0 0
      ((B/A)*r*(1-r^2)*u^2) := by
    convert j3.add jp using 1 <;> dsimp only [Function.comp_def] <;> ring
  have j5 := hR.comp j4
  convert j5 using 1 <;> dsimp [threePulseEndpoint, Q, Function.comp_def]
  · ring
  · field_simp [hA]

theorem threePulseLoss_second_jet (Phi R : ℝ → ℝ) (F A B r u : ℝ)
    (hF : 0 < F) (hA : A ≠ 0) (hR : ScalarSecondJet R 0 F A B)
    (hPhi : ScalarSecondJet Phi F 0 (1/A) (-B/A^3)) :
    ScalarSecondJet (fun h => Real.log F - Real.log (threePulseEndpoint Phi R F r u h))
      0 0 0 (-B/F*r*(1-r^2)*u^2) := by
  have hj := (scalarSecondJet_log_loss F hF).comp
    (threePulseEndpoint_second_jet Phi R F A B r u hA hR hPhi)
  convert hj using 1 <;> dsimp only [Function.comp_def] <;> ring

theorem threePulseLoss_genuine_second_jet (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y) (r u : ℝ) :
    ScalarSecondJet (fun h => Real.log F - Real.log (threePulseEndpoint (coordinate F g.impact) R F r u h))
      0 0 0 ((1-F*deriv g.impact F/g.impact F)*(g.impact F/F^2)^2*r*(1-r^2)*u^2) := by
  let A := g.impact F / F
  let B := g.impact F * (F * deriv g.impact F - g.impact F) / F ^ 3
  have hA : A ≠ 0 := div_ne_zero (g.positive F hF).ne' hF.ne'
  have hj := local_response_inverse_jets F g hF hg R hR0 hp
  have hRj : ScalarSecondJet R 0 F A B := ⟨hR0, hR3.of_le (by decide), hj.1, hj.2⟩
  have hPj : ScalarSecondJet (coordinate F g.impact) F 0 (1/A) (-B/A^3) := by
    refine ⟨coordinate_at_benchmark F g.impact,
      (coordinate_contDiffAt_four F g hF hg).of_le (by decide), ?_, ?_⟩
    · convert coordinate_hasDerivAt F g hF hF using 1
      dsimp [A]
      field_simp
    · convert coordinate_second_derivative F g hF hg using 1
      dsimp [A, B]
      field_simp [hF.ne', (g.positive F hF).ne']
      ring
  have hfinal := threePulseLoss_second_jet (coordinate F g.impact) R F A B r u hF hA hRj hPj
  convert hfinal using 1
  dsimp [B]
  field_simp [hF.ne', (g.positive F hF).ne']
  ring

theorem threePulseLoss_contDiffAt (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0) (r u : ℝ) :
    ContDiffAt ℝ 3 (fun h => Real.log F - Real.log
      (threePulseEndpoint (coordinate F g.impact) R F r u h)) 0 := by
  let Q : ℝ → ℝ := fun y => coordinate F g.impact (F+r*(R y-F))
  have hQ0 : Q 0 = 0 := by simp [Q, hR0, coordinate_at_benchmark]
  have hQ : ContDiffAt ℝ 3 Q 0 := by
    have hh : ContDiffAt ℝ 3 (fun y => F + r * (R y - F)) 0 :=
      contDiffAt_const.add (contDiffAt_const.mul (hR3.sub contDiffAt_const))
    have hc := (coordinate_contDiffAt_four F g hF hg).of_le (show (3 : WithTop ℕ∞) ≤ 4 by decide)
    have he : F + r * (R 0 - F) = F := by simp [hR0]
    have hc' : ContDiffAt ℝ 3 (coordinate F g.impact) (F + r * (R 0 - F)) := by
      rw [he]
      exact hc
    exact hc'.comp 0 hh
  have hl : ContDiffAt ℝ 3 (fun h : ℝ => u*h) 0 := by fun_prop
  have h1 : ContDiffAt ℝ 3 (fun h => Q (u*h)) 0 := by
    have hcQ : ContDiffAt ℝ 3 Q (u * 0) := by simpa using hQ
    exact hcQ.comp 0 hl
  have h2 := h1.sub (show ContDiffAt ℝ 3 (fun h : ℝ => (1+r)*u*h) 0 by fun_prop)
  have he2 : Q (u*(0 : ℝ)) - (1+r)*u*0 = 0 := by simp [hQ0]
  have h3 := (he2.symm ▸ hQ).comp 0 h2
  have h4 := h3.add (show ContDiffAt ℝ 3 (fun h : ℝ => r*u*h) 0 by fun_prop)
  have he4 : Q (Q (u*(0 : ℝ)) - (1+r)*u*0) + r*u*0 = 0 := by simp [hQ0]
  have h5 := (he4.symm ▸ hR3).comp 0 h4
  have h5' : ContDiffAt ℝ 3 (threePulseEndpoint (coordinate F g.impact) R F r u) 0 := h5
  apply contDiffAt_const.sub (h5'.log ?_)
  simpa [threePulseEndpoint, hR0, coordinate_at_benchmark] using hF.ne'

theorem threePulseLoss_cubic_bound (F : ℝ) (g : Response) (hF : 0 < F)
    (hg : ContDiffAt ℝ 3 g.impact F) (R : ℝ → ℝ) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y) (r u : ℝ) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε,
      |(Real.log F - Real.log (threePulseEndpoint (coordinate F g.impact) R F r u h)) -
        ((1-F*deriv g.impact F/g.impact F)/2*(g.impact F/F^2)^2*r*(1-r^2)*u^2*h^2)| ≤ C*h^3 := by
  have hj := threePulseLoss_genuine_second_jet F g hF hg R hR0 hR3 hp r u
  obtain ⟨ε,C,hε,hb⟩ := local_cubic_taylor_bound _ (threePulseLoss_contDiffAt F g hF hg R hR0 hR3 r u)
  refine ⟨ε,C,hε,?_⟩
  intro h hh
  have he : ((1-F*deriv g.impact F/g.impact F)*(g.impact F/F^2)^2*r*(1-r^2)*u^2)/2 =
      (1-F*deriv g.impact F/g.impact F)/2*(g.impact F/F^2)^2*r*(1-r^2)*u^2 := by ring
  simpa only [Real.norm_eq_abs, hj.value, hj.first.deriv, hj.second.deriv,
    zero_mul, zero_add, he] using hb h hh

theorem threePulse_scalar_loss_positive {ι : Type*} [Fintype ι]
    (F : ℝ) (g : Response) (hF : 0 < F) (hg : ContDiffAt ℝ 3 g.impact F)
    (R : ℝ → ℝ) (hR0 : R 0 = F) (hR3 : ContDiffAt ℝ 3 R 0)
    (hp : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y)
    (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (he : F * deriv g.impact F / g.impact F < 1)
    (u : ι → ℝ) (hu : ∀ i, u i ≠ 0) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0), ∀ i,
      0 < Real.log F - Real.log (threePulseEndpoint (coordinate F g.impact) R F r (u i) h) := by
  apply Filter.eventually_all.mpr
  intro i
  obtain ⟨ε,C,hε,hb⟩ := threePulseLoss_cubic_bound F g hF hg R hR0 hR3 hp r (u i)
  have hQ : 0 < (1-F*deriv g.impact F/g.impact F)/2*(g.impact F/F^2)^2*r*(1-r^2)*(u i)^2 := by
    have hr2 : 0 < 1-r^2 := by nlinarith
    exact mul_pos (mul_pos (mul_pos (mul_pos
      (div_pos (sub_pos.mpr he) (by norm_num))
      (sq_pos_of_ne_zero (div_ne_zero (g.positive F hF).ne' (pow_ne_zero _ hF.ne')))) hr0) hr2)
      (sq_pos_of_ne_zero (hu i))
  exact eventual_positive_of_cubic_remainder _ _ ε C hQ hε hb

theorem original_three_pulse_from_chart {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F ρ T : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 < ρ) (hT : 0 < T)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F/g.impact F < 1)
    (R : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (hR0 : R 0 = F)
    (hR3 : ContDiffAt ℝ 3 R 0) (hR : ContinuousOn R (Metric.ball 0 (2*ε)))
    (hp : ∀ y ∈ Metric.ball 0 (2*ε), 0 < R y ∧ coordinate F g.impact (R y) = y ∧
      HasDerivAt R (g.impact (R y)/R y) y)
    (hub : ι) (u : ι → ℝ) (hu : ∑ i,u i = 0) (hne : ∀ i,u i ≠ 0) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0),
      ∃ p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => g) completePairedEdges,
        p.terminal.time = T ∧
        (∀ i, p.terminal.prices i = threePulseEndpoint (coordinate F g.impact) R F
          (Real.exp (-ρ*(T/2))) (u i) h) ∧
        (∀ i, p.terminal.prices i < F) ∧
        0 < systemicCrisis (logPriceFromBenchmark F p.terminal.prices) (Fintype.card ι) := by
  classical
  let r := Real.exp (-ρ*(T/2))
  have hr0 : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  let D : (ι → ℝ) → CompleteEdgeIndex ι → ℝ := fun v =>
    embedPairedDollars (starEdges hub) (starDollars v hub)
  have hD (v : ι → ℝ) : ∀ e, 0 ≤ D v e :=
    embedPairedDollars_nonnegative _ _ (starDollars_nonnegative v hub)
  have hinput (v : ι → ℝ) (hv : ∑ i,v i = 0) (i : ι) :
      tradingInput (pairedMatrix completePairedEdges) (D v) i = v i := by
    rw [embedPairedDollars_input]
    exact star_input v hub hv i
  let v₂ : ι → ℝ := fun i => -(1+r)*u i
  let v₃ : ι → ℝ := fun i => r*u i
  have hz₂ : ∑ i,v₂ i = 0 := by simp [v₂, ←Finset.mul_sum, hu]
  have hz₃ : ∑ i,v₃ i = 0 := by simp [v₃, ←Finset.mul_sum, hu]
  have hs := three_vector_original_path completePairedEdges (T/2) T (by linarith) (by linarith)
    (fun _ : ι => F) (fun _ => ρ) (fun _ => g) (fun _ => hF) (fun _ => hρ.le)
    (fun _ => R) (fun _ => ε) (fun _ => hε) (fun _ => hR0) (fun _ => hR) (fun _ => hp)
    (D u) (D v₂) (D v₃) (hD u) (hD v₂) (hD v₃) (fun i => by
      rw [hinput u hu, hinput v₂ hz₂, hinput v₃ hz₃]
      dsimp [v₂, v₃]
      ring)
  have hpae : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0:ℝ) ∈ Metric.ball 0 (2*ε) by simpa using (show 0 < 2*ε by linarith))] with y hy
    exact (hp y hy).2.2
  have hl := threePulse_scalar_loss_positive F g hF hg R hR0 hR3 hpae r hr0 hr1 he u hne
  filter_upwards [hs, hl] with h hs hl
  obtain ⟨p, ht, hend⟩ := hs
  have heq : ∀ i, p.terminal.prices i = threePulseEndpoint (coordinate F g.impact) R F r (u i) h := by
    intro i
    rw [hend i]
    unfold threeVectorFinalCoordinate vectorRecoveryCoordinate recoveryPrices
    simp_rw [hinput u hu, hinput v₂ hz₂, hinput v₃ hz₃]
    dsimp [threeVectorFinalCoordinate, vectorRecoveryCoordinate, recoveryPrices, threePulseEndpoint, v₂, v₃]
    have htime : T - T/2 = T/2 := by ring
    rw [htime]
    have hfirst : h * u i = u i * h := mul_comm _ _
    have hsecond : h * (-(1+r)*u i) = -((1+r)*u i*h) := by ring
    have hthird : h * (r*u i) = r*u i*h := by ring
    simp only [sub_zero, hfirst, hsecond, hthird, ←sub_eq_add_neg]
    simp only [← (show r = Real.exp (-ρ*(T/2)) from rfl), mul_comm _ r]
  have hpos : ∀ i, 0 < p.terminal.prices i :=
    p.trace.endpoint_positive (fun i => by rw [p.initial_prices i]; exact hF)
  have hlp : ∀ i, 0 < Real.log F - Real.log (p.terminal.prices i) := by
    intro i
    rw [heq i]
    exact hl i
  have hbelow : ∀ i, p.terminal.prices i < F := by
    intro i
    exact (Real.log_lt_log_iff (hpos i) hF).mp (sub_pos.mp (hlp i))
  refine ⟨p, ht, heq, hbelow, ?_⟩
  have hlog : ∀ i, -logPriceFromBenchmark F p.terminal.prices i =
      Real.log F - Real.log (p.terminal.prices i) := by
    intro i
    dsimp [logPriceFromBenchmark]
    rw [Real.log_div (hpos i).ne' hF.ne']
    ring
  apply crisis_pos_of_mean_pos_and_positive_count _ _ Fintype.card_pos le_rfl
  · unfold meanLogLoss
    rw [← Finset.sum_neg_distrib]
    apply div_pos _ (by exact_mod_cast Fintype.card_pos)
    apply Finset.sum_pos
    · intro i _
      rw [hlog]
      exact hlp i
    · exact Finset.univ_nonempty
  · have hf : Finset.univ.filter (fun i => 0 < -logPriceFromBenchmark F p.terminal.prices i) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      rw [hlog]
      exact hlp i
    rw [hf, Finset.card_univ]

/-- Original Proposition 4.2: actual finite ordered pulses, exact dollar
closure, finite nonnegative inventories, and the stated cubic expansion. -/
theorem proposition_4_2_original {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F ρ T : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 < ρ) (hT : 0 < T)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F/g.impact F < 1)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ (u : ι → ℝ) (R : ℝ → ℝ), (∑ i,u i = 0) ∧ (∀ i,u i ≠ 0) ∧
      (∀ i, ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε,
        |(Real.log F - Real.log (threePulseEndpoint (coordinate F g.impact) R F
          (Real.exp (-ρ*(T/2))) (u i) h)) -
          ((1-F*deriv g.impact F/g.impact F)/2*(g.impact F/F^2)^2*
            (Real.exp (-ρ*(T/2)))*(1-(Real.exp (-ρ*(T/2)))^2)*(u i)^2*h^2)| ≤ C*h^3) ∧
      (∀ᶠ h in nhdsWithin 0 (Ioi 0),
        ∃ p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => ρ) (fun _ => g) completePairedEdges,
          p.terminal.time = T ∧
          (∀ i, p.terminal.prices i = threePulseEndpoint (coordinate F g.impact) R F
            (Real.exp (-ρ*(T/2))) (u i) h) ∧
          (∀ i, p.terminal.prices i < F) ∧
          0 < systemicCrisis (logPriceFromBenchmark F p.terminal.prices) (Fintype.card ι)) := by
  classical
  let hub : ι := Classical.arbitrary ι
  let u : ι → ℝ := partialCoveragePulseVector hub
  have hu : ∑ i,u i = 0 := partialCoveragePulseVector_zero_sum hub
  have hne : ∀ i,u i ≠ 0 := by
    intro i
    by_cases hi : i = hub
    · subst i
      exact (partialCoveragePulseVector_hub_negative hub hN).ne
    · simp [u, partialCoveragePulseVector, hi]
  obtain ⟨R, δ, hδ, hR0, hRδ, hpδ⟩ := exists_local_response_chart F g hF hg
  let ε := δ / 2
  have hε : 0 < ε := half_pos hδ
  have heps : 2*ε = δ := by dsimp [ε]; ring
  have hR : ContinuousOn R (Metric.ball 0 (2*ε)) := by
    rw [heps]
    exact hRδ.continuousOn
  have hR3 : ContDiffAt ℝ 3 R 0 := hRδ.contDiffAt
    (Metric.isOpen_ball.mem_nhds (by simpa using hδ))
  have hp : ∀ y ∈ Metric.ball 0 (2*ε), 0 < R y ∧ coordinate F g.impact (R y) = y ∧
      HasDerivAt R (g.impact (R y)/R y) y := by rwa [heps]
  have hpae : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show (0:ℝ) ∈ Metric.ball 0 δ by simpa using hδ)] with y hy
    exact (hpδ y hy).2.2
  refine ⟨u, R, hu, hne, ?_, ?_⟩
  · intro i
    exact threePulseLoss_cubic_bound F g hF hg R hR0 hR3 hpae (Real.exp (-ρ*(T/2))) (u i)
  · exact original_three_pulse_from_chart F ρ T g hF hρ hT hg he R ε hε hR0 hR3 hR hp hub u hu hne

end MarketCrash
