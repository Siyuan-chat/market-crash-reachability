import MarketCrash.TwoPulseScalar
import MarketCrash.OriginalThreePulse
import MarketCrash.PairedControlConstruction
import MarketCrash.CompletePairedEmbedding

noncomputable section
namespace MarketCrash
open Set Filter
open scoped Topology

theorem two_pulse_original_path {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hub : ι) (F rho T : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 ≤ rho) (hT : 0 ≤ T)
    (R : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε) (hR0 : R 0 = F)
    (hR : ContinuousOn R (Metric.ball 0 (2*ε)))
    (hp : ∀ y ∈ Metric.ball 0 (2*ε), 0 < R y ∧ coordinate F g.impact (R y) = y ∧
      HasDerivAt R (g.impact (R y)/R y) y)
    (u : ι → ℝ) (hu : ∑ i,u i = 0) :
    ∀ᶠ h in nhdsWithin 0 (Ioi 0),
      ∃ p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) completePairedEdges,
        p.terminal.time = T ∧ ∀ i, p.terminal.prices i =
          twoPulseEndpoint (coordinate F g.impact) R F (Real.exp (-rho*T)) (u i) h := by
  classical
  let d₁ := embedPairedDollars (starEdges hub) (starDollars u hub)
  let d₂ := embedPairedDollars (starEdges hub) (starDollars (fun i => -u i) hub)
  have hneg : (∑ i,-u i) = 0 := by rw [Finset.sum_neg_distrib,hu,neg_zero]
  have hv₁ : tradingInput (pairedMatrix completePairedEdges) d₁ = u := by
    funext i
    exact (embedPairedDollars_input _ _ _).trans (star_input u hub hu i)
  have hv₂ : tradingInput (pairedMatrix completePairedEdges) d₂ = fun i => -u i := by
    funext i
    exact (embedPairedDollars_input _ _ _).trans (star_input (fun i => -u i) hub hneg i)
  have hclosed : ∀ i, tradingInput (pairedMatrix completePairedEdges) d₁ i +
      tradingInput (pairedMatrix completePairedEdges) d₂ i +
        tradingInput (pairedMatrix completePairedEdges) (fun _ => 0) i = 0 := by
    intro i
    rw [hv₁,hv₂]
    simp [tradingInput]
  have hpath := three_vector_original_path completePairedEdges T T hT le_rfl
    (fun _ : ι => F) (fun _ => rho) (fun _ => g) (fun _ => hF) (fun _ => hρ)
    (fun _ => R) (fun _ => ε) (fun _ => hε) (fun _ => hR0) (fun _ => hR) (fun _ => hp)
    d₁ d₂ (fun _ => 0)
    (embedPairedDollars_nonnegative _ _ (starDollars_nonnegative u hub))
    (embedPairedDollars_nonnegative _ _ (starDollars_nonnegative (fun i => -u i) hub))
    (fun _ => le_rfl) hclosed
  have hRc : ContinuousAt R 0 := hR.continuousAt
    (Metric.isOpen_ball.mem_nhds (by simpa using (show 0 < 2*ε by linarith)))
  let y := fun h => vectorRecoveryCoordinate (fun _ : ι => F) (fun _ => rho)
    (fun _ => g) (fun _ => R) 0 T (fun i => h*u i)
  let x := fun h i => y h i-h*u i
  have hy := vectorRecoveryCoordinate_tendsto_zero (fun _ : ι => F) (fun _ => rho)
    (fun _ => g) (fun _ => hF) (fun _ => R) (fun _ => hR0) (fun _ => hRc) 0 T
    (fun h i => h*u i) (fun i => by simpa using (tendsto_id.mul_const (u i) : Tendsto (fun h : ℝ => h*u i) (nhds 0) (nhds (0*u i))))
  have hinside : ∀ᶠ h in nhds 0, ∀ i, x h i ∈ Metric.ball 0 (2*ε) := by
    apply Filter.eventually_all.mpr
    intro i
    have hx : Tendsto (fun h => x h i) (nhds 0) (nhds 0) := by
      simpa [x,y] using (hy i).sub (tendsto_id.mul_const (u i))
    exact hx.eventually (Metric.ball_mem_nhds 0 (by linarith))
  filter_upwards [hpath,hinside.filter_mono nhdsWithin_le_nhds] with h hh hin
  obtain ⟨p,ht,hpterminal⟩ := hh
  refine ⟨p,ht,?_⟩
  intro i
  rw [hpterminal]
  have hchart := (hp (x h i) (hin i)).2.1
  have hv₀ : tradingInput (pairedMatrix completePairedEdges) (fun _ : CompleteEdgeIndex ι => 0) =
      fun _ => (0 : ℝ) := by funext j; simp [tradingInput]
  simp only [threeVectorFinalCoordinate]
  rw [hv₁,hv₂,hv₀]
  simpa [vectorRecoveryCoordinate,recoveryPrices,twoPulseEndpoint,x,y,mul_comm] using congrArg R hchart

/-- Proposition 4.3, for every selected zero-sum direction with at least
k positive components. Actual ordered single-edge pulses at 0 and T,
original marginal settlement and recovery, finite inventory, no shorts,
and every asset's terminal dollars zero are part of the resulting path.
The original mean-loss coefficient has a uniform cubic remainder. -/
theorem proposition_4_3_original {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F rho T : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 < rho) (hT : 0 < T)
    (_hN : 2 ≤ Fintype.card ι) (hg : ContDiffAt ℝ 3 g.impact F)
    (alpha : ℝ) (hα : 0 < alpha) (_hα1 : alpha ≤ 1)
    (hkn : requiredAssetCount (ι := ι) alpha < Fintype.card ι)
    (_he0 : F*deriv g.impact F/g.impact F < 2)
    (he : Real.exp (-rho*T) < 2-F*deriv g.impact F/g.impact F)
    (u : ι → ℝ) (hu : ∑ i,u i = 0)
    (hcount : requiredAssetCount (ι := ι) alpha ≤ (Finset.univ.filter (fun i => 0 < u i)).card) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ h : ℝ, 0 < h → h < ε →
      ∃ p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) completePairedEdges,
        p.terminal.time = T ∧
        0 < systemicCrisis (logPriceFromBenchmark F p.terminal.prices) (requiredAssetCount (ι := ι) alpha) ∧
        |meanLogLoss (logPriceFromBenchmark F p.terminal.prices) -
          ((g.impact F/F^2)^2/(2*(Fintype.card ι : ℝ))*(1-Real.exp (-rho*T))*
            (2-F*deriv g.impact F/g.impact F-Real.exp (-rho*T))*(∑ i,(u i)^2)*h^2)| ≤ C*h^3 := by
  classical
  obtain ⟨R,δ,hδ,hR0,hcd,hchart⟩ := exists_local_response_chart F g hF hg
  have hzero : (0 : ℝ) ∈ Metric.ball 0 δ := by simpa using hδ
  have hR3 := hcd.contDiffAt (Metric.isOpen_ball.mem_nhds hzero)
  have hder : ∀ᶠ y in nhds 0, HasDerivAt R (g.impact (R y)/R y) y := by
    filter_upwards [Metric.ball_mem_nhds 0 hδ] with y hy
    exact (hchart y hy).2.2
  have heδ : 2*(δ/2) = δ := by ring
  have hRcont : ContinuousOn R (Metric.ball 0 (2*(δ/2))) := by
    rw [heδ]
    exact hcd.continuousOn
  have hpchart : ∀ y ∈ Metric.ball 0 (2*(δ/2)), 0 < R y ∧ coordinate F g.impact (R y) = y ∧
      HasDerivAt R (g.impact (R y)/R y) y := by simpa only [heδ] using hchart
  let hub : ι := Classical.choice (inferInstance : Nonempty ι)
  have hpath := two_pulse_original_path hub F rho T g hF hρ.le hT.le
    R (δ/2) (half_pos hδ) hR0 hRcont hpchart u hu
  have hr : Real.exp (-rho*T) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hρ hT])
  have hpositive := twoPulse_scalar_crisis_positive_of_direction F g hF hg R hR0 hR3 hder
    (Real.exp (-rho*T)) hr he u hu (requiredAssetCount (ι := ι) alpha)
    (requiredAssetCount_pos (ι := ι) alpha hα) hkn hcount
  obtain ⟨ε₀,C,hε₀,hbound⟩ := twoPulseMean_cubic_bound F g hF hg R hR0 hR3 hder
    (Real.exp (-rho*T)) u hu
  have hsmall : Iio ε₀ ∈ nhdsWithin 0 (Ioi 0) := nhdsWithin_le_nhds (Iio_mem_nhds hε₀)
  have hall : ∀ᶠ h in nhdsWithin 0 (Ioi 0),
      ∃ p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) completePairedEdges,
        p.terminal.time = T ∧
        0 < systemicCrisis (logPriceFromBenchmark F p.terminal.prices) (requiredAssetCount (ι := ι) alpha) ∧
        |meanLogLoss (logPriceFromBenchmark F p.terminal.prices) -
          ((g.impact F/F^2)^2/(2*(Fintype.card ι : ℝ))*(1-Real.exp (-rho*T))*
            (2-F*deriv g.impact F/g.impact F-Real.exp (-rho*T))*(∑ i,(u i)^2)*h^2)| ≤ C*h^3 := by
    filter_upwards [hpath,hpositive,hsmall,self_mem_nhdsWithin] with h hh hp hs ht
    obtain ⟨p,hptime,hprices⟩ := hh
    have hpeq := funext hprices
    have hpprices : ∀ i, 0 < p.terminal.prices i := fun i => by rw [hprices i]; exact hp.1 i
    have hlog : ∀ i, actualLogLoss F p.terminal.prices i =
        Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F (Real.exp (-rho*T)) (u i) h) := by
      intro i
      rw [actualLogLoss,Real.log_div hF.ne' (hpprices i).ne',hprices i]
    have hm : meanLogLoss (logPriceFromBenchmark F p.terminal.prices) =
        (1/(Fintype.card ι : ℝ))*∑ i,
          (Real.log F-Real.log (twoPulseEndpoint (coordinate F g.impact) R F (Real.exp (-rho*T)) (u i) h)) := by
      rw [meanLogLoss_eq_actual F p.terminal.prices hF hpprices]
      simp_rw [hlog]
      ring
    refine ⟨p,hptime,?_,?_⟩
    · rw [hpeq]
      exact hp.2
    · rw [hm]
      exact hbound h ⟨le_of_lt ht,le_of_lt hs⟩
  obtain ⟨ε,hε,hεprop⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hall)
  refine ⟨ε,C,hε,?_⟩
  intro h hh hhe
  apply hεprop
  · simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hh] using hhe
  · exact hh

end MarketCrash
