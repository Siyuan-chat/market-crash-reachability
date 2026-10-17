import MarketCrash.OriginalThreePulse

noncomputable section
namespace MarketCrash
open Set Filter
open scoped Topology

theorem finite_cubic_remainders_uniform {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (Q : ι → ℝ)
    (hb : ∀ i, ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε, |f i h-Q i*h^2| ≤ C*h^3) :
    ∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε, ∀ i, |f i h-Q i*h^2| ≤ C*h^3 := by
  classical
  choose ε C hε hb using hb
  let δ := Finset.univ.inf' Finset.univ_nonempty ε
  let B := Finset.univ.sup' Finset.univ_nonempty C
  have hδ : 0 < δ := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hε i)
  refine ⟨δ,B,hδ,?_⟩
  intro h hh i
  have hδi : δ ≤ ε i := Finset.inf'_le ε (Finset.mem_univ i)
  have hBi : C i ≤ B := Finset.le_sup' _ (Finset.mem_univ i)
  exact (hb i h ⟨hh.1,hh.2.trans hδi⟩).trans (mul_le_mul_of_nonneg_right hBi (pow_nonneg hh.1 _))

/-- Full Proposition 4.2 with one neighborhood and one cubic bound for all assets. -/
theorem proposition_4_2_original_uniform {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (F rho T : ℝ) (g : Response) (hF : 0 < F) (hρ : 0 < rho) (hT : 0 < T)
    (hg : ContDiffAt ℝ 3 g.impact F) (he : F*deriv g.impact F/g.impact F < 1)
    (hN : 2 ≤ Fintype.card ι) :
    ∃ (u : ι → ℝ) (R : ℝ → ℝ), (∑ i,u i = 0) ∧ (∀ i,u i ≠ 0) ∧
      (∃ ε C : ℝ, 0 < ε ∧ ∀ h ∈ Icc 0 ε, ∀ i,
        |(Real.log F-Real.log (threePulseEndpoint (coordinate F g.impact) R F
          (Real.exp (-rho*(T/2))) (u i) h)) -
          ((1-F*deriv g.impact F/g.impact F)/2*(g.impact F/F^2)^2*
            Real.exp (-rho*(T/2))*(1-(Real.exp (-rho*(T/2)))^2)*(u i)^2*h^2)| ≤ C*h^3) ∧
      (∀ᶠ h in nhdsWithin 0 (Ioi 0),
        ∃ p : OriginalAdmissiblePhysicalPath (fun _ : ι => F) (fun _ => rho) (fun _ => g) completePairedEdges,
          p.terminal.time = T ∧
          (∀ i, p.terminal.prices i = threePulseEndpoint (coordinate F g.impact) R F
            (Real.exp (-rho*(T/2))) (u i) h) ∧
          (∀ i, p.terminal.prices i < F) ∧
          0 < systemicCrisis (logPriceFromBenchmark F p.terminal.prices) (Fintype.card ι)) := by
  obtain ⟨u,R,hu,hne,hb,hpath⟩ := proposition_4_2_original F rho T g hF hρ hT hg he hN
  refine ⟨u,R,hu,hne,?_,hpath⟩
  exact finite_cubic_remainders_uniform _ _ hb

end MarketCrash
