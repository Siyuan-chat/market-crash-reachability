import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Core definitions from V12 Final, equations (1.1), (2.6), (3.1).
The price domain is strictly positive. No notion of admissible controlled path
or global reachability is silently supplied by these definitions. -/
noncomputable section
open Set MeasureTheory
namespace MarketCrash

def positivePrices : Set ℝ := Ioi 0

structure Response where
  impact : ℝ → ℝ
  continuousOn_positive : ContinuousOn impact positivePrices
  positive : ∀ S ∈ positivePrices, 0 < impact S

def coordinate (F : ℝ) (g : ℝ → ℝ) (S : ℝ) : ℝ :=
  ∫ u in F..S, u / g u

def coordinateImage (F : ℝ) (g : ℝ → ℝ) : Set ℝ :=
  coordinate F g '' positivePrices

def potential {ι : Type*} [Fintype ι] (y : ι → ℝ) : ℝ := ∑ i, y i

structure PairedEdge (ι : Type*) where
  seller : ι
  buyer : ι
  distinct : seller ≠ buyer

def pairedMatrix {ι κ : Type*} [DecidableEq ι] (edges : κ → PairedEdge ι)
    (i : ι) (e : κ) : ℝ :=
  (if i = (edges e).buyer then 1 else 0) -
  (if i = (edges e).seller then 1 else 0)

def tradingInput {ι κ : Type*} [Fintype κ] (B : ι → κ → ℝ)
    (rates : κ → ℝ) (i : ι) : ℝ := ∑ e, B i e * rates e

end MarketCrash
