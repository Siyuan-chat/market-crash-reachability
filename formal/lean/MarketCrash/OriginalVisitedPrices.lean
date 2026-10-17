import MarketCrash.OriginalPhysicalTrace
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
namespace MarketCrash
open Set
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
variable {F rho : ι → ℝ} {response : ι → Response} {edges : κ → PairedEdge ι}
variable {s mid t : PhysicalMarketState ι}

def OriginalPhysicalStep.Visited
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) (x : ℝ) : Prop :=
  match step with
  | .continuous m _ _ _ _ => ∃ a ∈ Icc m.a m.b, m.prices a i = x
  | .pulse p _ _ _ => ∃ a ∈ Icc (0 : ℝ) 1, p.prices a i = x

def OriginalPhysicalReachable.Visited {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → ι → ℝ → Prop
  | _, .refl _, i, x => s.prices i = x
  | _, .append previous step, i, x => previous.Visited i x ∨ step.Visited i x

/-- Observations include all economic fields at continuous physical times
and at every intermediate flow-completed pulse parameter. -/
def OriginalPhysicalStep.Observes
    (step : OriginalPhysicalStep F rho response edges s t) (o : PhysicalMarketState ι) : Prop :=
  match step with
  | .continuous m _ _ _ _ => ∃ a ∈ Icc m.a m.b,
      o = ⟨a, m.prices a, m.shares a, m.dollarLedger a⟩
  | .pulse p _ _ _ => ∃ a ∈ Icc (0 : ℝ) 1,
      o = ⟨p.physicalTime, p.prices a, p.shares a, p.dollarLedger a⟩

def OriginalPhysicalReachable.Observes {s : PhysicalMarketState ι} :
    {t : PhysicalMarketState ι} → OriginalPhysicalReachable F rho response edges s t → PhysicalMarketState ι → Prop
  | _, .refl _, o => o = s
  | _, .append previous step, o => previous.Observes o ∨ step.Observes o

theorem continuous_price_radial_attained (f : ℝ → ℝ) (a b : ℝ)
    (hc : ContinuousOn f (Icc a b)) (t : ℝ) (ht : t ∈ Icc a b)
    (x : ℝ) (hx : x ∈ uIcc (f a) (f t)) : ∃ u ∈ Icc a t, f u = x := by
  have hcont : ContinuousOn f (uIcc a t) := by
    rw [uIcc_of_le ht.1]
    exact hc.mono (fun u hu => ⟨hu.1, hu.2.trans ht.2⟩)
  obtain ⟨u, hu, heq⟩ := intermediate_value_uIcc hcont hx
  exact ⟨u, by simpa [uIcc_of_le ht.1] using hu, heq⟩

theorem OriginalPhysicalStep.visited_start
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : step.Visited i (s.prices i) := by
  cases step with
  | continuous m _ _ _ _ => exact ⟨m.a, ⟨le_rfl, m.time_order⟩, rfl⟩
  | pulse p _ _ _ => exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩

theorem OriginalPhysicalStep.visited_terminal
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) : step.Visited i (t.prices i) := by
  cases step with
  | continuous m _ _ _ _ => exact ⟨m.b, ⟨m.time_order, le_rfl⟩, rfl⟩
  | pulse p _ _ _ => exact ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩

theorem OriginalPhysicalStep.radial_to_visited
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) (x z : ℝ)
    (hx : step.Visited i x) (hz : z ∈ uIcc (s.prices i) x) : step.Visited i z := by
  cases step with
  | continuous m _ _ _ _ =>
    obtain ⟨a, ha, heq⟩ := hx
    obtain ⟨u, hu, hval⟩ := continuous_price_radial_attained (fun a => m.prices a i)
      m.a m.b (m.continuous_prices i) a ha z (by simpa [heq] using hz)
    exact ⟨u, ⟨hu.1, hu.2.trans ha.2⟩, hval⟩
  | pulse p _ _ _ =>
    obtain ⟨a, ha, heq⟩ := hx
    obtain ⟨u, hu, hval⟩ := continuous_price_radial_attained (fun a => p.prices a i)
      0 1 (p.continuous_prices i) a ha z (by simpa [heq] using hz)
    exact ⟨u, ⟨hu.1, hu.2.trans ha.2⟩, hval⟩

theorem OriginalPhysicalReachable.visited_terminal
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) :
    trace.Visited i (t.prices i) := by
  cases trace with
  | refl => rfl
  | append previous step => exact Or.inr (step.visited_terminal i)

/-- Every benchmark-to-visited radial price was actually executed on
this same finite trace, including the interior of its physical pulses. -/
theorem OriginalPhysicalReachable.radial_to_visited
    (trace : OriginalPhysicalReachable F rho response edges s t) (i : ι) (x z : ℝ)
    (hx : trace.Visited i x) (hz : z ∈ uIcc (s.prices i) x) : trace.Visited i z := by
  induction trace generalizing x z with
  | refl =>
    change s.prices i = x at hx
    rw [← hx] at hz
    have he : z = s.prices i := by simpa using hz
    exact he.symm
  | @append mid t previous step ih =>
    rcases hx with hx | hx
    · exact Or.inl (ih x z hx hz)
    · rcases (uIcc_subset_uIcc_union_uIcc (a := s.prices i) (b := mid.prices i) (c := x)) hz with hprev | hstep
      · exact Or.inl (ih (mid.prices i) z (previous.visited_terminal i) hprev)
      · exact Or.inr (step.radial_to_visited i x z hx hstep)

theorem OriginalPhysicalStep.observed_prices_visited
    (step : OriginalPhysicalStep F rho response edges s t) (o : PhysicalMarketState ι)
    (ho : step.Observes o) (i : ι) : step.Visited i (o.prices i) := by
  cases step with
  | continuous m _ _ _ _ =>
    obtain ⟨a, ha, rfl⟩ := ho
    exact ⟨a, ha, rfl⟩
  | pulse p _ _ _ =>
    obtain ⟨a, ha, rfl⟩ := ho
    exact ⟨a, ha, rfl⟩

theorem OriginalPhysicalReachable.observed_prices_visited
    (trace : OriginalPhysicalReachable F rho response edges s t) (o : PhysicalMarketState ι)
    (ho : trace.Observes o) (i : ι) : trace.Visited i (o.prices i) := by
  induction trace with
  | refl => change o = s at ho; subst o; rfl
  | append previous step ih =>
    rcases ho with ho | ho
    · exact Or.inl (ih ho)
    · exact Or.inr (step.observed_prices_visited o ho i)

theorem OriginalPhysicalReachable.radial_at_observation
    (trace : OriginalPhysicalReachable F rho response edges s t) (o : PhysicalMarketState ι)
    (ho : trace.Observes o) (i : ι) (x : ℝ) (hx : x ∈ uIcc (s.prices i) (o.prices i)) :
    trace.Visited i x :=
  trace.radial_to_visited i _ x (trace.observed_prices_visited o ho i) hx

theorem OriginalPhysicalStep.observes_initial
    (step : OriginalPhysicalStep F rho response edges s t) : step.Observes s := by
  cases step with
  | continuous m _ _ _ _ => exact ⟨m.a, ⟨le_rfl, m.time_order⟩, rfl⟩
  | pulse p _ _ _ => exact ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩

theorem OriginalPhysicalStep.observes_terminal
    (step : OriginalPhysicalStep F rho response edges s t) : step.Observes t := by
  cases step with
  | continuous m _ _ _ _ => exact ⟨m.b, ⟨m.time_order, le_rfl⟩, rfl⟩
  | pulse p _ _ _ => exact ⟨1, ⟨by norm_num, le_rfl⟩, rfl⟩

theorem OriginalPhysicalReachable.observes_initial
    (trace : OriginalPhysicalReachable F rho response edges s t) : trace.Observes s := by
  induction trace with
  | refl => rfl
  | append previous step ih => exact Or.inl ih

theorem OriginalPhysicalReachable.observes_terminal
    (trace : OriginalPhysicalReachable F rho response edges s t) : trace.Observes t := by
  cases trace with
  | refl => rfl
  | append previous step => exact Or.inr step.observes_terminal

/-- Every earlier prefix observation remains an observation of its extension. -/
theorem OriginalPhysicalReachable.observes_append_previous
    (previous : OriginalPhysicalReachable F rho response edges s mid)
    (step : OriginalPhysicalStep F rho response edges mid t) (o : PhysicalMarketState ι)
    (ho : previous.Observes o) : (previous.append step).Observes o := Or.inl ho

/-- This includes each point of the final continuous piece and every
internal pulse-completion parameter, not only its endpoint. -/
theorem OriginalPhysicalReachable.observes_append_step
    (previous : OriginalPhysicalReachable F rho response edges s mid)
    (step : OriginalPhysicalStep F rho response edges mid t) (o : PhysicalMarketState ι)
    (ho : step.Observes o) : (previous.append step).Observes o := Or.inr ho

theorem OriginalPhysicalStep.observed_time_between
    (step : OriginalPhysicalStep F rho response edges s t) (o : PhysicalMarketState ι)
    (ho : step.Observes o) : o.time ∈ Icc s.time t.time := by
  cases step with
  | continuous m _ _ _ _ =>
    obtain ⟨a, ha, rfl⟩ := ho
    exact ha
  | pulse p _ _ _ =>
    obtain ⟨a, ha, rfl⟩ := ho
    exact ⟨le_rfl, le_rfl⟩

theorem OriginalPhysicalReachable.observed_time_between
    (trace : OriginalPhysicalReachable F rho response edges s t) (o : PhysicalMarketState ι)
    (ho : trace.Observes o) : o.time ∈ Icc s.time t.time := by
  induction trace with
  | refl => change o = s at ho; subst o; exact ⟨le_rfl, le_rfl⟩
  | append previous step ih =>
    rcases ho with ho | ho
    · have hh := ih ho
      exact ⟨hh.1, hh.2.trans step.chronological⟩
    · have hh := step.observed_time_between o ho
      exact ⟨previous.chronological.trans hh.1, hh.2⟩

/-- A hypothesis only on actual trace visits supplies the needed radial
property; no condition on unrelated positive prices is introduced. -/
theorem OriginalPhysicalReachable.property_on_radial_at_observation
    (trace : OriginalPhysicalReachable F rho response edges s t)
    (P : ι → ℝ → Prop) (hP : ∀ i x, trace.Visited i x → P i x)
    (hinit : ∀ i, s.prices i = F i) (o : PhysicalMarketState ι)
    (ho : trace.Observes o) (i : ι) (x : ℝ)
    (hx : x ∈ uIcc (F i) (o.prices i)) : P i x := by
  apply hP i x
  apply trace.radial_at_observation o ho i x
  simpa [hinit i] using hx

theorem OriginalPhysicalStep.observes_at_time
    (step : OriginalPhysicalStep F rho response edges s t) (tau : ℝ)
    (htau : tau ∈ Icc s.time t.time) :
    ∃ o : PhysicalMarketState ι, step.Observes o ∧ o.time = tau := by
  cases step with
  | continuous m _ _ _ _ =>
    exact ⟨⟨tau, m.prices tau, m.shares tau, m.dollarLedger tau⟩, ⟨tau, htau, rfl⟩, rfl⟩
  | pulse p _ _ _ =>
    have he : tau = p.physicalTime := le_antisymm htau.2 htau.1
    exact ⟨⟨p.physicalTime, p.prices 0, p.shares 0, p.dollarLedger 0⟩,
      ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩, he.symm⟩

theorem OriginalPhysicalReachable.observes_at_time
    (trace : OriginalPhysicalReachable F rho response edges s t) (tau : ℝ)
    (htau : tau ∈ Icc s.time t.time) :
    ∃ o : PhysicalMarketState ι, trace.Observes o ∧ o.time = tau := by
  induction trace with
  | refl => exact ⟨s, rfl, (le_antisymm htau.2 htau.1).symm⟩
  | @append mid t previous step ih =>
    by_cases hm : tau ≤ mid.time
    · obtain ⟨o, ho, he⟩ := ih ⟨htau.1, hm⟩
      exact ⟨o, Or.inl ho, he⟩
    · obtain ⟨o, ho, he⟩ := step.observes_at_time tau ⟨(lt_of_not_ge hm).le, htau.2⟩
      exact ⟨o, Or.inr ho, he⟩

theorem OriginalPhysicalStep.visited_positive
    (step : OriginalPhysicalStep F rho response edges s t) (i : ι) (x : ℝ)
    (hx : step.Visited i x) : 0 < x := by
  cases step with
  | continuous m _ _ _ _ =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact m.positive_prices a ha i
  | pulse p _ _ _ =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact p.positive_prices a ha i

theorem OriginalPhysicalReachable.visited_positive
    (trace : OriginalPhysicalReachable F rho response edges s t)
    (hp : ∀ i, 0 < s.prices i) (i : ι) (x : ℝ) (hx : trace.Visited i x) : 0 < x := by
  induction trace with
  | refl => change s.prices i = x at hx; rw [← hx]; exact hp i
  | append previous step ih =>
    rcases hx with hx | hx
    · exact ih hx
    · exact step.visited_positive i x hx

end MarketCrash
