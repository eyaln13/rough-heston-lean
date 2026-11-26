import FractionalPulseBias

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

/-- The terminal size-bias parameter does not change the trimmed past
law at any earlier observation. -/
theorem fractional_pulse_bias_trim_eq
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H s r : ℝ≥0}
    (hα : 0<α) (hα' : α<1) (hκ : 0≤κ) (hε : 0<ε) (hd : 0<d)
    (hsr : s≤r) (hr : r≤H) (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C) :
    (@sizeBiasedLaw Ω m μ (fractionalPulseMass ε M r) ε).trim (𝒢.le s) =
      (@sizeBiasedLaw Ω m μ (fractionalPulseMass ε M s) ε).trim (𝒢.le s) := by
  let _ : MeasurableSpace Ω := m
  let Z := fractionalPulseMass ε M
  let Q (t : ℝ≥0) := sizeBiasedLaw μ (Z t) ε
  have hQ (t : ℝ≥0) (ht : t≤H) : IsProbabilityMeasure (Q t) := by
    obtain ⟨_,hn,hi,hE,_⟩ := fractional_pulse_mass_data hα hα' hκ hε hd ht hP
    exact sizeBiasedLaw_isProbabilityMeasure hε hi hn hE
  let : IsProbabilityMeasure (Q r) := hQ r hr
  let : IsProbabilityMeasure (Q s) := hQ s (hsr.trans hr)
  refine @Measure.ext Ω (𝒢 s) _ _ (fun A hA => ?_)
  rw [trim_measurableSet_eq (𝒢.le s) hA,trim_measurableSet_eq (𝒢.le s) hA]
  refine (measureReal_eq_measureReal_iff (measure_ne_top (Q r) A) (measure_ne_top (Q s) A)).mp ?_
  exact fractional_pulse_bias_agrees_on_past hα hα' hκ hε hd hsr hr hP hA

/-- A supremum measurable at the end of a block can be estimated
under its own terminal bias and used under any later bias. -/
theorem fractional_pulse_bias_past_integral
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H s r : ℝ≥0} {F : Ω → ℝ}
    (hα : 0<α) (hα' : α<1) (hκ : 0≤κ) (hε : 0<ε) (hd : 0<d)
    (hsr : s≤r) (hr : r≤H) (hP : FractionalPulseProcess μ 𝒢 H α κ a ε d M U C)
    (hF : StronglyMeasurable[𝒢 s] F) :
    let Q (t : ℝ≥0) := @sizeBiasedLaw Ω m μ (fractionalPulseMass ε M t) ε
    (Integrable F (Q r) ↔ Integrable F (Q s)) ∧
      (∫ ω,F ω ∂Q r)=(∫ ω,F ω ∂Q s) := by
  let _ : MeasurableSpace Ω := m
  let Q (t : ℝ≥0) := sizeBiasedLaw μ (fractionalPulseMass ε M t) ε
  have he : (Q r).trim (𝒢.le s) = (Q s).trim (𝒢.le s) := fractional_pulse_bias_trim_eq hα hα' hκ hε hd hsr hr hP
  change (Integrable F (Q r) ↔ Integrable F (Q s)) ∧
    (∫ ω,F ω ∂Q r)=(∫ ω,F ω ∂Q s)
  constructor
  · refine ⟨fun hi => ?_,fun hi => ?_⟩
    · have ht := hi.trim (𝒢.le s) hF
      rw [he] at ht
      exact integrable_of_integrable_trim (𝒢.le s) ht
    · have ht := hi.trim (𝒢.le s) hF
      rw [← he] at ht
      exact integrable_of_integrable_trim (𝒢.le s) ht
  · calc
      _ = ∫ ω,F ω ∂(Q r).trim (𝒢.le s) := integral_trim (μ := Q r) (𝒢.le s) hF
      _ = ∫ ω,F ω ∂(Q s).trim (𝒢.le s) := by rw [he]
      _ = _ := (integral_trim (μ := Q s) (𝒢.le s) hF).symm

#print axioms fractional_pulse_bias_trim_eq
#print axioms fractional_pulse_bias_past_integral

end RoughHeston
