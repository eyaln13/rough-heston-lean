module
public import MathFin.Probability.Brownian.Ito.ItoIntegralCLM

@[expose] public section
open MeasureTheory
open scoped NNReal

namespace MathFin.ItoIntegralCLM

noncomputable def timeMeasure_T (T : ℝ≥0) : Measure ℝ≥0 :=
  ItoIntegralL2.timeMeasure.restrict (Set.Ioc 0 T)

instance (T : ℝ≥0) : IsFiniteMeasure (timeMeasure_T T) :=
  inferInstanceAs (IsFiniteMeasure (timeMeasureHorizon T))

noncomputable def trimMeasure_T {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {B : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :=
  ((timeMeasure_T T).prod μ).trim (ItoIntegralL2.natFiltration (mΩ := mΩ) hBmeas).predictable_le_prod

alias itoIntegralCLM_T := itoIntegralCLM
alias itoIntegralCLM_T_norm := itoIntegralCLM_norm

end MathFin.ItoIntegralCLM
