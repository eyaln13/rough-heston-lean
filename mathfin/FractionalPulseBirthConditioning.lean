import ActualFractionalPulse
import LaplaceBoundary

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace RoughHeston

/-- Conditioning on a positive event known at time zero preserves the
supplied age filtration and each of its martingales. -/
theorem martingale_under_birth_conditioning
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {𝒢 : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ} {A : Set Ω}
    (hA : MeasurableSet[𝒢 0] A) (hApos : 0<P A)
    (hM : Martingale M 𝒢 P) :
    Martingale M 𝒢 (@boundaryConditionedMeasure Ω m P A) := by
  let _ : MeasurableSpace Ω := m
  let Q := boundaryConditionedMeasure P A
  let : IsProbabilityMeasure Q := boundaryConditionedMeasure_isProbability hApos
  have hfin : (P A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hApos.ne'
  have hInt (t : ℝ≥0) : Integrable (M t) Q := (hM.integrable t).restrict.smul_measure hfin
  refine martingale_of_past_set_integrals hM.stronglyAdapted hInt ?_
  intro s t hst E hE
  have hEm : MeasurableSet E := 𝒢.le s E hE
  have hAs : MeasurableSet[𝒢 s] A := 𝒢.mono (show 0≤s from zero_le) A hA
  have hSet (r : ℝ≥0) : (∫ ω in E,M r ω ∂Q)=
      (P A)⁻¹.toReal*(∫ ω in E∩A,M r ω ∂P) := by
    unfold Q boundaryConditionedMeasure
    rw [Measure.restrict_smul,Measure.restrict_restrict hEm,integral_smul_measure,smul_eq_mul]
  rw [hSet,hSet,hM.setIntegral_eq hst (hE.inter hAs)]

/-- The actual fractional pulse remains an inverse pulse solution after
conditioning at birth. All compensation identities use the same
supplied age filtration and the original pulse normalization. -/
theorem FractionalPulseProcess.condition_at_birth
    {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝒢 : Filtration ℝ≥0 m} {M U C : ℝ≥0 → Ω → ℝ}
    {α κ a ε d : ℝ} {H : ℝ≥0} {A : Set Ω}
    (hP : FractionalPulseProcess P 𝒢 H α κ a ε d M U C)
    (hA : MeasurableSet[𝒢 0] A) (hApos : 0<P A) :
    FractionalPulseProcess (@boundaryConditionedMeasure Ω m P A) 𝒢 H α κ a ε d M U C := by
  let _ : MeasurableSpace Ω := m
  let Q := boundaryConditionedMeasure P A
  have hfin : (P A)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hApos.ne'
  have hAC : Q ≪ P :=
    ((Measure.AbsolutelyContinuous.refl (P.restrict A)).smul_left _).trans
      Measure.restrict_le_self.absolutelyContinuous
  exact ⟨martingale_under_birth_conditioning hA hApos hP.martingale,
    fun t => ((hP.martingale_memLp t).mono_measure Measure.restrict_le_self).smul_measure hfin,
    hP.martingale_continuous,hAC.ae_le hP.martingale_zero,
    hP.variance_adapted,hP.variance_continuous,hP.variance_nonnegative,hP.variance_zero,
    martingale_under_birth_conditioning hA hApos hP.compensated_square,
    fun t => (hP.compensator_integrable t).restrict.smul_measure hfin,
    fun s t hst => hAC.ae_le (hP.compensator_monotone s t hst),
    fun t ht => hAC.ae_le (hP.compensator t ht),hAC.ae_le hP.inverse⟩

#print axioms FractionalPulseProcess.condition_at_birth

end RoughHeston
