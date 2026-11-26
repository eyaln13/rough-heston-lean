import CanonicalPulseBirthTrace
import PhysicalCompletionIntegralTransfer

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

/-- A shorter observation horizon uses the same pulse paths, noise and
compensation; only the interval on which the inverse is needed changes. -/
theorem FractionalPulseProcess.shorten {Ω : Type*} {m : MeasurableSpace Ω}
    {P : Measure Ω} {F : Filtration ℝ≥0 m} {H H' : ℝ≥0}
    {α κ a ε d : ℝ} {M U C : ℝ≥0→Ω→ℝ}
    (hP : FractionalPulseProcess P F H α κ a ε d M U C) (hH : H'≤H) :
    FractionalPulseProcess P F H' α κ a ε d M U C :=
  ⟨hP.martingale,hP.martingale_memLp,hP.martingale_continuous,hP.martingale_zero,
    hP.variance_adapted,hP.variance_continuous,hP.variance_nonnegative,hP.variance_zero,
    hP.compensated_square,hP.compensator_integrable,hP.compensator_monotone,
    (fun t ht => hP.compensator t (ht.trans hH)),
    hP.inverse.mono (fun _ hr r h => hr r ⟨h.1,h.2.trans (NNReal.coe_le_coe.mpr hH)⟩)⟩

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]

/-- The event estimate on the birth trace is converted to the original
probability by the actual birth mass. Completion leaves that mass fixed. -/
theorem physical_birthTrace_event_real {A E : Set Ω} (hA : MeasurableSet[m] A)
    (hAp : 0<P A) (hE : MeasurableSet[m] E) :
    P.real (E∩A) = P.real A *
      (@birthTraceLaw Ω (physicalCompletedSpace P) (physicalCompletedMeasure P) A).real
        ((Subtype.val : A→Ω) ⁻¹' E) := by
  let Pc := physicalCompletedMeasure P
  have hAc : MeasurableSet[physicalCompletedSpace P] A := physical_ambient_le_completion P A hA
  have hEc : MeasurableSet[physicalCompletedSpace P] E := physical_ambient_le_completion P E hE
  let _ : MeasurableSpace Ω := physicalCompletedSpace P
  have he : (birthTraceLaw Pc A) ((Subtype.val : A→Ω) ⁻¹' E) =
      (boundaryConditionedMeasure Pc A) E := by
    rw [← Measure.map_apply measurable_subtype_coe hEc,birthTraceLaw_map hAc]
  have hE' : (birthTraceLaw Pc A).real ((Subtype.val : A→Ω) ⁻¹' E) =
      (boundaryConditionedMeasure Pc A).real E :=
    congrArg ENNReal.toReal he
  rw [hE',physical_completion_birth_probability P A hE]
  unfold boundaryConditionedMeasure Measure.real
  rw [Measure.smul_apply,Measure.restrict_apply hE,smul_eq_mul,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hpos : 0<(P A).toReal := ENNReal.toReal_pos hAp.ne' (measure_ne_top _ _)
  field_simp

/-- A trace-level linear lower probability times a uniform birth atom
gives a linear probability on the original physical mesh. -/
theorem physical_birthTrace_linear_event {A E : Set Ω} (hA : MeasurableSet[m] A)
    (hAp : 0<P A) (hE : MeasurableSet[m] E)
    {c cB ε : ℝ} (hc : 0≤c) (hε : 0≤ε) (hB : cB≤P.real A)
    (hTrace : c*ε ≤ (@birthTraceLaw Ω (physicalCompletedSpace P) (physicalCompletedMeasure P) A).real
      ((Subtype.val : A→Ω) ⁻¹' E)) :
    (cB*c)*ε ≤ P.real (E∩A) := by
  rw [physical_birthTrace_event_real hA hAp hE,mul_assoc]
  exact (mul_le_mul_of_nonneg_right hB (mul_nonneg hc hε)).trans
    (mul_le_mul_of_nonneg_left hTrace ENNReal.toReal_nonneg)

#print axioms FractionalPulseProcess.shorten
#print axioms physical_birthTrace_event_real
#print axioms physical_birthTrace_linear_event

end RoughHeston
