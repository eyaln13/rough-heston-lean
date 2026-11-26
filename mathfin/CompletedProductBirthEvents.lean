import CanonicalBirthProbabilities
import PhysicalPulseCoordinates

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω Γ : Type*} [m : MeasurableSpace Ω] [m' : MeasurableSpace Γ]
    (P : Measure Ω) (ν : Measure Γ) [IsProbabilityMeasure P] [IsProbabilityMeasure ν]

/-- Probabilities of canonical-coordinate events agree on the two completed spaces. -/
theorem completedProduct_fst_event {A : Set Ω} (hA : MeasurableSet[m] A) :
    (physicalCompletedMeasure (P.prod ν)).real (Prod.fst ⁻¹' A)=(physicalCompletedMeasure P).real A := by
  change ((P.prod ν) (Prod.fst ⁻¹' A)).toReal=(P A).toReal
  rw [(measurePreserving_fst (μ:=P) (ν:=ν)).measure_preimage hA.nullMeasurableSet]

/-- Completing the independent extension and conditioning at birth
preserve the original conditional probability of a companion event. -/
theorem completedProduct_birth_conditional {A E : Set Ω} (hA : MeasurableSet[m] A) (hE : MeasurableSet[m] E) :
    (@boundaryConditionedMeasure (Ω×Γ) (physicalCompletedSpace (P.prod ν))
      (physicalCompletedMeasure (P.prod ν)) (Prod.fst ⁻¹' A)).real (Prod.fst ⁻¹' E)=
      (@boundaryConditionedMeasure Ω (physicalCompletedSpace P) (physicalCompletedMeasure P) A).real E := by
  rw [physical_completion_birth_probability (P.prod ν) _ (measurable_fst hE),
    physical_completion_birth_probability P _ hE]
  unfold boundaryConditionedMeasure Measure.real
  rw [Measure.smul_apply,Measure.smul_apply,Measure.restrict_apply (measurable_fst hE),Measure.restrict_apply hE]
  have hp := measurePreserving_fst (μ:=P) (ν:=ν)
  rw [hp.measure_preimage hA.nullMeasurableSet, ← preimage_inter,
    hp.measure_preimage (hE.inter hA).nullMeasurableSet]

/-- A linear estimate for a coordinate event on the completed product
birth trace gives its unconditional lower bound on the original path law. -/
theorem completedProduct_birthTrace_to_original {A E : Set Ω} (hA : MeasurableSet[m] A) (hE : MeasurableSet[m] E)
    {c cB ε : ℝ} (hc : 0≤c) (hB₀ : 0<cB) (hε : 0≤ε) (hB : cB≤(physicalCompletedMeasure P).real A)
    (hTrace : c*ε≤
      (@birthTraceLaw (Ω×Γ) (physicalCompletedSpace (P.prod ν)) (physicalCompletedMeasure (P.prod ν))
        (Prod.fst ⁻¹' A)).real ((Subtype.val : (Prod.fst ⁻¹' A : Set (Ω×Γ))→Ω×Γ) ⁻¹' (Prod.fst ⁻¹' E))) :
    (cB*c)*ε≤P.real E := by
  have hB' : cB≤(P.prod ν).real (Prod.fst ⁻¹' A) := hB.trans_eq (completedProduct_fst_event P ν hA).symm
  have hp := (ENNReal.toReal_pos_iff.mp (hB₀.trans_le hB')).1
  have hh := physical_birthTrace_linear_event (P:=P.prod ν) (measurable_fst hA) hp (measurable_fst hE) hc hε hB' hTrace
  have hle : (P.prod ν).real ((Prod.fst ⁻¹' E)∩(Prod.fst ⁻¹' A))≤(P.prod ν).real (Prod.fst ⁻¹' E) :=
    measureReal_mono inter_subset_left
  exact (hh.trans hle).trans_eq (completedProduct_fst_event P ν hE)

#print axioms completedProduct_fst_event
#print axioms completedProduct_birth_conditional
#print axioms completedProduct_birthTrace_to_original

end RoughHeston
