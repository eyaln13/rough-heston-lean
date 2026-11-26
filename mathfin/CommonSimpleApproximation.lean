import JointItoAssembly
import ProductKernelEnergy
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {P Q : Measure Ω} [IsFiniteMeasure P] [IsFiniteMeasure Q]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

private theorem jointPredictableMeasure_add :
    jointPredictableMeasure F (P + Q) H =
      jointPredictableMeasure F P H + jointPredictableMeasure F Q H := by
  unfold jointPredictableMeasure
  rw [Measure.prod_add, trim_add]

/-- One sequence of elementary predictable integrands approximates a
fixed raw representative in both joint L² spaces. -/
theorem exists_jointSimpleApproximation_two_measures {f : ℝ≥0 × Ω → ℝ}
    (hf : StronglyMeasurable[F.predictable] f)
    (hP : MemLp f 2 (jointPredictableMeasure F P H))
    (hQ : MemLp f 2 (jointPredictableMeasure F Q H)) :
    ∃ V : ℕ → JointTBoundedSP H F,
      Tendsto (fun n => jointSimpleAssembly (μ := P) H F (V n)) atTop (𝓝 (hP.toLp f)) ∧
      Tendsto (fun n => jointSimpleAssembly (μ := Q) H F (V n)) atTop (𝓝 (hQ.toLp f)) ∧
      Tendsto (fun n => eLpNorm ((Function.uncurry ⇑(V n).val) - f) 2
        ((hestonTimeMeasure H).prod Q)) atTop (𝓝 0) := by
  let ν := jointPredictableMeasure F (P + Q) H
  let νP := jointPredictableMeasure F P H
  let νQ := jointPredictableMeasure F Q H
  have hBoth : MemLp f 2 ν := by
    rw [show ν = νP + νQ from jointPredictableMeasure_add]
    exact hP.add_measure hQ
  let v := hBoth.toLp f
  let A := jointSimpleAssembly (μ := P + Q) H F
  have hv := (jointSimpleAssembly_denseRange (μ := P + Q) H F) v
  obtain ⟨a, ha, haLim⟩ := mem_closure_iff_seq_limit.mp hv
  choose V hV using ha
  have hVL : Tendsto (fun n => A (V n)) atTop (𝓝 v) := by
    apply haLim.congr
    intro n
    exact (hV n).symm
  have hApprox₀ : Tendsto (fun n => eLpNorm (⇑(A (V n)) - f) 2 ν) atTop (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hBoth).mp hVL
  have hApprox : Tendsto (fun n => eLpNorm ((Function.uncurry ⇑(V n).val) - f) 2 ν) atTop (𝓝 0) := by
    apply hApprox₀.congr
    intro n
    exact eLpNorm_congr_ae ((jointSimpleAssembly_ae (μ := P + Q) (V n)).sub EventuallyEq.rfl)
  have hleP : νP ≤ ν := by rw [show ν = νP + νQ from jointPredictableMeasure_add]; exact Measure.le_add_right le_rfl
  have hleQ : νQ ≤ ν := by rw [show ν = νP + νQ from jointPredictableMeasure_add]; exact Measure.le_add_left le_rfl
  have hmono {η : @Measure (ℝ≥0 × Ω) F.predictable} (he : η ≤ ν) :
      Tendsto (fun n => eLpNorm ((Function.uncurry ⇑(V n).val) - f) 2 η) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hApprox
      (fun _ => zero_le) (fun _ => eLpNorm_mono_measure _ he)
  have hLift {R : Measure Ω} [IsFiniteMeasure R]
      (hR : MemLp f 2 (jointPredictableMeasure F R H))
      (hle : jointPredictableMeasure F R H ≤ ν) :
      Tendsto (fun n => jointSimpleAssembly (μ := R) H F (V n)) atTop (𝓝 (hR.toLp f)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ hR).mpr
    apply (hmono hle).congr
    intro n
    exact eLpNorm_congr_ae (((jointSimpleAssembly_ae (μ := R) (V n)).sub EventuallyEq.rfl).symm)
  refine ⟨V, hLift hP hleP, hLift hQ hleQ, ?_⟩
  apply (hmono hleQ).congr
  intro n
  rw [hestonTimeMeasure_eq_horizon]
  have hSm : StronglyMeasurable[F.predictable] (Function.uncurry ⇑(V n).val) := (V n).val.isStronglyPredictable
  exact eLpNorm_trim F.predictable_le_prod (hSm.sub hf)

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.exists_jointSimpleApproximation_two_measures
