import SHEStochastic.FiniteScalarIto
import BridgeFilteredItoJoint

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω ι : Type*} [m : MeasurableSpace Ω] [DecidableEq ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 m} {T : ℝ≥0}
  {M : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
/-- The predictable measure underlying the public native Girsanov
coordinate integral is the same as the project measure. -/
theorem finiteScalarInputMeasure_eq_joint :
    FiniteScalarIto.inputMeasure F μ T = jointPredictableMeasure F μ T := rfl

/-- The physical predictable measure in the public transport statement
agrees with the existing joint measure. -/
theorem processMeasure_eq_joint :
    (SHE.PredictableL2.energyMeasure μ T).trim (SHE.PredictableL2.predictable_le_product F) =
      jointPredictableMeasure F μ T :=
  (FilteredScalarIto.processMeasure_eq (𝓖 := F) (μ := μ) (B := fun _ _ => (0 : ℝ))
    T (fun _ => measurable_const)).trans finiteScalarInputMeasure_eq_joint

/-- The scalar coordinate of the public native integral agrees with
the project integral whenever the drivers agree through the horizon. -/
theorem finiteScalarIntegralCLM_eq_joint (P : FiniteScalarIto.Coordinates F μ T ι) (i : ι)
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u T : ℝ≥0) : ℝ)) F μ)
    (hagree : ∀ u ≤ T, P.W i u =ᵐ[μ] M u)
    (φ : Lp ℝ 2 (jointPredictableMeasure F μ T)) :
    FiniteScalarIto.integralCLM P i φ = jointItoIntegralCLM T hM₂ φ := by
  let L := FiniteScalarIto.integralCLM P i
  let R := jointItoIntegralCLM (𝒢 := F) T hM₂
  change L φ = R φ
  refine congrFun ((jointSimpleAssembly_denseRange (μ := μ) T F).equalizer L.continuous R.continuous ?_) φ
  funext V
  change L (jointSimpleAssembly T F V) = R (jointSimpleAssembly T F V)
  have heL : L (jointSimpleAssembly T F V) = FiniteScalarIto.simpleLp P i V :=
    FiniteScalarIto.integralCLM_simple P i V
  have heR : R (jointSimpleAssembly T F V) = jointItoAssembly T hM₂ V :=
    jointItoIntegralCLM_agrees T hM₂ hM hclock V
  rw [heL, heR]
  let a := FiniteScalarIto.memLp_simpleValue P i V
  let b := memLp_jointItoSimple hM₂ V.val
  have hp : ∀ᵐ ω ∂μ, ∀ p ∈ V.val.value.support,
      P.W i p.1 ω = M p.1 ω ∧ P.W i p.2 ω = M p.2 ω := by
    refine (ae_ball_iff V.val.value.support.finite_toSet.countable).2 fun p hp => ?_
    exact (hagree p.1 ((V.val.le_of_mem_support_value p hp).trans (V.property p hp))).and
      (hagree p.2 (V.property p hp))
  apply Lp.ext
  filter_upwards [a.coeFn_toLp, b.coeFn_toLp, hp] with ω ha hb hω
  change a.toLp _ ω = b.toLp _ ω
  rw [ha, hb]
  change FilteredItoL2.itoSimple (FiniteScalarIto.measurable_coordinate P i) V.val ω =
    jointItoSimple M V.val ω
  rw [FilteredItoL2.itoSimple_apply, jointItoSimple]
  simp only [Finsupp.sum]
  exact Finset.sum_congr rfl (fun p hp => by rw [(hω p hp).1, (hω p hp).2])

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.finiteScalarInputMeasure_eq_joint
#print axioms RoughHeston.GirsanovPort.processMeasure_eq_joint
#print axioms RoughHeston.GirsanovPort.finiteScalarIntegralCLM_eq_joint
