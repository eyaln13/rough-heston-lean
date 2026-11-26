import SHEStochastic.FilteredItoCLM
import JointItoAssembly

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {B M : ℝ≥0 → Ω → ℝ}

/-- The public SHE arbitrary-filtration predictable measure is definitionally
our finite-horizon measure under the current-pin compatibility shim. -/
theorem filteredPredictableMeasure_eq_joint (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u)) :
    SHEStochastic.FilteredItoCLM.trimMeasure_T (𝓖 := F) (μ := μ) T hBmeas =
      jointPredictableMeasure F μ T := rfl

/-- The two scalar elementary embeddings represent the same simple process. -/
theorem filteredSimpleAssembly_eq_joint (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (V : JointTBoundedSP T F) :
    SHEStochastic.FilteredItoCLM.simpleAssembly_T (𝓖 := F) (μ := μ) T hBmeas V =
      jointSimpleAssembly T F V := rfl

/-- The public SHE scalar Itô map agrees with the existing joint Itô map
for any stopped martingale agreeing with the Brownian driver up to `T`. -/
theorem filteredItoIntegralCLM_eq_joint [IsFilteredPreBrownian B F μ] (hB : IsPreBrownianReal B μ)
    (T : ℝ≥0) (hBmeas : ∀ u, Measurable (B u))
    (hM₂ : ∀ u, MemLp (M u) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun u ω => M u ω ^ 2 - ((min u T : ℝ≥0) : ℝ)) F μ)
    (hagree : ∀ u ≤ T, B u =ᵐ[μ] M u)
    (φ : Lp ℝ 2 (jointPredictableMeasure F μ T)) :
    SHEStochastic.FilteredItoCLM.itoIntegralCLM_T (𝓖 := F) hB T hBmeas φ =
      jointItoIntegralCLM T hM₂ φ := by
  let L := SHEStochastic.FilteredItoCLM.itoIntegralCLM_T (𝓖 := F) hB T hBmeas
  let R := jointItoIntegralCLM (𝒢 := F) T hM₂
  change L φ = R φ
  refine congrFun ((jointSimpleAssembly_denseRange (μ := μ) T F).equalizer L.continuous R.continuous ?_) φ
  funext V
  change L (jointSimpleAssembly T F V) = R (jointSimpleAssembly T F V)
  have heL : L (jointSimpleAssembly T F V) =
      SHEStochastic.FilteredItoL2.itoSimpleLp (F := F) hB hBmeas V.val := by
    rw [← filteredSimpleAssembly_eq_joint T hBmeas (μ := μ) V]
    exact SHEStochastic.FilteredItoCLM.itoIntegralCLM_T_simpleAssembly_T hB T hBmeas V
  have heR : R (jointSimpleAssembly T F V) = jointItoAssembly T hM₂ V :=
    jointItoIntegralCLM_agrees T hM₂ hM hclock V
  rw [heL, heR]
  let a := SHEStochastic.FilteredItoL2.memLp_itoSimple hB hBmeas V.val
  let b := memLp_jointItoSimple hM₂ V.val
  have hp : ∀ᵐ ω ∂μ, ∀ p ∈ V.val.value.support,
      B p.1 ω = M p.1 ω ∧ B p.2 ω = M p.2 ω := by
    refine (ae_ball_iff V.val.value.support.finite_toSet.countable).2 fun p hp => ?_
    exact (hagree p.1 ((V.val.le_of_mem_support_value p hp).trans (V.property p hp))).and
      (hagree p.2 (V.property p hp))
  apply Lp.ext
  filter_upwards [a.coeFn_toLp, b.coeFn_toLp, hp] with ω ha hb hω
  change a.toLp _ ω = b.toLp _ ω
  rw [ha, hb, SHEStochastic.FilteredItoL2.itoSimple_apply, jointItoSimple]
  simp only [Finsupp.sum]
  exact Finset.sum_congr rfl (fun p hp => by rw [(hω p hp).1, (hω p hp).2])

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.filteredPredictableMeasure_eq_joint
#print axioms RoughHeston.GirsanovPort.filteredSimpleAssembly_eq_joint
#print axioms RoughHeston.GirsanovPort.filteredItoIntegralCLM_eq_joint
