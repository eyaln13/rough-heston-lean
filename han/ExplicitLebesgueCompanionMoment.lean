import ExplicitLebesgueAggregateForward
import AggregateDyadicVarianceMoments

/-! Uniform original companion moments on the complete focal law. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open GirsanovPort
set_option maxHeartbeats 1600000

variable {T : ℝ≥0} {α κ σ b ε v₀ : ℝ}
local notation "I" => FixedMeshClusterIndex (T:ℝ) b ε
local notation "Ω" => CanonicalPath T (CoupledPhysicalState I)
local notation "Ω'" => Ω × (ℝ≥0 → ℝ)

/-- The unpulsed companion has a canonical dyadic moment bound independent
of the focal cluster count and the pulse duration. -/
theorem explicitLebesguePulseLaw_companion_dyadic_bound
    (L : FractionalFixedMeshLaw T α κ σ (lebesgueMeshInitial T b ε v₀) (lebesgueMeshInput T α b ε))
    (hT : 0 < T) (hα : 1/2 < α) (hα' : α < 1) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ)
    (hb : 0 < b) (hε : 0 < ε) (hv₀ : 0 ≤ v₀) (j : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    let C := v₀+constantImmigrationConvolution α b T
    let V := canonicalPhysicalVariance T (none : Option I) t
    Integrable (fun p : Ω => (V p)^(2^j:ℕ)) (L.law : Measure Ω) ∧
    (∫ p : Ω, (V p)^(2^j:ℕ) ∂(L.law : Measure Ω)) ≤ fractionalAggregateMomentCap σ α T C j := by
  intro C V
  let μ := (L.law : Measure Ω)
  let P := μ.prod gaussianLimit
  have hα₀ : 0 < α := by linarith
  have hΓ : 0 < Real.Gamma α*α := mul_pos (Real.Gamma_pos_of_pos hα₀) hα₀
  have hC : 0 ≤ C := by
    unfold C constantImmigrationConvolution
    exact add_nonneg hv₀ (mul_nonneg hb.le (div_nonneg (Real.rpow_nonneg (le_max_right _ _) _) hΓ.le))
  have hDet (r : ℝ) (hr : r ∈ Icc (0:ℝ) T) : v₀+constantImmigrationConvolution α b r ≤ C := by
    unfold C constantImmigrationConvolution
    rw [max_eq_left hr.1, max_eq_left T.coe_nonneg]
    exact add_le_add_right (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow hr.1 hr.2 hα₀.le) hΓ.le) hb.le) _
  obtain ⟨B,hB₂,hB,hNull,hM,hClock,_,⟨Y⟩⟩ := explicitLebesguePulseLaw_aggregate_forward L hT hα hα' hσ hb hε
  obtain ⟨hYI,hYM⟩ := aggregateVariance_dyadic_moment_le hα hα'.le hκ hB hNull hB₂ hM hClock
    Y.predictable Y.nonnegative Y.integrable Y.meanLe Y.continuous_pathLp.stronglyMeasurable
    Y.continuous_pathLp.continuousOn Y.rep hC hDet Y.forward j t ht
  let U := FractionalFixedMeshLaw.liftedAggregateVariance (ι := I) (T := T) canonicalSecondVariance
  have hfst : MeasurePreserving (Prod.fst : Ω' → Ω) P μ := measurePreserving_fst
  have hNonneg := hfst.quasiMeasurePreserving.ae L.nonnegative
  have hEq : (fun z : Ω' => (U t z)^(2^j:ℕ)) =ᵐ[P] fun z => (V z.1)^(2^j:ℕ) := by
    filter_upwards [hNonneg] with z hz
    change (max 0 (V z.1))^(2^j:ℕ) = (V z.1)^(2^j:ℕ)
    exact congrArg (fun x : ℝ => x^(2^j:ℕ)) (max_eq_right (hz none (canonicalEvalTime T t)))
  have hVm : Measurable (fun p : Ω => (V p)^(2^j:ℕ)) := by
    have hc : Continuous V := ((continuous_apply none).comp continuous_fst).comp (continuous_canonicalPathEval T t)
    exact hc.measurable.pow_const _
  constructor
  · change Integrable (fun p : Ω => (V p)^(2^j:ℕ)) μ
    rw [← hfst.map_eq]
    exact (integrable_map_measure hVm.aestronglyMeasurable hfst.aemeasurable).2 (hYI.congr hEq)
  · change (∫ p : Ω, (V p)^(2^j:ℕ) ∂μ) ≤ _
    rw [← hfst.map_eq, integral_map hfst.aemeasurable hVm.aestronglyMeasurable]
    exact (le_of_eq (integral_congr_ae hEq).symm).trans hYM

#print axioms RoughHeston.explicitLebesguePulseLaw_companion_dyadic_bound

end RoughHeston
