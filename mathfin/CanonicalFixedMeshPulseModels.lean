import CanonicalFractionalPulseAge
import FractionalFixedMeshLaw

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}
local notation "Path" => CanonicalPath T (CoupledPhysicalState ι)
local notation "𝒢" => canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T

namespace FractionalFixedMeshLaw

variable (L : FractionalFixedMeshLaw T α κ σ v β)

/-- The competitor is an actual boundary process in the common physical
filtration underlying the fixed-mesh law. -/
theorem actualCompanionBoundary {b : ℝ} (hα : α<1) (hv : 0≤v none)
    (hb : β none = fun _ => b) :
    HestonBoundaryProcess (L.law:Measure Path) 𝒢 T α κ (σ^2/2) b (v none)
      (canonicalPhysicalResidual T none) (canonicalRegularVariance T none (v none))
      (canonicalPhysicalCompensator T σ none none) := by
  obtain ⟨B,hB⟩ := L.variance_uniform_memLp 1
  have hB0 : 0≤B :=
    (integral_nonneg (fun _ => sq_nonneg _)).trans ((hB none 0 zero_le).2)
  refine canonicalCompanion_boundaryProcess_of_inverse hα hv L.law L.starts L.nonnegative
    ?_ (L.residualMartingale none) (fun t => L.residual_memLp (i := none) t)
    (L.productMartingale none none) hB0 ?_ ?_
  · simpa only [hb] using L.inverse none
  · intro t ht
    norm_num at hB
    exact (hB none t ht).1
  · exact fun t ht => (hB none t ht).2

/-- The focal pulse uses the same physical filtration, translated to its
birth age, and the matching coordinate and compensator. -/
theorem actualFractionalPulse {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d) :
    FractionalPulseProcess (L.law:Measure Path) (pulseAgeFiltration 𝒢 τ) (T-τ)
      α κ (σ^2/2) ε d (fun t => canonicalPhysicalResidual T (some i) (τ+t))
      (canonicalPulseAgeVariance T τ i (v (some i)))
      (fun t => canonicalPhysicalCompensator T σ (some i) (some i) (τ+t)) := by
  refine canonicalFractionalPulse_at_age hα hκ hv L.law L.starts L.nonnegative hτ ?_
    (L.residualMartingale (some i)) (fun t => L.residual_memLp (i := some i) t)
    (L.productMartingale (some i) (some i))
  simpa only [hβ] using L.inverse (some i)

/-- Conditioning on extinction of the competitor at the birth time is
conditioning on an age-zero event in the common filtration. -/
theorem actualFractionalPulse_at_companion_zero {i : ι} {τ : ℝ≥0} {ε d : ℝ}
    (hα : α<1) (hκ : 0≤κ) (hτ : τ≤T) (hv : v (some i)=0)
    (hβ : β (some i)=translatedPulseRate τ ε d)
    (hA : 0 < (L.law:Measure Path) {p | canonicalRegularVariance T none (v none) τ p=0}) :
    FractionalPulseProcess
      (boundaryConditionedMeasure (L.law:Measure Path) {p | canonicalRegularVariance T none (v none) τ p=0})
      (pulseAgeFiltration 𝒢 τ) (T-τ)
      α κ (σ^2/2) ε d (fun t => canonicalPhysicalResidual T (some i) (τ+t))
      (canonicalPulseAgeVariance T τ i (v (some i)))
      (fun t => canonicalPhysicalCompensator T σ (some i) (some i) (τ+t)) := by
  apply (L.actualFractionalPulse hα hκ hτ hv hβ).condition_at_birth _ hA
  change MeasurableSet[𝒢 (τ+0)] {p | canonicalRegularVariance T none (v none) τ p=0}
  rw [add_zero]
  exact measurableSet_eq_fun ((canonicalRegularVariance_adapted (T := T) (none : Option ι) (v none) τ).measurable)
    measurable_const

end FractionalFixedMeshLaw

#print axioms FractionalFixedMeshLaw.actualCompanionBoundary
#print axioms FractionalFixedMeshLaw.actualFractionalPulse
#print axioms FractionalFixedMeshLaw.actualFractionalPulse_at_companion_zero

end RoughHeston
