import JointHestonWeights

open MeasureTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

/-- A strongly predictable real drift with square-integrable time
paths and a uniform energy cap is an element of the joint predictable
L² space. -/
theorem memLp_two_joint_of_pathwise_energy_cap {g : ℝ≥0 × Ω → ℝ}
    (hg : StronglyMeasurable[F.predictable] g)
    (hpaths : ∀ᵐ ω ∂μ, Integrable (fun r => g (r, ω) ^ 2) (hestonTimeMeasure H))
    {δ : ℝ} (hcap : ∀ᵐ ω ∂μ, (∫ r, g (r, ω) ^ 2 ∂hestonTimeMeasure H) ≤ δ) :
    MemLp g 2 (jointPredictableMeasure F μ H) := by
  haveI : IsFiniteMeasure (hestonTimeMeasure H) := by
    rw [hestonTimeMeasure_eq_horizon]
    infer_instance
  have hgprod : StronglyMeasurable g := hg.mono F.predictable_le_prod
  have hsq : StronglyMeasurable (fun z => g z ^ 2) := hgprod.pow _
  have hI : Integrable (fun z => g z ^ 2) ((hestonTimeMeasure H).prod μ) := by
    refine (integrable_prod_iff' hsq.aestronglyMeasurable).2 ⟨hpaths, ?_⟩
    refine (integrable_const δ).mono' hsq.norm.integral_prod_left'.aestronglyMeasurable ?_
    filter_upwards [hcap] with ω hω
    simp_rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact hω
  have hP := (memLp_two_iff_integrable_sq hgprod.aestronglyMeasurable).2 hI
  exact (le_of_eq (eLpNorm_jointPredictableMeasure_eq_product H hg)).trans_lt hP

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.memLp_two_joint_of_pathwise_energy_cap
