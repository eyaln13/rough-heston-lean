import ProductKernelEnergy
import JointPredictableDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m}

/-- The deterministic time coordinate is measurable in the predictable σ-algebra. -/
theorem measurable_fst_jointPredictable (𝒢 : Filtration ℝ≥0 m) :
    @Measurable (ℝ≥0 × Ω) ℝ≥0 𝒢.predictable _ Prod.fst := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  apply measurable_of_Ioi
  intro s
  rw [show (Prod.fst : ℝ≥0 × Ω → ℝ≥0) ⁻¹' Ioi s = Ioi s ×ˢ (univ : Set Ω) by
    ext z
    simp]
  exact measurableSet_predictable_Ioi_prod (𝓕 := 𝒢) MeasurableSet.univ

private theorem measurable_real_time_jointPredictable (𝒢 : Filtration ℝ≥0 m) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝒢.predictable _ (fun z => (z.1 : ℝ)) :=
  measurable_subtype_coe.comp (measurable_fst_jointPredictable 𝒢)

theorem heston_convolutionWeight_predictable
    (α : ℝ) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ} (hV : IsStronglyPredictable 𝒢 V) :
    IsStronglyPredictable 𝒢 (hestonConvolutionWeight α t V) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  have hVm : Measurable (Function.uncurry V) := StronglyMeasurable.measurable hV
  have htime : Measurable (fun z : ℝ≥0 × Ω => (t : ℝ) - (z.1 : ℝ)) :=
    measurable_const.sub (measurable_real_time_jointPredictable 𝒢)
  exact (((hestonKernel_measurable α).comp htime).mul hVm.sqrt).stronglyMeasurable

theorem heston_cutoffWeight_predictable
    (α : ℝ) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ} (hV : IsStronglyPredictable 𝒢 V) (n : ℕ) :
    IsStronglyPredictable 𝒢 (hestonCutoffWeight α t V n) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := 𝒢.predictable
  have hVm : Measurable (Function.uncurry V) := StronglyMeasurable.measurable hV
  have htime : Measurable (fun z : ℝ≥0 × Ω => (t : ℝ) - (z.1 : ℝ)) :=
    measurable_const.sub (measurable_real_time_jointPredictable 𝒢)
  have hcut : Measurable (fun z : ℝ≥0 × Ω =>
      max ((n : ℝ) + 1)⁻¹ ((t : ℝ) - (z.1 : ℝ))) :=
    measurable_const.max htime
  exact (((hestonKernel_measurable α).comp hcut).mul
    (hVm.sqrt.min measurable_const)).stronglyMeasurable

/-- Each cutoff weight has a deterministic uniform bound. -/
theorem heston_cutoffWeight_bound {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (t : ℝ≥0) (V : ℝ≥0 → Ω → ℝ) (n : ℕ) (s : ℝ≥0) (ω : Ω) :
    ‖hestonCutoffWeight α t V n s ω‖ ≤
      hestonKernel α ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) := by
  let r : ℝ := (n : ℝ) + 1
  let z : ℝ := max r⁻¹ ((t : ℝ) - (s : ℝ))
  let q : ℝ := min (Real.sqrt (V s ω)) r
  have hr : 0 < r := by dsimp [r]; positivity
  have hinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hz : r⁻¹ ≤ z := le_max_left _ _
  have hp := hinv.trans_le hz
  have hq : 0 ≤ q := le_min (Real.sqrt_nonneg _) hr.le
  have hg := (Real.Gamma_pos_of_pos hα).le
  have hk : 0 ≤ hestonKernel α z := by
    simp only [hestonKernel, ite_eq_left hp]
    exact div_nonneg (Real.rpow_nonneg hp.le _) hg
  have hkr : hestonKernel α z ≤ hestonKernel α r⁻¹ := by
    simp only [hestonKernel, ite_eq_left hp, ite_eq_left hinv]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hinv hz (sub_nonpos.mpr hα')) hg
  change ‖hestonKernel α z * q‖ ≤ hestonKernel α r⁻¹ * r
  rw [Real.norm_of_nonneg (mul_nonneg hk hq)]
  exact mul_le_mul hkr (min_le_right _ _) hq (hk.trans hkr)

theorem heston_cutoff_weight_memLp_two_joint [IsFiniteMeasure μ]
    {α : ℝ} (hα : 0 < α) (hα' : α ≤ 1) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hV : IsStronglyPredictable 𝒢 V) (n : ℕ) :
    MemLp (Function.uncurry (hestonCutoffWeight α t V n)) 2
      (jointPredictableMeasure 𝒢 μ t) := by
  have hm : StronglyMeasurable[𝒢.predictable] (Function.uncurry (hestonCutoffWeight α t V n)) :=
    heston_cutoffWeight_predictable α t hV n
  exact MemLp.of_bound hm.aestronglyMeasurable _
    (Eventually.of_forall fun z => heston_cutoffWeight_bound hα hα' t V n z.1 z.2)

/-- Trimming to the predictable σ-algebra preserves the energy seminorm
of a predictable function. -/
theorem eLpNorm_jointPredictableMeasure_eq_product (t : ℝ≥0) {p : ℝ≥0∞}
    {f : ℝ≥0 × Ω → ℝ} (hf : StronglyMeasurable[𝒢.predictable] f) :
    eLpNorm f p (jointPredictableMeasure 𝒢 μ t) = eLpNorm f p ((hestonTimeMeasure t).prod μ) := by
  rw [hestonTimeMeasure_eq_horizon]
  exact eLpNorm_trim 𝒢.predictable_le_prod hf

theorem heston_convolution_weight_memLp_two_joint [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hV : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    MemLp (Function.uncurry (hestonConvolutionWeight α t V)) 2 (jointPredictableMeasure 𝒢 μ t) := by
  have hV' : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hV
  have hVm := (hV'.mono 𝒢.predictable_le_prod).measurable
  have hprod := heston_convolution_weight_memLp_two hα t hVm hVnonneg hVint hmean
  exact (le_of_eq (eLpNorm_jointPredictableMeasure_eq_product t
    (heston_convolutionWeight_predictable α t hV))).trans_lt hprod

theorem heston_cutoff_weight_L2_joint_of_uniform_mean [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) (hα' : α ≤ 1) (t : ℝ≥0) {V : ℝ≥0 → Ω → ℝ}
    (hV : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    Tendsto (fun n => eLpNorm
      (fun z : ℝ≥0 × Ω => hestonCutoffWeight α t V n z.1 z.2 -
        hestonConvolutionWeight α t V z.1 z.2) 2 (jointPredictableMeasure 𝒢 μ t))
      atTop (𝓝 0) := by
  have hV' : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hV
  have hVm := (hV'.mono 𝒢.predictable_le_prod).measurable
  have hd (n : ℕ) : StronglyMeasurable[𝒢.predictable]
      (fun z : ℝ≥0 × Ω => hestonCutoffWeight α t V n z.1 z.2 -
        hestonConvolutionWeight α t V z.1 z.2) :=
    (heston_cutoffWeight_predictable α t hV n).sub
      (heston_convolutionWeight_predictable α t hV)
  simpa only [fun n => eLpNorm_jointPredictableMeasure_eq_product (μ := μ) t (p := 2) (hd n)] using
    heston_cutoff_weight_L2_of_uniform_mean hα hα' t hVm hVnonneg hVint hmean

end RoughHeston

#print axioms RoughHeston.heston_convolutionWeight_predictable
#print axioms RoughHeston.heston_cutoffWeight_predictable
#print axioms RoughHeston.heston_cutoff_weight_memLp_two_joint
#print axioms RoughHeston.eLpNorm_jointPredictableMeasure_eq_product
#print axioms RoughHeston.heston_convolution_weight_memLp_two_joint
#print axioms RoughHeston.heston_cutoff_weight_L2_joint_of_uniform_mean
