import JointHestonWeights

open MeasureTheory Filter Set
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

namespace RoughHeston

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℝ≥0 m}

private theorem heston_kernel_sq_intervalIntegrable {α : ℝ} (hα : 1 / 2 < α) (t : ℝ≥0) :
    IntervalIntegrable (fun r => hestonKernel α r ^ 2) volume 0 (t : ℝ) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg t)).2
    (hestonKernel_memLp_two hα t).integrable_sq

private theorem shifted_kernel_sq_before {α : ℝ} (hα : 1 / 2 < α) (u : ℝ≥0) :
    IntervalIntegrable (fun s => hestonKernel α ((u : ℝ) - s) ^ 2) volume 0 (u : ℝ) := by
  have h := (heston_kernel_sq_intervalIntegrable hα u).comp_sub_left (u : ℝ)
  simpa only [sub_zero, sub_self] using h.symm

private theorem shifted_kernel_sq_eq_zero_after (α : ℝ) {u s : ℝ} (hus : u ≤ s) :
    hestonKernel α (u - s) ^ 2 = 0 := by
  simp [hestonKernel, not_lt.mpr (sub_nonpos.mpr hus)]

private theorem shifted_kernel_sq_after (α : ℝ) {u T : ℝ≥0} (huT : u ≤ T) :
    IntervalIntegrable (fun s => hestonKernel α ((u : ℝ) - s) ^ 2)
      volume (u : ℝ) (T : ℝ) := by
  have huT' : (u : ℝ) ≤ (T : ℝ) := by exact_mod_cast huT
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huT').2
  have hz : Integrable (fun _ : ℝ => (0 : ℝ)) (volume.restrict (Ioc (u : ℝ) T)) :=
    integrable_zero _ _ _
  refine hz.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact (shifted_kernel_sq_eq_zero_after α hs.1.le).symm

private theorem shifted_kernel_sq_measurable (α : ℝ) (u : ℝ≥0) :
    Measurable (fun s : ℝ => hestonKernel α ((u : ℝ) - s)) :=
  (hestonKernel_measurable α).comp (measurable_const.sub measurable_id)

/-- The reflected kernel on the larger time horizon is still in L²,
since it vanishes at and after its own observation time. -/
theorem heston_shifted_kernel_memLp_two_horizon {α : ℝ} (hα : 1 / 2 < α)
    {u T : ℝ≥0} (huT : u ≤ T) :
    MemLp (fun s : ℝ≥0 => hestonKernel α ((u : ℝ) - (s : ℝ))) 2 (hestonTimeMeasure T) := by
  have hm := shifted_kernel_sq_measurable α u
  have hi := (shifted_kernel_sq_before hα u).trans (shifted_kernel_sq_after α huT)
  have hlarge : MemLp (fun s : ℝ => hestonKernel α ((u : ℝ) - s)) 2
      (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg T)).1 hi)
  have hsmall : MemLp (fun s : ℝ => hestonKernel α ((u : ℝ) - s)) 2
      (volume.restrict (Ioo (0 : ℝ) (T : ℝ))) :=
    hlarge.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have ht : Measurable (fun s : ℝ≥0 => hestonKernel α ((u : ℝ) - (s : ℝ))) :=
    hm.comp measurable_subtype_coe
  apply (memLp_map_measure_iff ht.aestronglyMeasurable
    continuous_real_toNNReal.measurable.aemeasurable).2
  refine MemLp.ae_eq ?_ hsmall
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp only [Function.comp_apply, Real.coe_toNNReal s hs.1.le]

/-- The fixed-horizon squared energy of the shifted kernel is exactly
the squared energy of the original kernel up to the observation time. -/
theorem integral_heston_shifted_kernel_sq_horizon {α : ℝ} (hα : 1 / 2 < α)
    {u T : ℝ≥0} (huT : u ≤ T) :
    (∫ s : ℝ≥0, hestonKernel α ((u : ℝ) - (s : ℝ)) ^ 2 ∂hestonTimeMeasure T) =
      ∫ r in (0 : ℝ)..(u : ℝ), hestonKernel α r ^ 2 := by
  let f (s : ℝ) := hestonKernel α ((u : ℝ) - s) ^ 2
  have hm : Measurable (fun s : ℝ≥0 => hestonKernel α ((u : ℝ) - (s : ℝ)) ^ 2) :=
    ((shifted_kernel_sq_measurable α u).comp measurable_subtype_coe).pow_const 2
  have huT' : (u : ℝ) ≤ (T : ℝ) := by exact_mod_cast huT
  have hzero : (∫ s in (u : ℝ)..(T : ℝ), f s) = 0 := by
    apply intervalIntegral.integral_zero_ae
    refine Eventually.of_forall fun s hs => ?_
    rw [uIoc_of_le huT'] at hs
    exact shifted_kernel_sq_eq_zero_after α hs.1.le
  calc
    _ = ∫ s in Ioo (0 : ℝ) (T : ℝ), f s := by
      rw [hestonTimeMeasure, integral_map_of_stronglyMeasurable
        continuous_real_toNNReal.measurable hm.stronglyMeasurable]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      simp only [f, Real.coe_toNNReal s hs.1.le]
    _ = ∫ s in (0 : ℝ)..(T : ℝ), f s := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
        intervalIntegral.integral_of_le (NNReal.coe_nonneg T)]
    _ = ∫ s in (0 : ℝ)..(u : ℝ), f s := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (shifted_kernel_sq_before hα u) (shifted_kernel_sq_after α huT), hzero, add_zero]
    _ = _ := by
      simpa only [sub_self, sub_zero] using intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := (u : ℝ)) (fun r => hestonKernel α r ^ 2) (u : ℝ)

private theorem heston_convolution_weight_memLp_two_product_horizon [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) {u T : ℝ≥0} (huT : u ≤ T) {V : ℝ≥0 → Ω → ℝ}
    (hVmeas : Measurable (Function.uncurry V)) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    MemLp (Function.uncurry (hestonConvolutionWeight α u V)) 2
      ((hestonTimeMeasure T).prod μ) :=
  memLp_kernel_mul_sqrt_of_uniform_mean (heston_shifted_kernel_memLp_two_horizon hα huT)
    hVmeas hVnonneg hVint hmean

/-- The uncut Heston weight at time `u` is in predictable L² on any
fixed horizon reaching `u`. -/
theorem heston_convolution_weight_memLp_two_joint_horizon [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) {u T : ℝ≥0} (huT : u ≤ T) {V : ℝ≥0 → Ω → ℝ}
    (hV : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    MemLp (Function.uncurry (hestonConvolutionWeight α u V)) 2
      (jointPredictableMeasure 𝒢 μ T) := by
  have hV' : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hV
  have hprod := heston_convolution_weight_memLp_two_product_horizon hα huT
    (hV'.mono 𝒢.predictable_le_prod).measurable hVnonneg hVint hmean
  exact (le_of_eq (eLpNorm_jointPredictableMeasure_eq_product T
    (heston_convolutionWeight_predictable α u hV))).trans_lt hprod

/-- The squared L² norm on a fixed predictable horizon is bounded by the
uniform first moment times the squared deterministic kernel integral. -/
theorem heston_convolution_weight_energy_le [IsFiniteMeasure μ]
    {α : ℝ} (hα : 1 / 2 < α) {u T : ℝ≥0} (huT : u ≤ T) {V : ℝ≥0 → Ω → ℝ}
    (hV : IsStronglyPredictable 𝒢 V) (hVnonneg : ∀ s ω, 0 ≤ V s ω)
    (hVint : ∀ s, Integrable (V s) μ) {C : ℝ}
    (hmean : ∀ s, (∫ ω, V s ω ∂μ) ≤ C) :
    (eLpNorm (Function.uncurry (hestonConvolutionWeight α u V)) 2
      (jointPredictableMeasure 𝒢 μ T)).toReal ^ 2 ≤
      C * (∫ r in (0 : ℝ)..(T : ℝ), hestonKernel α r ^ 2) := by
  let k (s : ℝ≥0) := hestonKernel α ((u : ℝ) - (s : ℝ))
  let H := Function.uncurry (hestonConvolutionWeight α u V)
  have hk : MemLp k 2 (hestonTimeMeasure T) := heston_shifted_kernel_memLp_two_horizon hα huT
  have hV' : StronglyMeasurable[𝒢.predictable] (Function.uncurry V) := hV
  have hH : MemLp H 2 ((hestonTimeMeasure T).prod μ) :=
    heston_convolution_weight_memLp_two_product_horizon hα huT
      (hV'.mono 𝒢.predictable_le_prod).measurable hVnonneg hVint hmean
  have hHsm : StronglyMeasurable[𝒢.predictable] H :=
    heston_convolutionWeight_predictable α u hV
  have hC : 0 ≤ C :=
    (integral_nonneg (hVnonneg 0)).trans (hmean 0)
  let : IsFiniteMeasure (hestonTimeMeasure T) := by
    unfold hestonTimeMeasure
    infer_instance
  rw [eLpNorm_jointPredictableMeasure_eq_product T hHsm, ← Lp.norm_toLp H hH,
    norm_toLp_two_sq hH, integral_prod _ hH.integrable_sq]
  have hEq (s : ℝ≥0) : (∫ ω, H (s, ω) ^ 2 ∂μ) = k s ^ 2 * ∫ ω, V s ω ∂μ := by
    change (∫ ω, (k s * Real.sqrt (V s ω)) ^ 2 ∂μ) = _
    simp_rw [mul_pow, Real.sq_sqrt (hVnonneg s _), integral_const_mul]
  calc
    _ ≤ ∫ s, k s ^ 2 * C ∂hestonTimeMeasure T :=
      integral_mono hH.integrable_sq.integral_prod_left (hk.integrable_sq.mul_const C)
        (fun s => (hEq s).trans_le (mul_le_mul_of_nonneg_left (hmean s) (sq_nonneg _)))
    _ = C * (∫ r in (0 : ℝ)..(u : ℝ), hestonKernel α r ^ 2) := by
      rw [integral_mul_const, mul_comm _ C]
      congr 1
      exact integral_heston_shifted_kernel_sq_horizon hα huT
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (intervalIntegral.integral_mono_interval le_rfl (NNReal.coe_nonneg u)
        (by exact_mod_cast huT) (Eventually.of_forall fun _ => sq_nonneg _)
        (heston_kernel_sq_intervalIntegrable hα T)) hC

end RoughHeston

#print axioms RoughHeston.heston_shifted_kernel_memLp_two_horizon
#print axioms RoughHeston.integral_heston_shifted_kernel_sq_horizon
#print axioms RoughHeston.heston_convolution_weight_memLp_two_joint_horizon
#print axioms RoughHeston.heston_convolution_weight_energy_le
