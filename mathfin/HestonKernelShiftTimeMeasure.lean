import HestonKernelShiftWeights

/-! Transfer the reflected kernel estimates to the stochastic time measure. -/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Interval

namespace RoughHeston

set_option maxHeartbeats 1000000

/-- Exact measure-transfer for deterministic real kernel weights on
the nonnegative stochastic time coordinate. -/
theorem integrable_hestonTimeMeasure_of_intervalIntegrable {T : ℝ≥0} {f : ℝ → ℝ}
    (hf : Measurable f) (hfi : IntervalIntegrable f volume 0 (T:ℝ)) :
    Integrable (fun t : ℝ≥0 => f t) (hestonTimeMeasure T) := by
  have hm : Measurable (fun t : ℝ≥0 => f t) := hf.comp measurable_subtype_coe
  unfold hestonTimeMeasure
  apply (integrable_map_measure hm.aestronglyMeasurable continuous_real_toNNReal.measurable.aemeasurable).2
  rw [restrict_Ioo_eq_restrict_Ioc]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).1 hfi
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  simp only [Function.comp_apply, Real.coe_toNNReal t ht.1.le]

theorem hestonKernel_shift_squared_energy_hestonTimeMeasure {α σ s t : ℝ} {T : ℝ≥0}
    (hα : 1/2 < α) (hα' : α ≤ 1) (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ (T:ℝ)) :
    let K := fun r : ℝ≥0 => hestonKernel α (t-(r:ℝ))-hestonKernel α (s-(r:ℝ))
    Integrable (fun r => (σ*K r)^2) (hestonTimeMeasure T) ∧
    (∫ r, (σ*K r)^2 ∂hestonTimeMeasure T) ≤
      (σ^2*(2/(Real.Gamma α^2*(2*α-1))))*(t-s)^(2*α-1) := by
  intro K
  let Kreal (r : ℝ) := hestonKernel α (t-r)-hestonKernel α (s-r)
  let f (r : ℝ) := (σ*Kreal r)^2
  have hk : Measurable Kreal := ((hestonKernel_measurable α).comp
    (measurable_const.sub measurable_id)).sub ((hestonKernel_measurable α).comp (measurable_const.sub measurable_id))
  have hf : Measurable f := (hk.const_mul σ).pow_const _
  have hi := (intervalIntegrable_hestonKernelDifference hα hs (hs.trans hst) (hst.trans htT) htT).1.const_mul (σ^2)
  have hfi : IntervalIntegrable f volume 0 (T:ℝ) := by
    simpa only [f,Kreal,mul_pow] using hi
  have hei := integrable_hestonTimeMeasure_of_intervalIntegrable hf hfi
  refine ⟨hei, ?_⟩
  have hm : Measurable (fun r : ℝ≥0 => f r) := hf.comp measurable_subtype_coe
  have hEq : (∫ r, f (r:ℝ) ∂hestonTimeMeasure T) = ∫ r in (0:ℝ)..(T:ℝ), f r := by
    rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable hm.aestronglyMeasurable,
      restrict_Ioo_eq_restrict_Ioc, intervalIntegral.integral_of_le T.coe_nonneg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    simp only [Function.comp_apply, Real.coe_toNNReal r hr.1.le]
  change (∫ r, f (r:ℝ) ∂hestonTimeMeasure T) ≤ _
  rw [hEq]
  simp only [f,Kreal,mul_pow,intervalIntegral.integral_const_mul]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hestonKernel_lower_shift_energy_mass hα hα' hs hst htT).1 (sq_nonneg _)

#print axioms RoughHeston.hestonKernel_shift_squared_energy_hestonTimeMeasure

end RoughHeston
