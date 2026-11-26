import Verification
import ProductKernelEnergy

open MeasureTheory Filter Set
open scoped MeasureTheory NNReal Topology

namespace RoughHeston

theorem fractionalK_measurable (α : ℝ) : Measurable (fractionalK α) :=
  Measurable.ite measurableSet_Iic measurable_const
    ((measurable_id.pow_const _).div_const _)

theorem fractionalL_measurable (α : ℝ) : Measurable (fractionalL α) :=
  Measurable.ite measurableSet_Iic measurable_const
    ((measurable_id.pow_const _).div_const _)

private theorem causal_rpow_div_integrableOn_Ioc {p : ℝ} (hp : -1 < p) (c T : ℝ) :
    IntegrableOn (fun s : ℝ => if s ≤ 0 then 0 else s ^ p / c) (Ioc 0 T) := by
  by_cases hT : 0 ≤ T
  · have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1
      (intervalIntegral.intervalIntegrable_rpow' hp)
    have hc : Integrable (fun s : ℝ => s ^ p * c⁻¹)
        (volume.restrict (Ioc 0 T)) := h.mul_const _
    refine hc.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [ite_eq_right (not_le_of_gt hs.1), div_eq_mul_inv]
  · rw [Ioc_eq_empty (not_lt.mpr (le_of_not_ge hT))]
    exact integrableOn_empty

/-- The fractional Volterra kernel is integrable on every bounded
positive-time interval. -/
theorem fractionalK_integrableOn_Ioc {α : ℝ} (hα : 0 < α) (T : ℝ) :
    IntegrableOn (fractionalK α) (Ioc 0 T) :=
  causal_rpow_div_integrableOn_Ioc (by linarith : -1 < α - 1) (Real.Gamma α) T

/-- The fractional inverse kernel is integrable on every bounded
positive-time interval. -/
theorem fractionalL_integrableOn_Ioc {α : ℝ} (hα : α < 1) (T : ℝ) :
    IntegrableOn (fractionalL α) (Ioc 0 T) :=
  causal_rpow_div_integrableOn_Ioc (by linarith : -1 < -α) (Real.Gamma (1 - α)) T

theorem fractionalL_reflected_integrableOn_Ioc {α t : ℝ} (hα : α < 1) (ht : 0 ≤ t) :
    IntegrableOn (fun s : ℝ => fractionalL α (t - s)) (Ioc 0 t) := by
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).2
    (fractionalL_integrableOn_Ioc hα t)
  have hr := hi.comp_sub_left t
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).1
  simpa only [sub_zero, sub_self] using hr.symm

/-- Reflect the inverse kernel in the observation time and transfer
its L¹ bound to the nonnegative time coordinate. -/
theorem fractionalL_reflected_integrable_hestonTimeMeasure
    {α : ℝ} (hα : α < 1) (t : ℝ≥0) :
    Integrable (fun s : ℝ≥0 => fractionalL α ((t : ℝ) - (s : ℝ))) (hestonTimeMeasure t) := by
  have hm : Measurable (fun s : ℝ≥0 => fractionalL α ((t : ℝ) - (s : ℝ))) :=
    (fractionalL_measurable α).comp (measurable_const.sub measurable_subtype_coe)
  have hi : Integrable (fun s : ℝ => fractionalL α ((t : ℝ) - s))
      (volume.restrict (Ioo (0 : ℝ) (t : ℝ))) :=
    (fractionalL_reflected_integrableOn_Ioc hα (NNReal.coe_nonneg t)).mono_set Ioo_subset_Ioc_self
  apply (integrable_map_measure hm.aestronglyMeasurable
    continuous_real_toNNReal.measurable.aemeasurable).2
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  simp only [Function.comp_apply, Real.coe_toNNReal s hs.1.le]

end RoughHeston

#print axioms RoughHeston.fractionalK_integrableOn_Ioc
#print axioms RoughHeston.fractionalL_integrableOn_Ioc
#print axioms RoughHeston.fractionalL_reflected_integrableOn_Ioc
#print axioms RoughHeston.fractionalL_reflected_integrable_hestonTimeMeasure
