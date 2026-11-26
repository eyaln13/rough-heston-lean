import AffinePointPathData
import ProductKernelEnergy

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

/-- Reflection of a square-integrable Riccati row to the physical clock. -/
theorem reflected_riccati_memLp_two (T : ℝ≥0) {w : ℝ → ℝ}
    (hw : Measurable w) (hw₂ : IntegrableOn (fun r => w r ^ 2) (Ioc 0 (T:ℝ)))
    (σ : ℝ) :
    MemLp (fun s : ℝ≥0 => σ * w ((T:ℝ)-(s:ℝ))) 2 (hestonTimeMeasure T) := by
  have hi : IntervalIntegrable (fun s => w s ^ 2) volume 0 (T:ℝ) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg T)).2 hw₂
  have hi' : IntervalIntegrable (fun s => w ((T:ℝ)-s) ^ 2) volume (T:ℝ) 0 := by
    simpa only [sub_zero,sub_self] using hi.comp_sub_left (T:ℝ)
  have hm : Measurable (fun s : ℝ => w ((T:ℝ)-s)) :=
    hw.comp (measurable_const.sub measurable_id)
  have hr : MemLp (fun s : ℝ => w ((T:ℝ)-s)) 2 (volume.restrict (Ioc (0:ℝ) (T:ℝ))) :=
    (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le (NNReal.coe_nonneg T)).1 hi'.symm)
  have hsmall : MemLp (fun s : ℝ => w ((T:ℝ)-s)) 2 (volume.restrict (Ioo (0:ℝ) (T:ℝ))) :=
    hr.mono_measure (Measure.restrict_mono Ioo_subset_Ioc_self le_rfl)
  have htarget : Measurable (fun s : ℝ≥0 => w ((T:ℝ)-(s:ℝ))) :=
    hm.comp measurable_subtype_coe
  have h : MemLp (fun s : ℝ≥0 => w ((T:ℝ)-(s:ℝ))) 2 (hestonTimeMeasure T) := by
    apply (memLp_map_measure_iff htarget.aestronglyMeasurable
      continuous_real_toNNReal.measurable.aemeasurable).2
    refine MemLp.ae_eq ?_ hsmall
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    simp only [Function.comp_apply,Real.coe_toNNReal s hs.1.le]
  exact h.const_mul σ

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.reflected_riccati_memLp_two
