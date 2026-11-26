import BridgeGirsanovDensityToJoint
import SHEStochastic.NativeTimeCut
import AffineVariancePreterminal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston.GirsanovPort

open SHEStochastic

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

noncomputable def affineEnergyClock {Ω : Type*} (g : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ r in (0 : ℝ)..(t : ℝ), g r.toNNReal ω ^ 2

private theorem hestonTimeMeasure_integral_le {H t : ℝ≥0} (ht : t ≤ H)
    {f : ℝ≥0 → ℝ} (hf : Measurable f) :
    (∫ r, (Iic t).indicator f r ∂hestonTimeMeasure H) =
      ∫ r in (0 : ℝ)..(t : ℝ), f r.toNNReal := by
  rw [hestonTimeMeasure, integral_map continuous_real_toNNReal.measurable.aemeasurable
    (hf.indicator measurableSet_Iic).aestronglyMeasurable,
    Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    intervalIntegral.integral_of_le (μ := volume) (f := fun r : ℝ => f r.toNNReal) t.coe_nonneg]
  have hEq : (fun r : ℝ => (Iic t).indicator f r.toNNReal) =ᵐ[volume.restrict (Ioc 0 (H : ℝ))]
      (Iic (t : ℝ)).indicator (fun r => f r.toNNReal) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : r.toNNReal ≤ t ↔ r ≤ (t : ℝ) := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hr.1.le]
    simp only [indicator, mem_Iic, he]
  rw [integral_congr_ae hEq, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  congr 1
  congr 1
  ext r
  have hm : (t : ℝ) ≤ (H : ℝ) := NNReal.coe_le_coe.mpr ht
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  exact ⟨fun h => ⟨h.2.1,h.1⟩,fun h => ⟨h.2,h.1,h.2.trans hm⟩⟩

theorem affineEnergyClock_prior_eq
    (u : Lp ℝ 2 (jointPredictableMeasure F μ H)) {g : ℝ≥0 → Ω → ℝ}
    (hg : IsStronglyPredictable F g) (hu : ⇑u =ᵐ[jointPredictableMeasure F μ H] Function.uncurry g)
    {t : ℝ≥0} (ht : t ≤ H) :
    NativeEnergy.energy (NativeTimeCut.prior t u) =ᵐ[μ] affineEnergyClock g t := by
  let v := NativeTimeCut.prior t u
  let b (p : ℝ≥0 × Ω) := if p.1 ≤ t then g p.1 p.2 else 0
  have hv : ⇑v =ᵐ[jointPredictableMeasure F μ H] b := by
    filter_upwards [NativeTimeCut.prior_ae t u, hu] with p hp hgu
    change u p = g p.1 p.2 at hgu
    rw [hp]
    change (if t < p.1 then (0 : ℝ) else u p) = b p
    rw [hgu]
    by_cases hh : p.1 ≤ t <;> simp [b, hh, not_lt.mpr]
  have he := nativeEnergy_ae_eq_hestonEnergy v b hv
  filter_upwards [he] with ω hω
  rw [hω]
  simp only [Real.norm_eq_abs, sq_abs]
  have hf : Measurable (fun r => g r ω ^ 2) :=
    (((hg.mono F.predictable_le_prod).measurable.comp (measurable_id.prodMk measurable_const))).pow_const 2
  unfold affineEnergyClock
  rw [← hestonTimeMeasure_integral_le ht hf]
  apply integral_congr_ae
  exact ae_of_all _ fun r => by by_cases hr : r ≤ t <;> simp [b, hr]

theorem affineEnergyClock_stronglyAdapted {g : ℝ≥0 → Ω → ℝ}
    (hg : StronglyAdapted F g) (hc : ∀ ω, Continuous (fun r => g r ω)) :
    StronglyAdapted F (affineEnergyClock g) := by
  intro t
  have h := weighted_time_primitive_stronglyMeasurable
    (fun r => (hg r).pow 2) (fun ω => (hc ω).pow 2) (d := fun _ => 1) measurable_const t
  change StronglyMeasurable[F t] (fun ω => ∫ s in (0 : ℝ)..(t : ℝ), g s.toNNReal ω ^ 2)
  simpa only [Pi.pow_apply, one_mul] using h

omit m in
theorem affineEnergyClock_continuous {g : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (fun r => g r ω)) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => affineEnergyClock g t ω) := by
  have h : Continuous (fun r : ℝ => g r.toNNReal ω ^ 2) := ((hc ω).comp continuous_real_toNNReal).pow 2
  exact (intervalIntegral.continuous_primitive (fun a b => h.intervalIntegrable a b) 0).comp
    NNReal.continuous_coe

omit m in
/-- The ordinary bracket energy obeys the exponential integral
identity path by path over the physical horizon. -/
theorem affineEnergyClock_exp_identity {g : ℝ≥0 → Ω → ℝ}
    (hc : ∀ ω, Continuous (fun r => g r ω)) (ω : Ω) :
    let Φ (t : ℝ≥0) := Real.exp (affineEnergyClock g t ω) * g t ω ^ 2
    Integrable Φ (hestonTimeMeasure H) ∧
      Real.exp (affineEnergyClock g H ω) = 1 + ∫ t, Φ t ∂hestonTimeMeasure H := by
  let a (r : ℝ) := g r.toNNReal ω ^ 2
  let A (r : ℝ) := ∫ x in (0 : ℝ)..r, a x
  let φ (r : ℝ) := Real.exp (A r) * a r
  have ha : Continuous a := ((hc ω).comp continuous_real_toNNReal).pow 2
  have hA : ∀ r, HasDerivAt A (a r) r := fun r =>
    intervalIntegral.integral_hasDerivAt_right (ha.intervalIntegrable 0 r)
      ha.stronglyMeasurable.stronglyMeasurableAtFilter ha.continuousAt
  have hφ : Continuous φ :=
    (Real.continuous_exp.comp (intervalIntegral.continuous_primitive (fun x y => ha.intervalIntegrable x y) 0)).mul ha
  have he : (∫ x in (0 : ℝ)..(H : ℝ), φ x) = Real.exp (A (H : ℝ)) - 1 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r _ => (hA r).exp) (hφ.intervalIntegrable 0 H)
    simpa only [A, intervalIntegral.integral_same, Real.exp_zero] using h
  let Φ (t : ℝ≥0) := Real.exp (affineEnergyClock g t ω) * g t ω ^ 2
  have hΦ : Continuous Φ := (Real.continuous_exp.comp (affineEnergyClock_continuous hc ω)).mul ((hc ω).pow 2)
  have hI : Integrable Φ (hestonTimeMeasure H) := by
    unfold hestonTimeMeasure
    rw [integrable_map_measure hΦ.stronglyMeasurable.aestronglyMeasurable continuous_real_toNNReal.measurable.aemeasurable,
      Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    have h : IntegrableOn φ (Ioc (0 : ℝ) (H : ℝ)) := (hφ.intervalIntegrable 0 H).1
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simp only [φ, a, Function.comp_apply, Φ, affineEnergyClock, A, Real.coe_toNNReal _ hr.1.le]
  have hΦeq : (∫ t, Φ t ∂hestonTimeMeasure H) = ∫ r in (0 : ℝ)..(H : ℝ), φ r := by
    calc
      _ = ∫ r, (Iic H).indicator Φ r ∂hestonTimeMeasure H := by
        apply integral_congr_ae
        filter_upwards [ae_time_lt_hestonTimeMeasure H] with r hr
        rw [indicator_of_mem hr.le]
      _ = ∫ r in (0 : ℝ)..(H : ℝ), Φ r.toNNReal := hestonTimeMeasure_integral_le le_rfl hΦ.measurable
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro r hr
        rw [uIcc_of_le H.coe_nonneg] at hr
        simp only [φ, a, Φ, affineEnergyClock, A, Real.coe_toNNReal _ hr.1]
  refine ⟨hI, ?_⟩
  rw [hΦeq, he]
  change Real.exp (A (H : ℝ)) = _
  ring

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.affineEnergyClock_prior_eq
#print axioms RoughHeston.GirsanovPort.affineEnergyClock_exp_identity
