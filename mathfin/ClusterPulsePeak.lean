import ClusterPulseMeanUpper
import PulsedImmigrationBounds

open MeasureTheory Set Filter
open scoped Interval

namespace RoughHeston.GirsanovPort

/-- Uniform peak of the deterministic rectangular-pulse response. -/
theorem rectangularPulse_resolvent_peak {α ε d r t : ℝ} {R : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : ε = d^α) (hd : 0 < d)
    (ht : t ∈ Ioc 0 r) (hR : Measurable R)
    (hcomp : ∀ u ∈ Ioc 0 r, 0 ≤ R u ∧ R u ≤ 2*fractionalK α u) :
    volterraConvolution R (rectangularPulseRate ε d) t ≤
      (4/(Real.Gamma α*α))*d^(2*α-1) := by
  have hε₀ : 0 ≤ ε := hε ▸ Real.rpow_nonneg hd.le _
  have hΓ := Real.Gamma_pos_of_pos hα
  by_cases hdt : d ≤ t
  · have hm := rectangularPulse_resolvent_mean_upper hα hα' hε₀ hd ht hR hcomp
    rw [fractionalK, ite_eq_right (not_le.mpr ht.1)] at hm
    have hpow := Real.rpow_le_rpow_of_nonpos hd hdt (sub_nonpos.mpr hα')
    have hjoin : d^α*d^(α-1) = d^(2*α-1) := by rw [← Real.rpow_add hd]; congr 1; ring
    refine hm.trans ?_
    rw [← hjoin, ← hε]
    have hcoeff : 0 ≤ (4/α)*ε/Real.Gamma α := by positivity
    have hz := mul_le_mul_of_nonneg_left hpow hcoeff
    convert hz using 1 <;> ring
  · have htd := le_of_not_ge hdt
    let ν := volume.restrict (Ioc 0 t)
    have hs := (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).2
      (fractionalK_integrableOn_Ioc hα t)
    have hki : Integrable (fun v => fractionalK α (t-v)) ν := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1.le).1
      simpa only [sub_zero,sub_self] using (hs.comp_sub_left t).symm
    have hb : ∀ᵐ v ∂ν, 0 ≤ R (t-v)*rectangularPulseRate ε d v ∧
        R (t-v)*rectangularPulseRate ε d v ≤ ((ε/d)*2)*fractionalK α (t-v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne t)] with v hv hvt
      have hr := hcomp (t-v) ⟨sub_pos.mpr (lt_of_le_of_ne hv.2 hvt), by linarith [ht.2,hv.1]⟩
      rw [rectangularPulseRate, indicator_of_mem (show v∈Ioc 0 d from ⟨hv.1,hv.2.trans htd⟩)]
      constructor
      · exact mul_nonneg hr.1 (div_nonneg hε₀ hd.le)
      · simpa only [mul_assoc,mul_comm,mul_left_comm] using
          mul_le_mul_of_nonneg_right hr.2 (div_nonneg hε₀ hd.le)
    have hmain : Integrable (fun v => R (t-v)*rectangularPulseRate ε d v) ν := by
      apply (hki.const_mul ((ε/d)*2)).mono'
        ((hR.comp (measurable_const.sub measurable_id)).mul
          (measurable_const.indicator measurableSet_Ioc)).aestronglyMeasurable
      filter_upwards [hb] with v hv
      change ‖R (t-v)*rectangularPulseRate ε d v‖ ≤ _
      rw [Real.norm_of_nonneg hv.1]; exact hv.2
    have h := integral_mono_ae hmain (hki.const_mul ((ε/d)*2)) (hb.mono fun _ hv => hv.2)
    have hker : (∫ v, fractionalK α (t-v) ∂ν) = t^α/(Real.Gamma α*α) := by
      rw [show (∫ v, fractionalK α (t-v) ∂ν) = ∫ v in (0:ℝ)..t, fractionalK α (t-v)
            by exact (intervalIntegral.integral_of_le ht.1.le).symm,
        intervalIntegral.integral_comp_sub_left, sub_self, sub_zero]
      have heq : fractionalK α = hestonKernel α := by
        funext x; by_cases hx : 0 < x <;> simp [fractionalK,hestonKernel,hx,le_of_not_gt]
      rw [heq]
      exact hestonKernel_integral hα ht.1.le
    rw [integral_const_mul,hker] at h
    change (∫ v, R (t-v)*rectangularPulseRate ε d v ∂ν) ≤ _
    refine h.trans ?_
    have hpow := Real.rpow_le_rpow ht.1.le htd hα.le
    have hpos := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow (mul_pos hΓ hα).le)
      (show 0 ≤ (ε/d)*2 by positivity)
    rw [hε] at hpos ⊢
    have hpeak := heston_scaled_pulse_bound (α := α) hd
    have hz : 0 ≤ d^(2*α-1)/(Real.Gamma α*α) := by positivity
    refine hpos.trans ?_
    calc
      _ = 2*((d^α/d)*(d^α/(Real.Gamma α*α))) := by ring
      _ = 2*(d^(2*α-1)/(Real.Gamma α*α)) := by rw [hpeak]
      _ ≤ 4*(d^(2*α-1)/(Real.Gamma α*α)) := by linarith only [hz]
      _ = _ := by ring

#print axioms rectangularPulse_resolvent_peak

end RoughHeston.GirsanovPort
