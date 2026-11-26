import RectangularPulseMeasure
import FractionalKernelIncrements

open MeasureTheory Set Filter
open scoped Interval

namespace RoughHeston
namespace GirsanovPort

private theorem K_positive {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    0 < fractionalK α s := by
  rw [fractionalK, ite_eq_right (not_le_of_gt hs)]
  exact div_pos (Real.rpow_pos_of_pos hs _) (Real.Gamma_pos_of_pos hα)

private theorem K_reflect_integral {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    (∫ v in Ioc (0 : ℝ) s, fractionalK α (s-v)) = s ^ α / (Real.Gamma α * α) := by
  have he : fractionalK α = hestonKernel α := by
    funext x
    by_cases hx : 0 < x <;> simp [fractionalK, hestonKernel, hx, le_of_not_gt]
  rw [← intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_comp_sub_left,
    sub_self, sub_zero, he]
  exact hestonKernel_integral hα hs.le

private theorem K_le_twice_at_half {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    fractionalK α (s/2) ≤ 2 * fractionalK α s := by
  have hh : 0 < s / 2 := by positivity
  rw [fractionalK, fractionalK, ite_eq_right (not_le_of_gt hh), ite_eq_right (not_le_of_gt hs),
    Real.rpow_sub_one hh.ne', Real.rpow_sub_one hs.ne']
  have he : (s/2) ^ α / (s/2) / Real.Gamma α = 2 * ((s/2) ^ α / s / Real.Gamma α) := by
    field_simp
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply div_le_div_of_nonneg_right _ (Real.Gamma_pos_of_pos hα).le
  apply div_le_div_of_nonneg_right _ hs.le
  exact Real.rpow_le_rpow hh.le (by linarith) hα.le

/-- A local upper comparison of the causal resolvent gives the mean
profile bound for all ages, including the elapsed part of the pulse. -/
theorem rectangularPulse_resolvent_mean_upper {α ε d r s : ℝ} {R : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : 0 ≤ ε) (hd : 0 < d)
    (hs : s ∈ Ioc (0 : ℝ) r) (hR : Measurable R)
    (hComp : ∀ u ∈ Ioc (0 : ℝ) r, 0 ≤ R u ∧ R u ≤ 2 * fractionalK α u) :
    volterraConvolution R (rectangularPulseRate ε d) s ≤ (4/α) * ε * fractionalK α s := by
  by_cases hsd : 2*d ≤ s
  · let ν := rectangularPulseMeasure ε d s
    have : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d s
    obtain ⟨hmass, hage⟩ := rectangularPulseMeasure_postpulse hε hd hsd
    have hsh : 0 < s/2 := by linarith [hs.1]
    have hBounds : ∀ᵐ v ∂ν, 0 ≤ R (s-v) ∧ R (s-v) ≤ 4 * fractionalK α s := by
      filter_upwards [hage] with v hv
      have hpos : 0 < s-v := hsh.trans_le hv.1
      obtain ⟨h₀,h₁⟩ := hComp _ ⟨hpos, hv.2.trans hs.2⟩
      have hmono : fractionalK α (s-v) ≤ fractionalK α (s/2) := by
        rw [fractionalK, fractionalK, ite_eq_right (not_le_of_gt hpos), ite_eq_right (not_le_of_gt hsh)]
        exact div_le_div_of_nonneg_right
          (Real.rpow_le_rpow_of_nonpos hsh hv.1 (sub_nonpos.mpr hα')) (Real.Gamma_pos_of_pos hα).le
      refine ⟨h₀, h₁.trans ?_⟩
      calc
        _ ≤ 2 * fractionalK α (s/2) := mul_le_mul_of_nonneg_left hmono (by norm_num)
        _ ≤ 2 * (2 * fractionalK α s) := mul_le_mul_of_nonneg_left (K_le_twice_at_half hα hs.1) (by norm_num)
        _ = _ := by ring
    have hI : Integrable (fun v => R (s-v)) ν := by
      refine (integrable_const (4 * fractionalK α s)).mono'
        (hR.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
      filter_upwards [hBounds] with v hv
      simpa only [Real.norm_of_nonneg hv.1] using hv.2
    rw [← rectangularPulseMeasure_integral_eq_convolution hε hd]
    have h := integral_mono_ae hI (integrable_const (4 * fractionalK α s)) (hBounds.mono fun _ hv => hv.2)
    rw [integral_const, smul_eq_mul, hmass] at h
    convert h.trans ?_ using 1
    rw [show ε * (4 * fractionalK α s) = 4 * (ε * fractionalK α s) by ring, mul_assoc]
    exact mul_le_mul_of_nonneg_right ((le_div_iff₀ hα).2 (by linarith))
      (mul_nonneg hε (K_positive hα hs.1).le)
  · let ν := volume.restrict (Ioc (0 : ℝ) s)
    let j := rectangularPulseRate ε d
    have hj : Measurable j := measurable_const.indicator measurableSet_Ioc
    have hjB (v : ℝ) : 0 ≤ j v ∧ j v ≤ ε/d := by
      by_cases hv : v ∈ Ioc (0 : ℝ) d
      · simp [j, rectangularPulseRate, indicator_of_mem hv, div_nonneg hε hd.le]
      · simp [j, rectangularPulseRate, indicator_of_notMem hv, div_nonneg hε hd.le]
    have hB : ∀ᵐ v ∂ν, 0 ≤ R (s-v) * j v ∧
        R (s-v) * j v ≤ (2 * (ε/d)) * fractionalK α (s-v) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne s)] with v hv hvne
      have hv' : 0 < s - v := sub_pos.mpr (lt_of_le_of_ne hv.2 hvne)
      obtain ⟨h₀,h₁⟩ := hComp _ ⟨hv', (sub_le_self _ hv.1.le).trans hs.2⟩
      refine ⟨mul_nonneg h₀ (hjB v).1, ?_⟩
      exact (mul_le_mul h₁ (hjB v).2 (hjB v).1
        (mul_nonneg (by norm_num) (K_positive hα hv').le)).trans_eq (by ring)
    have hK : Integrable (fun v => fractionalK α (s-v)) ν := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).mp
      have h := (intervalIntegrable_iff_integrableOn_Ioc_of_le hs.1.le).mpr
        (fractionalK_integrableOn_Ioc hα s)
      simpa only [sub_zero, sub_self] using (h.comp_sub_left s).symm
    have hK' : Integrable (fun v => (2 * (ε/d)) * fractionalK α (s-v)) ν := hK.const_mul _
    have hI : Integrable (fun v => R (s-v) * j v) ν := by
      refine hK'.mono' ((hR.comp (measurable_const.sub measurable_id)).mul hj).aestronglyMeasurable ?_
      exact hB.mono fun v hv => by simpa only [Real.norm_of_nonneg hv.1] using hv.2
    have hi := integral_mono_ae hI hK' (hB.mono fun _ hv => hv.2)
    rw [integral_const_mul, K_reflect_integral hα hs.1] at hi
    unfold volterraConvolution
    change (∫ v, R (s-v) * j v ∂ν) ≤ _
    refine hi.trans ?_
    have hpow : s ^ α = s ^ (α-1) * s := by
      conv_lhs => rw [show α = α - 1 + 1 by ring, Real.rpow_add_one hs.1.ne']
    have hs' : s / d ≤ 2 := (div_le_iff₀ hd).2 (by linarith)
    have he : (2 * (ε/d)) * (s ^ α / (Real.Gamma α * α)) =
        (2 * (s / d) / α) * ε * fractionalK α s := by
      rw [fractionalK, ite_eq_right (not_le_of_gt hs.1), hpow]
      ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) hα.le) hε) (K_positive hα hs.1).le

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.rectangularPulse_resolvent_mean_upper
