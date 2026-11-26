import PulsedImmigration

open MeasureTheory Set
open scoped MeasureTheory

namespace RoughHeston

/-- The response to a full or partly elapsed pulse of width at most
`d` is bounded by its input rate times the first `d` units of kernel
mass. The estimate is uniform for nonnegative kernels dominated by
the fractional Heston kernel. -/
theorem heston_pulse_convolution_le {k : ℝ → ℝ} {α ε d a b t : ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : 0 ≤ ε) (hd : 0 < d)
    (hab : a ≤ b) (hbt : b ≤ t) (hw : b - a ≤ d)
    (hkm : Measurable k) (hk₀ : ∀ x > 0, 0 ≤ k x)
    (hkK : ∀ x > 0, k x ≤ hestonKernel α x) :
    (∫ s in a..b, (ε / d) * k (t - s)) ≤
      (ε / d) * (d ^ α / (Real.Gamma α * α)) := by
  let l := b - a
  let r := t - b
  have hl : 0 ≤ l := sub_nonneg.mpr hab
  have hr : 0 ≤ r := sub_nonneg.mpr hbt
  have hdom (x : ℝ) (hx : 0 < x) : k (x + r) ≤ hestonKernel α x := by
    have hxr : 0 < x + r := hx.trans_le (le_add_of_nonneg_right hr)
    refine (hkK _ hxr).trans ?_
    rw [hestonKernel, hestonKernel, ite_eq_left hxr, ite_eq_left hx]
    exact div_le_div_of_nonneg_right
      (Real.rpow_le_rpow_of_nonpos hx (le_add_of_nonneg_right hr) (sub_nonpos.mpr hα'))
      (Real.Gamma_pos_of_pos hα).le
  have hbase (D : ℝ) : IntegrableOn (hestonKernel α) (Ioc 0 D) := by
    have he : hestonKernel α = fractionalK α := by
      funext x
      by_cases h : x ≤ 0
      · simp [hestonKernel, fractionalK, h, not_lt.mpr h]
      · simp [hestonKernel, fractionalK, h, lt_of_not_ge h]
    rw [he]
    exact fractionalK_integrableOn_Ioc hα D
  have hcomp : (∫ x in (0 : ℝ)..l, k (x + r)) ≤
      ∫ x in (0 : ℝ)..l, hestonKernel α x := by
    rw [intervalIntegral.integral_of_le hl, intervalIntegral.integral_of_le hl]
    have hmono := (ae_restrict_mem (μ := volume) (s := Ioc (0 : ℝ) l)
      measurableSet_Ioc).mono fun x hx => hdom x hx.1
    have hi : IntegrableOn (fun x => k (x + r)) (Ioc (0 : ℝ) l) := by
      apply (hbase l).mono' (hkm.comp (measurable_id.add measurable_const)).aestronglyMeasurable
      filter_upwards [hmono, ae_restrict_mem measurableSet_Ioc] with x hx hm
      change ‖k (x + r)‖ ≤ hestonKernel α x
      rw [Real.norm_of_nonneg (hk₀ _ (hm.1.trans_le (le_add_of_nonneg_right hr)))]
      exact hx
    exact integral_mono_ae hi (hbase l) hmono
  have hfull : (∫ x in (0 : ℝ)..l, hestonKernel α x) ≤
      ∫ x in (0 : ℝ)..d, hestonKernel α x := by
    rw [intervalIntegral.integral_of_le hl, intervalIntegral.integral_of_le hd.le]
    refine setIntegral_mono_set (hbase d) ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [hestonKernel, ite_eq_left hx.1]
      exact div_nonneg (Real.rpow_nonneg hx.1.le _) (Real.Gamma_pos_of_pos hα).le
    · exact ae_of_all _ (Ioc_subset_Ioc_right hw)
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left,
    ← hestonKernel_integral hα hd.le]
  have hshift : (∫ x in (0 : ℝ)..l, k (x + r)) = ∫ x in (t - b)..(t - a), k x := by
    rw [intervalIntegral.integral_comp_add_right, zero_add, show l + r = t - a by dsimp [l, r]; ring]
  rw [← hshift]
  exact mul_le_mul_of_nonneg_left (hcomp.trans hfull) (div_nonneg hε hd.le)

/-- At pulse width `d` and mass `d^α`, the response bound vanishes
at rate `d^(2α-1)`. -/
theorem heston_scaled_pulse_bound {α d : ℝ} (hd : 0 < d) :
    (d ^ α / d) * (d ^ α / (Real.Gamma α * α)) =
      d ^ (2 * α - 1) / (Real.Gamma α * α) := by
  have h : (d ^ α * d ^ α) / d = d ^ (2 * α - 1) := by
    calc
      _ = d ^ (α + α) / d ^ (1 : ℝ) := by rw [Real.rpow_add hd, Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hd, show α + α - 1 = 2 * α - 1 by ring]
  rw [← h]
  ring

end RoughHeston

#print axioms RoughHeston.heston_pulse_convolution_le
#print axioms RoughHeston.heston_scaled_pulse_bound
