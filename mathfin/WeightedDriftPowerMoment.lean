import KernelMomentTransfer
import ClusterRealMomentTransfer

/-! Deterministic signed time integrals controlled by a timewise
power moment, through their absolute kernel weights. -/

open MeasureTheory Filter Set
open scoped ENNReal

namespace RoughHeston

theorem lintegral_weighted_drift_power_le
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {μ : Measure Ω} {ν : Measure S} [SFinite μ] [SFinite ν]
    {F : S → Ω → ℝ} {w : S → ℝ} (hw : Measurable w) (hwi : Integrable w ν)
    (hF : Measurable (Function.uncurry F))
    (hFi : ∀ᵐ ω ∂μ, Integrable (fun r => w r*F r ω) ν)
    (p : ℕ) (hp : 1 ≤ p) {C : ℝ≥0∞}
    (hP : ∀ᵐ r ∂ν, (∫⁻ ω, ‖F r ω‖ₑ ^ p ∂μ) ≤ C) :
    (∫⁻ ω, ‖∫ r, w r*F r ω ∂ν‖ₑ^p ∂μ) ≤
      ENNReal.ofReal (∫ r, ‖w r‖ ∂ν)^p*C := by
  let a (r : S) := ENNReal.ofReal ‖w r‖
  let V (r : S) (ω : Ω) := ‖F r ω‖ₑ
  have ha : Measurable a := hw.norm.ennreal_ofReal
  have hV : Measurable (Function.uncurry V) := hF.enorm
  have he (ω : Ω) (hi : Integrable (fun r => w r*F r ω) ν) :
      ‖∫ r, w r*F r ω ∂ν‖ₑ ≤ ∫⁻ r, a r*V r ω ∂ν := by
    rw [← ofReal_norm]
    apply (ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm _)).trans
    rw [ofReal_integral_eq_lintegral_ofReal hi.norm (Eventually.of_forall fun _ => norm_nonneg _)]
    apply le_of_eq
    apply lintegral_congr
    intro r
    rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
    simp only [a, V, ofReal_norm]
  have hh := weighted_kernel_moment_time_profile_of_one_le (m := (p:ℝ))
    (by exact_mod_cast hp) ha hV (c := fun _ => C)
    (by simpa only [V, ENNReal.rpow_natCast] using hP)
  let E := ∫⁻ r, a r ∂ν
  have hEp : E ^ (↑p-1 : ℝ)*E = E^p := by
    calc
      _ = E ^ (↑p-1 : ℝ)*E^(1:ℝ) := congrArg (fun z => E ^ (↑p-1 : ℝ)*z) (ENNReal.rpow_one E).symm
      _ = _ := by rw [← ENNReal.rpow_add_of_nonneg (↑p-1) 1
          (sub_nonneg.mpr (by exact_mod_cast hp)) zero_le_one, sub_add_cancel, ENNReal.rpow_natCast]
  have hPower : E^(↑p-1 : ℝ)*(∫⁻ r, a r*C ∂ν) = E^p*C := by
    rw [lintegral_mul_const C ha]
    change E^(↑p-1 : ℝ)*(E*C) = _
    rw [← mul_assoc,hEp]
  apply (lintegral_mono_ae (hFi.mono fun ω hω => pow_le_pow_left' (he ω hω) p)).trans
  rw [ofReal_integral_eq_lintegral_ofReal hwi.norm (Eventually.of_forall fun _ => norm_nonneg _)]
  change _ ≤ E^p*C
  simp only [ENNReal.rpow_natCast] at hh
  change _ ≤ E^(↑p-1 : ℝ)*(∫⁻ r, a r*C ∂ν) at hh
  rw [hPower] at hh
  exact hh

#print axioms RoughHeston.lintegral_weighted_drift_power_le

end RoughHeston
