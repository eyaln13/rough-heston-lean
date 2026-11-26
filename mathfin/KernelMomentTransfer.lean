import MartingalePowerMoment
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter Set
open scoped MeasureTheory ENNReal

namespace RoughHeston

variable {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
  {ν : Measure S} {μ : Measure Ω} [SFinite ν] [SFinite μ]

/-- Weighted Hölder in time and Tonelli in probability give the
power moment of a nonnegative kernel convolution. -/
theorem lintegral_weighted_kernel_moment_le {w : S → ℝ≥0∞} {V : S → Ω → ℝ≥0∞}
    {m : ℝ} (hm : 1 < m) (hw : Measurable w) (hV : Measurable (Function.uncurry V))
    {C : ℝ≥0∞} (hC : ∀ᵐ s ∂ν, (∫⁻ ω, V s ω ^ m ∂μ) ≤ C) :
    (∫⁻ ω, (∫⁻ s, w s * V s ω ∂ν) ^ m ∂μ) ≤
      (∫⁻ s, w s ∂ν) ^ m * C := by
  let A := ∫⁻ s, w s ∂ν
  let h (s : S) (ω : Ω) := w s * V s ω ^ m
  have hh : Measurable (Function.uncurry h) :=
    (hw.comp measurable_fst).mul (ENNReal.continuous_rpow_const.measurable.comp hV)
  have hVm (ω : Ω) : Measurable (fun s => V s ω) :=
    hV.comp (measurable_id.prodMk measurable_const)
  have hmean : (∫⁻ s, ∫⁻ ω, h s ω ∂μ ∂ν) ≤ ∫⁻ s, w s * C ∂ν := by
    apply lintegral_mono_ae
    filter_upwards [hC] with s hs
    have hf : Measurable (fun ω => V s ω ^ m) :=
      ENNReal.continuous_rpow_const.measurable.comp
        (hV.comp (measurable_const.prodMk measurable_id))
    rw [show (∫⁻ ω, h s ω ∂μ) = w s * ∫⁻ ω, V s ω ^ m ∂μ from
      lintegral_const_mul _ hf]
    gcongr
  have hApow : A ^ (m - 1) * A = A ^ m := by
    calc
      _ = A ^ (m - 1) * A ^ (1 : ℝ) := congrArg (fun x => A ^ (m - 1) * x) (ENNReal.rpow_one A).symm
      _ = _ := by rw [← ENNReal.rpow_add_of_nonneg (m - 1) 1 (sub_nonneg.mpr hm.le) zero_le_one,
        sub_add_cancel]
  calc
    _ ≤ ∫⁻ ω, A ^ (m - 1) * (∫⁻ s, h s ω ∂ν) ∂μ :=
      lintegral_mono fun ω => lintegral_weighted_rpow_le (μ := ν) hw (hVm ω) hm
    _ = A ^ (m - 1) * ∫⁻ ω, ∫⁻ s, h s ω ∂ν ∂μ :=
      lintegral_const_mul _ hh.lintegral_prod_left'
    _ = A ^ (m - 1) * ∫⁻ s, ∫⁻ ω, h s ω ∂μ ∂ν :=
      congrArg (fun x => A ^ (m - 1) * x) (lintegral_lintegral_swap hh.aemeasurable).symm
    _ ≤ A ^ (m - 1) * ∫⁻ s, w s * C ∂ν := by gcongr
    _ = _ := by
      rw [lintegral_mul_const _ hw]
      change A ^ (m - 1) * (A * C) = A ^ m * C
      rw [← mul_assoc, hApow]

/-- A terminal BDG estimate with the convolution's energy gives the
moment bound in terms of the deterministic squared kernel weight
and the timewise variance moments. -/
theorem kernel_noise_moment_le_of_bdg {w : S → ℝ≥0∞} {V : S → Ω → ℝ≥0∞}
    {N : Ω → ℝ} {m : ℝ} (hm : 1 < m) (hw : Measurable w)
    (hV : Measurable (Function.uncurry V)) {C D : ℝ≥0∞}
    (hC : ∀ᵐ s ∂ν, (∫⁻ ω, V s ω ^ m ∂μ) ≤ C)
    (hBDG : (∫⁻ ω, ‖N ω‖ₑ ^ (2 * m) ∂μ) ≤
      D * ∫⁻ ω, (∫⁻ s, w s * V s ω ∂ν) ^ m ∂μ) :
    (∫⁻ ω, ‖N ω‖ₑ ^ (2 * m) ∂μ) ≤ D * (∫⁻ s, w s ∂ν) ^ m * C := by
  apply hBDG.trans
  rw [mul_assoc]
  have h := lintegral_weighted_kernel_moment_le hm hw hV hC
  gcongr

end RoughHeston

#print axioms RoughHeston.lintegral_weighted_kernel_moment_le
#print axioms RoughHeston.kernel_noise_moment_le_of_bdg
