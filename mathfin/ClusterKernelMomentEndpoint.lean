import ClusterKernelMoment

open MeasureTheory
open scoped ENNReal

namespace RoughHeston

/-- Time-profile estimate including the first-moment endpoint used at the
base of the cluster moment induction. -/
theorem weighted_kernel_moment_time_profile_of_one_le
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {ν : Measure S} {μ : Measure Ω} [SFinite ν] [SFinite μ]
    {w c : S → ℝ≥0∞} {V : S → Ω → ℝ≥0∞} {m : ℝ} (hm : 1 ≤ m)
    (hw : Measurable w) (hV : Measurable (Function.uncurry V))
    (hc : ∀ᵐ s ∂ν, (∫⁻ ω, V s ω ^ m ∂μ) ≤ c s) :
    (∫⁻ ω, (∫⁻ s,w s * V s ω ∂ν)^m ∂μ) ≤
      (∫⁻ s,w s ∂ν)^(m-1) * (∫⁻ s,w s*c s ∂ν) := by
  rcases eq_or_lt_of_le hm with he | hgt
  · subst m
    simp only [ENNReal.rpow_one, sub_self, ENNReal.rpow_zero, one_mul] at hc ⊢
    let f (s : S) (ω : Ω) := w s * V s ω
    have hf : Measurable (Function.uncurry f) := (hw.comp measurable_fst).mul hV
    change (∫⁻ ω, ∫⁻ s, f s ω ∂ν ∂μ) ≤ _
    rw [← lintegral_lintegral_swap hf.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [hc] with s hs
    have hv : Measurable (V s) := hV.comp (measurable_const.prodMk measurable_id)
    rw [show (∫⁻ ω, f s ω ∂μ) = w s*(∫⁻ ω,V s ω ∂μ) from lintegral_const_mul _ hv]
    gcongr
  · exact weighted_kernel_moment_time_profile hgt hw hV hc

#print axioms weighted_kernel_moment_time_profile_of_one_le

end RoughHeston
