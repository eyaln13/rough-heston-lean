import ClusterKernelMomentEndpoint

open MeasureTheory
open scoped ENNReal

namespace RoughHeston

/-- A finite bound for the extended moment gives membership in Lᵖ
and the same numerical bound for the ordinary expectation. -/
theorem memLp_and_integral_norm_pow_of_lintegral {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} {p : ℕ} (hp : 0 < p) (hX : Measurable X)
    {b : ℝ} (hb : 0 ≤ b)
    (h : (∫⁻ ω, ENNReal.ofReal (‖X ω‖^p) ∂μ) ≤ ENNReal.ofReal b) :
    MemLp X (p : ℝ≥0∞) μ ∧ (∫ ω, ‖X ω‖^p ∂μ) ≤ b := by
  have hn (ω : Ω) : 0 ≤ ‖X ω‖^p := pow_nonneg (norm_nonneg _) _
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top h
  have hi : Integrable (fun ω => ‖X ω‖^p) μ := by
    simpa only [ENNReal.toReal_ofReal (hn _)] using
      integrable_toReal_of_lintegral_ne_top
        ((hX.norm.pow_const p).ennreal_ofReal.aemeasurable) hfin
  have hp₀ : (p:ℝ≥0∞) ≠ 0 := by exact_mod_cast hp.ne'
  constructor
  · apply (integrable_norm_rpow_iff hX.aestronglyMeasurable hp₀ (by simp)).mp
    simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using hi
  · rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hn)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hb).mp h

/-- Convert the two deterministic factors in the weighted BDG bound to
ordinary time integrals, including the lowest order where the exponent is zero. -/
theorem weighted_time_profile_ofReal {S : Type*} [MeasurableSpace S] {ν : Measure S}
    {w c : S → ℝ} (hw : Integrable w ν) (hwc : Integrable (fun t => w t*c t) ν)
    (hn : ∀ᵐ t ∂ν, 0 ≤ w t) (hc : ∀ᵐ t ∂ν, 0 ≤ c t) {d : ℝ} (hd : 0 ≤ d) :
    (∫⁻ t, ENNReal.ofReal (w t) ∂ν)^d *
        (∫⁻ t, ENNReal.ofReal (w t)*ENNReal.ofReal (c t) ∂ν) =
      ENNReal.ofReal ((∫ t, w t ∂ν)^d * ∫ t, w t*c t ∂ν) := by
  have hnn : ∀ᵐ t ∂ν, 0 ≤ w t*c t := by
    filter_upwards [hn,hc] with t ht hc; exact mul_nonneg ht hc
  have hprod : (∫⁻ t, ENNReal.ofReal (w t)*ENNReal.ofReal (c t) ∂ν) =
      ∫⁻ t, ENNReal.ofReal (w t*c t) ∂ν := by
    apply lintegral_congr_ae
    filter_upwards [hn] with t ht
    exact (ENNReal.ofReal_mul ht).symm
  rw [hprod, ← ofReal_integral_eq_lintegral_ofReal hw hn,
    ← ofReal_integral_eq_lintegral_ofReal hwc hnn,
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg_of_ae hn) hd,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (integral_nonneg_of_ae hn) _)]

#print axioms memLp_and_integral_norm_pow_of_lintegral
#print axioms weighted_time_profile_ofReal

end RoughHeston
