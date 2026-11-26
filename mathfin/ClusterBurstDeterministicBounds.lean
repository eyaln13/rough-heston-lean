import RectangularPulseMeasure
import FractionalKernelIncrements

open MeasureTheory Set Filter
open scoped ENNReal Interval

namespace RoughHeston
namespace GirsanovPort

private theorem fractionalK_antitone_positive {α u v : ℝ} (hα : 0 < α) (hα' : α ≤ 1)
    (hu : 0 < u) (huv : u ≤ v) : fractionalK α v ≤ fractionalK α u := by
  rw [fractionalK, fractionalK, ite_eq_right (not_le_of_gt (hu.trans_le huv)), ite_eq_right (not_le_of_gt hu)]
  apply div_le_div_of_nonneg_right _ (Real.Gamma_pos_of_pos hα).le
  exact Real.rpow_le_rpow_of_nonpos hu huv (sub_nonpos.mpr hα')

private theorem fractionalK_positive {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    0 < fractionalK α s := by
  rw [fractionalK, ite_eq_right (not_le_of_gt hs)]
  exact div_pos (Real.rpow_pos_of_pos hs _) (Real.Gamma_pos_of_pos hα)

/-- The resolvent pulse mean has a uniform lower bound throughout the
middle quarter of the observation interval. -/
theorem pulse_mean_middle_lower {α ε d r s : ℝ} {R : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : 0 < ε) (hd : 0 < d) (hdr : d ≤ r / 8)
    (hs : s ∈ Icc (r / 4) (r / 2)) (hR : Measurable R)
    (hComp : ∀ u ∈ Ioc (0 : ℝ) r, fractionalK α u / 2 ≤ R u ∧ R u ≤ 2 * fractionalK α u) :
    ε * (fractionalK α r / 2) ≤ volterraConvolution R (rectangularPulseRate ε d) s := by
  have hds : 2 * d ≤ s := by linarith [hs.1]
  have hs₀ : 0 < s / 2 := by linarith
  let ν := rectangularPulseMeasure ε d s
  have : IsFiniteMeasure ν := rectangularPulseMeasure_isFiniteMeasure ε d s
  obtain ⟨hmass, hage⟩ := rectangularPulseMeasure_postpulse hε.le hd hds
  have hBounds : ∀ᵐ v ∂ν, fractionalK α r / 2 ≤ R (s-v) ∧
      R (s-v) ≤ 2 * fractionalK α (s/2) := by
    filter_upwards [hage] with v hv
    have hu : 0 < s-v := hs₀.trans_le hv.1
    have hur : s-v ≤ r := hv.2.trans (by linarith [hs.2, hd, hdr])
    have h := hComp _ ⟨hu, hur⟩
    exact ⟨(div_le_div_of_nonneg_right (fractionalK_antitone_positive hα hα' hu hur)
        (by norm_num : (0 : ℝ) ≤ 2)).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_left (fractionalK_antitone_positive hα hα' hs₀ hv.1) (by norm_num))⟩
  have hr₀ : 0 < r := by linarith
  have hLower : 0 ≤ fractionalK α r / 2 := div_nonneg (fractionalK_positive hα hr₀).le (by norm_num)
  have hI : Integrable (fun v => R (s-v)) ν := by
    refine (integrable_const (2 * fractionalK α (s / 2))).mono'
      (hR.comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
    exact hBounds.mono fun v hv => by
      rw [Real.norm_of_nonneg (hLower.trans hv.1)]
      exact hv.2
  rw [← rectangularPulseMeasure_integral_eq_convolution hε.le hd]
  have h := integral_mono_ae (integrable_const (fractionalK α r / 2)) hI (hBounds.mono fun _ hv => hv.1)
  rw [integral_const, smul_eq_mul, hmass] at h
  exact h

/-- The covariance integrand over the middle quarter yields the burst
mean lower bound of order `ε * r^(2*α-1)`. -/
theorem pulse_covariance_middle_lower {α ε d r : ℝ} {R m : ℝ → ℝ}
    (hα : 0 < α) (hα' : α ≤ 1) (hε : 0 < ε) (hd : 0 < d) (hdr : d ≤ r / 8)
    (hR : Measurable R)
    (hComp : ∀ u ∈ Ioc (0 : ℝ) r, fractionalK α u / 2 ≤ R u ∧ R u ≤ 2 * fractionalK α u)
    (hm : ∀ s ∈ Ioc (0 : ℝ) r, 0 ≤ m s)
    (hMean : ∀ s ∈ Icc (r / 4) (r / 2), m s = volterraConvolution R (rectangularPulseRate ε d) s)
    (hInt : IntegrableOn (fun s => R (r-s) * m s) (Ioc (0 : ℝ) r)) :
    (ε / (16 * (Real.Gamma α) ^ 2)) * r ^ (2 * α - 1) ≤
      ∫ s in Ioc (0 : ℝ) r, R (r-s) * m s := by
  have hr : 0 < r := by linarith
  let k := fractionalK α r / 2
  let B := Ioc (r/4) (r/2)
  have hk : 0 ≤ k := div_nonneg (fractionalK_positive hα hr).le (by norm_num)
  have hB : B ⊆ Ioc (0 : ℝ) r :=
    Ioc_subset_Ioc (by positivity) (by linarith)
  have hLower (s : ℝ) (hs : s ∈ B) : ε * k ^ 2 ≤ R (r-s) * m s := by
    have hsB : s ∈ Icc (r/4) (r/2) := Ioc_subset_Icc_self hs
    have hM := pulse_mean_middle_lower hα hα' hε hd hdr hsB hR hComp
    rw [← hMean _ hsB] at hM
    have hRlower : k ≤ R (r-s) := by
      have h₁ : 0 < r-s := by linarith [hs.2]
      have h₂ : r-s ≤ r := by linarith [hs.1]
      exact (div_le_div_of_nonneg_right (fractionalK_antitone_positive hα hα' h₁ h₂)
        (by norm_num : (0 : ℝ) ≤ 2)).trans (hComp _ ⟨h₁, h₂⟩).1
    have hM₀ := (mul_nonneg hε.le hk).trans hM
    calc
      ε * k ^ 2 = k * (ε * k) := by ring
      _ ≤ R (r-s) * m s := mul_le_mul hRlower hM (mul_nonneg hε.le hk) (hk.trans hRlower)
  have hI : IntegrableOn (fun s => R (r-s) * m s) B := hInt.mono_set hB
  have hBfinite : volume B ≠ ∞ := by
    dsimp [B]
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hLocal : (∫ s in B, ε * k ^ 2) ≤ ∫ s in B, R (r-s) * m s :=
    setIntegral_mono_on (integrableOn_const hBfinite) hI measurableSet_Ioc hLower
  have hNonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) r)] fun s => R (r-s) * m s := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae (volume.ae_ne r)] with s hs hne
    have hs' : s < r := lt_of_le_of_ne hs.2 hne
    have hu : 0 < r - s := sub_pos.mpr hs'
    have h₂ : r-s ≤ r := sub_le_self _ hs.1.le
    have hR₀ : 0 ≤ R (r-s) :=
      (div_nonneg (fractionalK_positive hα hu).le (by norm_num)).trans (hComp _ ⟨hu,h₂⟩).1
    exact mul_nonneg hR₀ (hm _ hs)
  have hb : (∫ s in B, R (r-s) * m s) ≤ ∫ s in Ioc (0 : ℝ) r, R (r-s) * m s :=
    setIntegral_mono_set hInt hNonneg (ae_of_all _ hB)
  have he : (∫ s in B, ε * k ^ 2) = (ε / (16 * (Real.Gamma α) ^ 2)) * r ^ (2 * α - 1) := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, show B = Ioc (r/4) (r/2) from rfl,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith : 0 ≤ r/2-r/4)]
    dsimp [k]
    have hpow : r ^ (2 * α - 1) = (r ^ (α - 1)) ^ 2 * r := by
      rw [show (2 * α - 1 : ℝ) = (α - 1) + (α - 1) + 1 by ring,
        Real.rpow_add hr, Real.rpow_add hr, Real.rpow_one, pow_two]
    rw [fractionalK, ite_eq_right (not_le_of_gt hr), div_pow, div_pow, hpow]
    ring
  rw [he] at hLocal
  exact hLocal.trans hb

/-- A fractional upper bound on the pulse mean controls the expected
accumulated bracket on the whole observation interval. -/
theorem pulse_mean_integral_upper {α ε r A : ℝ} {m : ℝ → ℝ}
    (hα : 0 < α) (hr : 0 ≤ r)
    (hInt : IntegrableOn m (Ioc (0 : ℝ) r))
    (hm : ∀ s ∈ Ioc (0 : ℝ) r, m s ≤ A * ε * fractionalK α s) :
    (∫ s in Ioc (0 : ℝ) r, m s) ≤ (A * ε) * (r ^ α / (Real.Gamma α * α)) := by
  have hK := fractionalK_integrableOn_Ioc hα r
  refine (setIntegral_mono_on hInt (hK.const_mul (A * ε)) measurableSet_Ioc hm).trans_eq ?_
  rw [integral_const_mul]
  congr 1
  have hK_eq : fractionalK α = hestonKernel α := by
    funext s
    by_cases hs : 0 < s <;> simp [fractionalK, hestonKernel, hs, le_of_not_gt]
  rw [hK_eq, ← intervalIntegral.integral_of_le hr]
  exact hestonKernel_integral hα hr

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.pulse_mean_middle_lower
#print axioms RoughHeston.GirsanovPort.pulse_covariance_middle_lower
#print axioms RoughHeston.GirsanovPort.pulse_mean_integral_upper
