import EntropySmoothExtension
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter
open scoped ENNReal Topology

namespace RoughHeston
namespace GirsanovPort

variable {A : Type*} [MeasurableSpace A] {ρ : Measure A}

noncomputable def entropyRegularization (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem entropyRegularization_pos (n : ℕ) : 0 < entropyRegularization n := by
  unfold entropyRegularization
  positivity

theorem entropyRegularization_le_one (n : ℕ) : entropyRegularization n ≤ 1 := by
  rw [entropyRegularization, inv_le_one₀ (by positivity : 0 < (n : ℝ) + 1)]
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem tendsto_entropyRegularization : Tendsto entropyRegularization atTop (𝓝 0) := by
  change Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one, Function.comp_def] using
    (tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)

theorem abs_regularizedEntropy_le {x η : ℝ} (hx : 0 ≤ x) (hη : 0 < η) (hη₁ : η ≤ 1) :
    |regularizedEntropy η x| ≤ 2 * x ^ 2 + 3 := by
  have he := abs_mul_log_le_sq_add_one (show 0 ≤ x + η by positivity)
  dsimp only [regularizedEntropy]
  have hs : η ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hη.le hη₁ 2
  exact he.trans (by nlinarith [sq_nonneg (x - η)])

/-- Uniform regularized bracket budgets imply integrability of the ratio.
The pointwise limit may use a different bounded localization at each
regularization scale. -/
theorem integrable_bracket_ratio_of_uniform_regularizations
    {z d : A → ℝ} {zn dn : ℕ → A → ℝ}
    (hz : Measurable z) (hd : Measurable d)
    (hzPos : ∀ᵐ a ∂ρ, 0 < z a) (hdNN : ∀ᵐ a ∂ρ, 0 ≤ d a)
    (hLimit : ∀ᵐ a ∂ρ, ∀ᶠ n in atTop, zn n a = z a ∧ dn n a = d a)
    {K : ℝ} (hInt : ∀ n, Integrable (fun a => extendedEntropySecond (entropyRegularization n) (zn n a) * dn n a) ρ)
    (hDn : ∀ n, ∀ᵐ a ∂ρ, 0 ≤ dn n a)
    (hBudget : ∀ n, (∫ a, extendedEntropySecond (entropyRegularization n) (zn n a) * dn n a ∂ρ) ≤ K) :
    Integrable (fun a => d a / z a) ρ := by
  let f (n : ℕ) (a : A) := extendedEntropySecond (entropyRegularization n) (zn n a) * dn n a
  have hfNN (n : ℕ) : 0 ≤ᵐ[ρ] f n := by
    filter_upwards [hDn n] with a ha
    exact mul_nonneg (inv_nonneg.mpr (le_trans (le_max_right _ _) (le_add_of_nonneg_right (entropyRegularization_pos n).le))) ha
  have hBound (n : ℕ) : (∫⁻ a, ENNReal.ofReal (f n a) ∂ρ) ≤ ENNReal.ofReal K := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hInt n) (hfNN n)]
    exact ENNReal.ofReal_le_ofReal (hBudget n)
  have hConv : ∀ᵐ a ∂ρ, Tendsto (fun n => ENNReal.ofReal (f n a)) atTop
      (𝓝 (ENNReal.ofReal (d a / z a))) := by
    filter_upwards [hzPos, hLimit] with a ha hloc
    have hzT : Tendsto (fun n => z a + entropyRegularization n) atTop (𝓝 (z a)) := by
      simpa only [add_zero] using tendsto_entropyRegularization.const_add (z a)
    have hr : Tendsto (fun n => d a / (z a + entropyRegularization n)) atTop (𝓝 (d a / z a)) :=
      tendsto_const_nhds.div hzT ha.ne'
    apply (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hr).congr'
    filter_upwards [hloc] with n hn
    dsimp [f, extendedEntropySecond]
    rw [hn.1, hn.2, max_eq_left ha.le, div_eq_mul_inv, mul_comm]
  have hFatou : (∫⁻ a, ENNReal.ofReal (d a / z a) ∂ρ) ≤ ENNReal.ofReal K := by
    have he : (fun a => ENNReal.ofReal (d a / z a)) =ᵐ[ρ]
        fun a => atTop.liminf (fun n => ENNReal.ofReal (f n a)) :=
      hConv.mono fun a h => h.liminf_eq.symm
    rw [lintegral_congr_ae he]
    exact (lintegral_liminf_le' (fun n => (hInt n).aemeasurable.ennreal_ofReal)).trans
      (Filter.liminf_le_of_frequently_le (Frequently.of_forall hBound))
  refine ⟨(hd.div hz).aestronglyMeasurable, ?_⟩
  change (∫⁻ a, ‖d a / z a‖ₑ ∂ρ) < ∞
  have he : (fun a => ‖d a / z a‖ₑ) =ᵐ[ρ] fun a => ENNReal.ofReal (d a / z a) := by
    filter_upwards [hzPos, hdNN] with a hza hda
    exact Real.enorm_eq_ofReal (div_nonneg hda hza.le)
  rw [lintegral_congr_ae he]
  exact hFatou.trans_lt ENNReal.ofReal_lt_top

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.integrable_bracket_ratio_of_uniform_regularizations
