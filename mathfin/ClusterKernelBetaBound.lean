import JointTimeEnergyProfile
import ClusterMomentInduction

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

/-- A physical-time kernel bound may be imposed off both endpoints.
It supplies integrability and the exact beta-integral bound. -/
theorem heston_time_integral_beta_bound {T : ℝ≥0} (hT : 0 < T)
    {a b C : ℝ} (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    {g : ℝ≥0 → ℝ} (hg : Measurable g)
    (hdom : ∀ t : ℝ≥0, 0 < t → t < T →
      0 ≤ g t ∧ g t ≤ C*((t:ℝ)^(a-1)*((T:ℝ)-(t:ℝ))^(b-1))) :
    Integrable g (hestonTimeMeasure T) ∧
    (∫ t, g t ∂hestonTimeMeasure T) ≤
      C*((T:ℝ)^(a+b-1)*(Real.Gamma a*Real.Gamma b/Real.Gamma (a+b))) := by
  let ν := volume.restrict (Ioc (0:ℝ) (T:ℝ))
  let f (t : ℝ) := t^(a-1)*((T:ℝ)-t)^(b-1)
  have hT' : 0 < (T:ℝ) := by exact_mod_cast hT
  obtain ⟨hfi,hf⟩ := real_beta_weight_scaled ha hb hT'
  have hcomp : ∀ᵐ t ∂ν, 0 ≤ g t.toNNReal ∧ g t.toNNReal ≤ C*f t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (T:ℝ))] with t ht hne
    have ht' : t.toNNReal < T := by
      change (t.toNNReal:ℝ) < (T:ℝ)
      rw [Real.coe_toNNReal _ ht.1.le]
      exact lt_of_le_of_ne ht.2 hne
    simpa only [f, Real.coe_toNNReal t ht.1.le] using
      hdom t.toNNReal (Real.toNNReal_pos.mpr ht.1) ht'
  have hm := hg.comp continuous_real_toNNReal.measurable
  have hi : Integrable (fun t : ℝ => g t.toNNReal) ν := by
    apply (hfi.const_mul C).mono' hm.aestronglyMeasurable
    filter_upwards [hcomp] with t h
    change ‖g t.toNNReal‖ ≤ C*f t
    rw [Real.norm_of_nonneg h.1]; exact h.2
  have he := integral_mono_ae hi (hfi.const_mul C) (hcomp.mono fun _ h => h.2)
  rw [integral_const_mul, hf] at he
  unfold hestonTimeMeasure
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  refine ⟨(integrable_map_measure hg.aestronglyMeasurable
    continuous_real_toNNReal.measurable.aemeasurable).2 hi,?_⟩
  rw [integral_map continuous_real_toNNReal.measurable.aemeasurable hg.aestronglyMeasurable]
  exact he

/-- The squared resolvent row is bounded uniformly by the fractional
power used in the moment recursion. -/
theorem fractional_square_noise_weight {α σ x : ℝ} (hα : 0 < α)
    (hx : 0 < x) {y : ℝ} (hy : |y| ≤ 2*fractionalK α x) :
    (σ*y)^2 ≤ (2*|σ|/Real.Gamma α)^2*x^((2*α-1)-1) := by
  have hg := Real.Gamma_pos_of_pos hα
  rw [fractionalK,ite_eq_right (not_le.mpr hx)] at hy
  have hz := mul_le_mul_of_nonneg_left hy (abs_nonneg σ)
  have hpow := pow_le_pow_left₀ (mul_nonneg (abs_nonneg σ) (abs_nonneg y)) hz 2
  have hex : x^((2*α-1)-1)=(x^(α-1))^2 := by
    rw [← Real.rpow_mul_natCast hx.le]
    congr 1; ring
  rw [hex]
  rw [mul_pow, sq_abs, sq_abs] at hpow
  convert hpow using 1 <;> ring

#print axioms heston_time_integral_beta_bound
#print axioms fractional_square_noise_weight

end RoughHeston
