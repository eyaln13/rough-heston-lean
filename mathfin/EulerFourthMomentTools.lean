import RawMartingaleIncrementFourth
import EulerCompactContainment

/-! Fourth-moment inequalities for bounded canonical martingale problems. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- Fourth-power Jensen on a finite measure space, with the total mass
explicitly included for the deterministic time integrals. -/
theorem integral_fourth_le_measure_cube_mul_pow_four
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 4 μ) :
    (∫ p, f p ∂μ)^4 ≤ (μ.real univ)^3 * (∫ p, f p^4 ∂μ) := by
  have hf₂ : MemLp f 2 μ := hf.mono_exponent (by norm_num)
  have hff : MemLp (f * f) 2 μ := (integral_sq_mul_le_of_four hf hf).1
  have h1 := integral_sq_le_measure_mul_sqIntegral hf₂
  have h2 := integral_sq_le_measure_mul_sqIntegral hff
  simp only [Pi.mul_apply, ← pow_two] at h2
  have he (p : Ω) : (f p ^ 2) ^ 2 = f p ^ 4 := by ring
  simp_rw [he] at h2
  have h3 := pow_le_pow_left₀ (sq_nonneg _) h1 2
  have h := (mul_le_mul_of_nonneg_left h2 (sq_nonneg (μ.real univ)))
  nlinarith [h3]

/-- A raw-filtration martingale with a square-integrable compensator
increment has an integrable fourth power, with the usual upper bound. -/
theorem continuous_raw_martingale_increment_fourth_integrable_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    {M A : ℝ≥0 → Ω → ℝ} (hM : Martingale M F μ)
    (hM₂ : ∀ t, MemLp (M t) 2 μ) (hMCont : ∀ ω, Continuous (fun t => M t ω))
    (hQ : Martingale (fun t => M t * M t - A t) F μ)
    (hACont : ∀ ω, Continuous (fun t => A t ω))
    (hAMono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    {s t : ℝ≥0} (hst : s ≤ t)
    (hAInt : Integrable (fun ω => (A t ω - A s ω)^2) μ) :
    Integrable (fun ω => (M t ω - M s ω)^4) μ ∧
      (∫ ω, (M t ω - M s ω)^4 ∂μ) ≤ (boundedMartingaleEvenPowerConstant 2).toReal *
        (∫ ω, (A t ω - A s ω)^2 ∂μ) := by
  let K := boundedMartingaleEvenPowerConstant 2
  let X (ω : Ω) := (M t ω - M s ω)^4
  let C (ω : Ω) := (A t ω - A s ω)^2
  have hK : K ≠ ⊤ := boundedMartingaleEvenPowerConstant_ne_top 2 le_rfl
  have hX₀ (ω : Ω) : 0 ≤ X ω := by dsimp [X]; positivity
  have hXₘ : Measurable X :=
    ((((hM.stronglyMeasurable t).mono (F.le t)).sub
      ((hM.stronglyMeasurable s).mono (F.le s))).measurable).pow_const _
  have hBDG := continuous_raw_martingale_increment_fourth_le hM hM₂ hMCont hQ hACont hAMono hst
  have hXe : (∫⁻ ω, ‖M t ω - M s ω‖ₑ ^ (4 : ℕ) ∂μ) = ∫⁻ ω, ENNReal.ofReal (X ω) ∂μ := by
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
      ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (M t ω - M s ω)^4)]
  have hCe : (∫⁻ ω, ENNReal.ofReal (A t ω - A s ω) ^ (2 : ℕ) ∂μ) =
      ENNReal.ofReal (∫ ω, C ω ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hAInt (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr_ae
    filter_upwards [hAMono] with ω hω
    rw [← ENNReal.ofReal_pow (sub_nonneg.mpr (hω hst))]
  rw [hXe, hCe] at hBDG
  have hFin : (∫⁻ ω, ENNReal.ofReal (X ω) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top) hBDG
  have hXi : Integrable X μ := by
    simpa only [ENNReal.toReal_ofReal (hX₀ _)] using
      integrable_toReal_of_lintegral_ne_top hXₘ.ennreal_ofReal.aemeasurable hFin
  refine ⟨hXi, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hXi (Eventually.of_forall hX₀)] at hBDG
  have h := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top)).2 hBDG
  have hC₀ : ∀ ω, 0 ≤ C ω := fun _ => sq_nonneg _
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (integral_nonneg hX₀),
    ENNReal.toReal_ofReal (integral_nonneg hC₀)] using h

#print axioms RoughHeston.integral_fourth_le_measure_cube_mul_pow_four
#print axioms RoughHeston.continuous_raw_martingale_increment_fourth_integrable_le

end RoughHeston
