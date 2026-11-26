import MartingalePowerMoment

/-! The real square-integrable envelope associated with the continuous Doob bound. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- Convert the extended-real Doob envelope to a real random variable
with a square-integrable dominating path supremum. -/
theorem exists_continuous_martingale_real_norm_envelope_sq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {𝒢 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)} {X : ℝ≥0 → Ω → ℝ}
    (hX : Martingale X 𝒢 μ) (T : ℝ≥0)
    (hcont : ∀ᵐ ω ∂μ, ContinuousOn (fun t => X t ω) (Icc 0 T))
    (hXt : Integrable (fun ω => (X T ω)^2) μ) :
    ∃ S : Ω → ℝ, Measurable S ∧ Integrable (fun ω => (S ω)^2) μ ∧
      (∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ ≤ S ω) ∧
      (∫ ω, (S ω)^2 ∂μ) ≤ 4 * (∫ ω, (X T ω)^2 ∂μ) := by
  obtain ⟨E, hE, hDom, hBound⟩ :=
    exists_continuous_martingale_norm_envelope hX T hcont (p := 2) (by norm_num)
  have hCast : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  simp_rw [hCast, ENNReal.rpow_natCast] at hBound
  norm_num at hBound
  have hXeq : (∫⁻ ω, ‖X T ω‖ₑ ^ (2 : ℕ) ∂μ) = ENNReal.ofReal (∫ ω, (X T ω)^2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hXt (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  rw [hXeq] at hBound
  have hFin : (∫⁻ ω, E ω ^ (2 : ℕ) ∂μ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top) hBound
  have hFinAE : ∀ᵐ ω ∂μ, E ω ≠ ⊤ := by
    filter_upwards [ae_lt_top (hE.pow_const 2) hFin] with ω hw
    intro he
    simp [he] at hw
  let S (ω : Ω) := (E ω).toReal
  have hS2 : Integrable (fun ω => (S ω)^2) μ := by
    have h := integrable_toReal_of_lintegral_ne_top (hE.pow_const 2).aemeasurable hFin
    simpa only [ENNReal.toReal_pow, S] using h
  have hSdom : ∀ᵐ ω ∂μ, ∀ t ≤ T, ‖X t ω‖ ≤ S ω := by
    filter_upwards [hFinAE, hDom] with ω he hb
    intro t ht
    have h := (ENNReal.toReal_le_toReal (ne_of_lt enorm_lt_top) he).2 (hb t ht)
    simpa only [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), S] using h
  refine ⟨S, hE.ennreal_toReal, hS2, hSdom, ?_⟩
  have hSeq : ENNReal.ofReal (∫ ω, (S ω)^2 ∂μ) =
        ∫⁻ ω, E ω ^ (2 : ℕ) ∂μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hS2 (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr_ae
    filter_upwards [hFinAE] with ω he
    rw [ENNReal.ofReal_pow (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal he]
  rw [← hSeq] at hBound
  have hTr := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)).2 hBound
  simpa only [ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _),
    ENNReal.toReal_mul, ENNReal.toReal_ofNat] using hTr

#print axioms RoughHeston.exists_continuous_martingale_real_norm_envelope_sq

end RoughHeston
