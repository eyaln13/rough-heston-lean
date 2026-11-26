import Verification
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory Filter Set
open scoped MeasureTheory Topology ENNReal

namespace RoughHeston

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- A stopped exponential density has a square moment bounded by the
exponential of its energy cap when its doubled stochastic exponential
has expectation at most one. -/
theorem density_sq_le_exp_of_energy_cap {D D₂ E : Ω → ℝ} {δ : ℝ}
    (hD : AEStronglyMeasurable D μ) (hD₂ : Integrable D₂ μ)
    (hD₂₀ : ∀ᵐ ω ∂μ, 0 ≤ D₂ ω) (hD₂₁ : (∫ ω, D₂ ω ∂μ) ≤ 1)
    (hE : ∀ᵐ ω ∂μ, E ω ≤ δ)
    (hfactor : ∀ᵐ ω ∂μ, D ω ^ 2 = Real.exp (E ω) * D₂ ω) :
    MemLp D 2 μ ∧ (∫ ω, D ω ^ 2 ∂μ) ≤ Real.exp δ := by
  have hcap : ∀ᵐ ω ∂μ, D ω ^ 2 ≤ Real.exp δ * D₂ ω := by
    filter_upwards [hD₂₀, hE, hfactor] with ω hd he hf
    rw [hf]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr he) hd
  have hsup : Integrable (fun ω => Real.exp δ * D₂ ω) μ := hD₂.const_mul _
  have hsq : Integrable (fun ω => D ω ^ 2) μ := by
    apply hsup.mono' (hD.pow _)
    exact hcap.mono fun ω h => by
      change ‖D ω ^ 2‖ ≤ Real.exp δ * D₂ ω
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact h
  refine ⟨(memLp_two_iff_integrable_sq hD).2 hsq, ?_⟩
  calc
    _ ≤ ∫ ω, Real.exp δ * D₂ ω ∂μ := integral_mono_ae hsq hsup hcap
    _ = Real.exp δ * (∫ ω, D₂ ω ∂μ) := integral_const_mul _ _
    _ ≤ Real.exp δ := (mul_le_mul_of_nonneg_left hD₂₁ (Real.exp_pos _).le).trans_eq (mul_one _)

/-- Changing measure by a probability density with bounded squared
cost moves each event probability by at most half the square root of
the density variance. -/
theorem event_probability_diff_le_density_variance {D : Ω → ℝ}
    (hD : MemLp D 2 μ) (hD₀ : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    (hDmean : (∫ ω, D ω ∂μ) = 1) {V : ℝ}
    (hVar : (∫ ω, (D ω - 1) ^ 2 ∂μ) ≤ V)
    {A : Set Ω} (hA : MeasurableSet A) :
    |(μ.withDensity (fun ω => ENNReal.ofReal (D ω))).real A - μ.real A| ≤ Real.sqrt V / 2 := by
  let p := μ.real A
  let F : Ω → ℝ := A.indicator (fun _ => 1)
  let H (ω : Ω) := F ω - p
  let G (ω : Ω) := D ω - 1
  have hFi : MemLp F 2 μ := (memLp_const (1 : ℝ)).indicator hA.nullMeasurableSet
  have hHi : MemLp H 2 μ := hFi.sub (memLp_const p)
  have hGi : MemLp G 2 μ := hD.sub (memLp_const (1 : ℝ))
  have hFmean : (∫ ω, F ω ∂μ) = p := integral_indicator_one hA
  have hFsecond : (∫ ω, F ω ^ 2 ∂μ) = p := by
    rw [← hFmean]
    apply integral_congr_ae
    exact ae_of_all μ fun ω => by by_cases h : ω ∈ A <;> simp [F, h]
  have hGmean : (∫ ω, G ω ∂μ) = 0 := by
    rw [integral_sub (hD.integrable one_le_two) (integrable_const _), hDmean, integral_const]
    simp
  have hHsecond : (∫ ω, H ω ^ 2 ∂μ) = p - p ^ 2 := by
    change (∫ ω, (F ω - p) ^ 2 ∂μ) = _
    have hFI := (hFi.integrable one_le_two).const_mul (2 * p)
    calc
      _ = ∫ ω, F ω ^ 2 - (2 * p) * F ω + p ^ 2 ∂μ :=
        integral_congr_ae (ae_of_all μ fun _ => by ring)
      _ = (∫ ω, F ω ^ 2 - (2 * p) * F ω ∂μ) + ∫ _ : Ω, p ^ 2 ∂μ :=
        integral_add (hFi.integrable_sq.sub hFI) (integrable_const (p ^ 2))
      _ = ((∫ ω, F ω ^ 2 ∂μ) - (∫ ω, (2 * p) * F ω ∂μ)) + ∫ _ : Ω, p ^ 2 ∂μ := by
        rw [show (∫ ω, F ω ^ 2 - (2 * p) * F ω ∂μ) =
          (∫ ω, F ω ^ 2 ∂μ) - ∫ ω, (2 * p) * F ω ∂μ from integral_sub hFi.integrable_sq hFI]
      _ = _ := by
        rw [integral_const_mul, hFsecond, hFmean, integral_const]
        simp
        ring
  have hHquarter : (∫ ω, H ω ^ 2 ∂μ) ≤ 1 / 4 := by
    rw [hHsecond]
    nlinarith [sq_nonneg (p - 1 / 2)]
  have hDR : (μ.withDensity (fun ω => ENNReal.ofReal (D ω))).real A =
      ∫ ω in A, D ω ∂μ := by
    have hpos : ∀ᵐ ω ∂μ.restrict A, 0 ≤ D ω := hD₀.filter_mono (ae_mono Measure.restrict_le_self)
    rw [Measure.real, withDensity_apply _ hA,
      ← ofReal_integral_eq_lintegral_ofReal (hD.integrable one_le_two).integrableOn hpos,
      ENNReal.toReal_ofReal (integral_nonneg_of_ae hpos)]
  have hEq : (∫ ω, H ω * G ω ∂μ) =
      (μ.withDensity (fun ω => ENNReal.ofReal (D ω))).real A - p := by
    have hFG : Integrable (fun ω => F ω * G ω) μ :=
      ((hFi.mul hGi : MemLp (F * G) 1 μ).integrable le_rfl)
    have hG1 := hGi.integrable one_le_two
    calc
      _ = ∫ ω, F ω * G ω - p * G ω ∂μ := integral_congr_ae
        (ae_of_all μ fun ω => by dsimp [H]; ring)
      _ = ∫ ω, F ω * G ω ∂μ := by
        rw [integral_sub hFG (hG1.const_mul _), integral_const_mul, hGmean, mul_zero, sub_zero]
      _ = ∫ ω in A, G ω ∂μ := by
        rw [← integral_indicator hA]
        apply integral_congr_ae
        exact ae_of_all μ fun ω => by by_cases h : ω ∈ A <;> simp [F, h]
      _ = _ := by
        change (∫ ω in A, D ω - 1 ∂μ) = _
        rw [integral_sub (hD.integrable one_le_two).integrableOn (integrable_const _),
          setIntegral_const, smul_eq_mul, mul_one, hDR]
  have hpq : (2 : ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have h := integral_mul_norm_le_Lp_mul_Lq hpq
    (by simpa using hHi : MemLp H (ENNReal.ofReal 2) μ)
    (by simpa using hGi : MemLp G (ENNReal.ofReal 2) μ)
  have hnorm (x : ℝ) : ‖x‖ ^ (2 : ℝ) = x ^ 2 := by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp only [hnorm, ← Real.sqrt_eq_rpow] at h
  rw [← hEq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ ω, ‖H ω‖ * ‖G ω‖ ∂μ := by
      simpa only [norm_mul] using norm_integral_le_integral_norm (fun ω => H ω * G ω)
    _ ≤ Real.sqrt (∫ ω, H ω ^ 2 ∂μ) * Real.sqrt (∫ ω, G ω ^ 2 ∂μ) := h
    _ ≤ Real.sqrt (1 / 4) * Real.sqrt V :=
      mul_le_mul (Real.sqrt_le_sqrt hHquarter) (Real.sqrt_le_sqrt hVar) (Real.sqrt_nonneg _)
        (Real.sqrt_nonneg _)
    _ = _ := by
      have hq : Real.sqrt (1 / 4) = 1 / 2 := by
        rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [hq]
      ring

/-- The energy cap gives an event-probability difference tending to zero
at the square-root scale. -/
theorem event_probability_diff_le_stopped_density_cost {D D₂ E : Ω → ℝ} {δ : ℝ}
    (hD : AEStronglyMeasurable D μ) (hD₀ : ∀ᵐ ω ∂μ, 0 ≤ D ω)
    (hDmean : (∫ ω, D ω ∂μ) = 1)
    (hD₂ : Integrable D₂ μ) (hD₂₀ : ∀ᵐ ω ∂μ, 0 ≤ D₂ ω)
    (hD₂₁ : (∫ ω, D₂ ω ∂μ) ≤ 1) (hE : ∀ᵐ ω ∂μ, E ω ≤ δ)
    (hfactor : ∀ᵐ ω ∂μ, D ω ^ 2 = Real.exp (E ω) * D₂ ω)
    {A : Set Ω} (hA : MeasurableSet A) :
    |(μ.withDensity (fun ω => ENNReal.ofReal (D ω))).real A - μ.real A| ≤
      Real.sqrt (Real.exp δ - 1) / 2 := by
  obtain ⟨hD₂mem, hD₂bound⟩ := density_sq_le_exp_of_energy_cap hD hD₂ hD₂₀ hD₂₁ hE hfactor
  apply event_probability_diff_le_density_variance hD₂mem hD₀ hDmean _ hA
  have hi := (hD₂mem.integrable one_le_two).const_mul (2 : ℝ)
  calc
    _ = ∫ ω, D ω ^ 2 - 2 * D ω + 1 ∂μ :=
      integral_congr_ae (ae_of_all μ fun _ => by ring)
    _ = (∫ ω, D ω ^ 2 - 2 * D ω ∂μ) + ∫ _ : Ω, (1 : ℝ) ∂μ :=
      integral_add (hD₂mem.integrable_sq.sub hi) (integrable_const (1 : ℝ))
    _ = ((∫ ω, D ω ^ 2 ∂μ) - (∫ ω, 2 * D ω ∂μ)) + ∫ _ : Ω, (1 : ℝ) ∂μ := by
      rw [show (∫ ω, D ω ^ 2 - 2 * D ω ∂μ) =
        (∫ ω, D ω ^ 2 ∂μ) - ∫ ω, 2 * D ω ∂μ from integral_sub hD₂mem.integrable_sq hi]
    _ ≤ _ := by
      rw [integral_const_mul, hDmean, integral_const]
      simp
      linarith

end RoughHeston

#print axioms RoughHeston.density_sq_le_exp_of_energy_cap
#print axioms RoughHeston.event_probability_diff_le_density_variance
#print axioms RoughHeston.event_probability_diff_le_stopped_density_cost
