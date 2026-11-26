import EntropyCompensatorIdentity
import EntropyFatouEnergy
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Interval Topology

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}
  {Z C : ℕ → ℝ≥0 → Ω → ℝ} {d : ℕ → ℝ → Ω → ℝ}

/-- Localized martingale entropy estimates with a uniform terminal
second-moment bound yield finite expected unregularized bracket energy. -/
theorem integrable_bracket_ratio_of_localized_martingales
    (hZ : ∀ n, Martingale (Z n) F μ) (hC : ∀ n, Martingale (fun t => Z n t * Z n t - C n t) F μ)
    (hCmono : ∀ n s t, s ≤ t → C n s ≤ᵐ[μ] C n t)
    (hBound : ∀ n, ∃ K : ℝ, ∀ t, ∀ᵐ ω ∂μ, ‖Z n t ω‖ ≤ K)
    (hNonneg : ∀ n t, ∀ᵐ ω ∂μ, 0 ≤ Z n t ω)
    (hcts : ∀ n, ∀ᵐ ω ∂μ, ContinuousOn (fun t => Z n t ω) (Icc 0 H))
    (hDensity : ∀ n t, t ≤ H → C n t =ᵐ[μ] fun ω => ∫ r in (0 : ℝ)..(t : ℝ), d n r ω)
    (hZmeas : ∀ n, Measurable (Function.uncurry (Z n)))
    (hdMeas : ∀ n, Measurable (Function.uncurry (d n)))
    (hdInt : ∀ n, Integrable (Function.uncurry (d n)) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ))
    (hdNN : ∀ n, 0 ≤ᵐ[(volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ] Function.uncurry (d n))
    {M : ℝ}
    (hMoment : ∀ n, (∫ ω, Z n H ω ^ 2 ∂μ) + (∫ ω, Z n 0 ω ^ 2 ∂μ) ≤ M)
    {z d₀ : ℝ × Ω → ℝ} (hz : Measurable z) (hd₀ : Measurable d₀)
    (hzPos : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ, 0 < z p)
    (hd₀NN : 0 ≤ᵐ[(volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ] d₀)
    (hLimit : ∀ᵐ p ∂(volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ,
      ∀ᶠ n in atTop, Z n p.1.toNNReal p.2 = z p ∧ d n p.1 p.2 = d₀ p) :
    Integrable (fun p => d₀ p / z p) ((volume.restrict (Ioc (0 : ℝ) (H : ℝ))).prod μ) := by
  let θ := volume.restrict (Ioc (0 : ℝ) (H : ℝ))
  let ρ := θ.prod μ
  let weight (n : ℕ) (p : ℝ × Ω) := extendedEntropySecond (entropyRegularization n) (Z n p.1.toNNReal p.2)
  let v (n : ℕ) (p : ℝ × Ω) := weight n p * d n p.1 p.2
  have hV (n : ℕ) : Integrable (v n) ρ := by
    let η := entropyRegularization n
    have hη := entropyRegularization_pos n
    have hm : Measurable (fun p : ℝ × Ω => Z n p.1.toNNReal p.2) :=
      (hZmeas n).comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd)
    have hw : Measurable (weight n) := (extendedEntropySecond_continuous hη).measurable.comp hm
    refine ((hdInt n).abs.const_mul η⁻¹).mono' (hw.mul (hdMeas n)).aestronglyMeasurable ?_
    exact ae_of_all _ fun p => by
      have hx : 0 ≤ max (Z n p.1.toNNReal p.2) 0 := le_max_right _ _
      have hpy : 0 < max (Z n p.1.toNNReal p.2) 0 + η := add_pos_of_nonneg_of_pos hx hη
      have hle := inv_anti₀ hη (le_add_of_nonneg_left hx)
      change ‖(max (Z n p.1.toNNReal p.2) 0 + η)⁻¹ * d n p.1 p.2‖ ≤ η⁻¹ * |d n p.1 p.2|
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr hpy.le)]
      exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  have hBudget (n : ℕ) : (∫ p, v n p ∂ρ) ≤ 2 * (2 * M + 6 * μ.real univ) := by
    obtain ⟨K, hK⟩ := hBound n
    let η := entropyRegularization n
    have hη := entropyRegularization_pos n
    have hη₁ := entropyRegularization_le_one n
    have hH : (0 : ℝ) ≤ (H : ℝ) := H.2
    have hIntPath : ∀ᵐ ω ∂μ, IntervalIntegrable (fun r => d n r ω) volume 0 (H : ℝ) :=
      (hdInt n).prod_left_ae.mono fun ω hw =>
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hH).2 hw
    have hMass : Integrable (fun ω => ∫ r in (0 : ℝ)..(H : ℝ), |d n r ω|) μ := by
      simp only [intervalIntegral.integral_of_le hH]
      exact (hdInt n).abs.integral_prod_right
    have hId := boundedMartingale_regularizedEntropy_identity (hZ n) (hC n) (hCmono n) hK
      (hNonneg n) (hcts n) (hDensity n) hIntPath hMass hη
    rw [show (∫ p, v n p ∂ρ) = ∫ ω, (∫ r in (0 : ℝ)..(H : ℝ), v n (r, ω)) ∂μ from by
      simp only [intervalIntegral.integral_of_le hH]
      exact integral_prod_symm (v n) (hV n)]
    have hbnd (t : ℝ≥0) :
        (∫ ω, |regularizedEntropy η (Z n t ω)| ∂μ) ≤
          2 * (∫ ω, Z n t ω ^ 2 ∂μ) + 3 * μ.real univ := by
      have hL₂ : MemLp (Z n t) 2 μ := MemLp.of_bound
        ((((hZ n).stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable) K (hK t)
      have hEnt : Integrable (fun ω => regularizedEntropy η (Z n t ω)) μ :=
        integrable_mulLog_of_nonnegative_L2 (hL₂.add (memLp_const η))
          ((hNonneg n t).mono fun ω hw => add_nonneg hw hη.le)
      have hi₂ : Integrable (fun ω => 2 * Z n t ω ^ 2) μ := hL₂.integrable_sq.const_mul 2
      have h3 : Integrable (fun _ : Ω => (3 : ℝ)) μ := integrable_const _
      have h := integral_mono_ae hEnt.abs (hi₂.add h3)
        ((hNonneg n t).mono fun ω hw => abs_regularizedEntropy_le hw hη hη₁)
      change (∫ ω, |regularizedEntropy η (Z n t ω)| ∂μ) ≤ ∫ ω, 2 * Z n t ω ^ 2 + 3 ∂μ at h
      rw [integral_add hi₂ h3, integral_const_mul, integral_const, smul_eq_mul, mul_comm (μ.real univ)] at h
      exact h
    have hEnt₁ (t : ℝ≥0) : Integrable (fun ω => regularizedEntropy η (Z n t ω)) μ := by
      have hL₂ : MemLp (Z n t) 2 μ := MemLp.of_bound
        ((((hZ n).stronglyMeasurable t).mono (F.le t)).aestronglyMeasurable) K (hK t)
      exact integrable_mulLog_of_nonnegative_L2 (hL₂.add (memLp_const η))
        ((hNonneg n t).mono fun ω hw => add_nonneg hw hη.le)
    have hA (t : ℝ≥0) : |∫ ω, regularizedEntropy η (Z n t ω) ∂μ| ≤
        2 * (∫ ω, Z n t ω ^ 2 ∂μ) + 3 * μ.real univ :=
      abs_integral_le_integral_abs.trans (hbnd t)
    rw [integral_sub (hEnt₁ H) (hEnt₁ 0)] at hId
    change (∫ ω, regularizedEntropy η (Z n H ω) ∂μ) -
        (∫ ω, regularizedEntropy η (Z n 0 ω) ∂μ) =
      (1 / 2 : ℝ) * ∫ ω, (∫ r in (0 : ℝ)..(H : ℝ), v n (r, ω)) ∂μ at hId
    have hEnd := (le_abs_self (∫ ω, regularizedEntropy η (Z n H ω) ∂μ)).trans (hA H)
    have h0 := (neg_le_abs (∫ ω, regularizedEntropy η (Z n 0 ω) ∂μ)).trans (hA 0)
    linarith [hMoment n]
  exact integrable_bracket_ratio_of_uniform_regularizations hz hd₀ hzPos hd₀NN hLimit hV hdNN hBudget

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.integrable_bracket_ratio_of_localized_martingales
