import TiltingItoPairing
import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The event form of Pinsker's inequality in the direction from the original
law to a law with exponential density. The proof tests the log-density against
a centered event indicator and uses Hoeffding's lemma under the tilted law. -/
theorem event_sq_le_log_density_cost {l : Ω → ℝ} (hl : Integrable l μ)
    (R : Measure Ω) [IsProbabilityMeasure R]
    (hR : R = μ.withDensity (fun ω => ENNReal.ofReal (Real.exp (l ω))))
    {A : Set Ω} (hA : MeasurableSet A) :
    2 * (μ.real A - R.real A)^2 ≤ -(∫ ω, l ω ∂μ) := by
  let f := A.indicator (fun _ => (1 : ℝ))
  have hf : Measurable f := measurable_const.indicator hA
  have hfB (ω : Ω) : f ω ∈ Icc (0 : ℝ) 1 := by
    by_cases h : ω ∈ A <;> simp [f, h]
  have hm (ν : Measure Ω) : (∫ ω, f ω ∂ν) = ν.real A := by
    rw [show (∫ ω, f ω ∂ν) = ∫ _ : Ω in A, (1 : ℝ) ∂ν from integral_indicator hA]
    exact setIntegral_one_eq_measureReal
  let d := μ.real A - R.real A
  let t := 4 * d
  let X := fun ω => f ω - R.real A
  have hX : HasSubgaussianMGF X ((‖(1 : ℝ) - 0‖₊ / 2)^2) R := by
    simpa only [X, hm] using hasSubgaussianMGF_of_mem_Icc (μ := R)
      hf.aemeasurable (ae_of_all R hfB)
  have hmg : (∫ ω, Real.exp (t * X ω) ∂R) ≤ Real.exp (t^2 / 8) := by
    convert hX.mgf_le t using 2
    · rfl
    · norm_num [NNReal.coe_div, Real.norm_eq_abs]
      ring
  let c := t^2 / 8
  let W := fun ω => Real.exp (t * X ω) * Real.exp (-c)
  have hWI : Integrable W R := (hX.integrable_exp_mul t).mul_const _
  have hW : (∫ ω, W ω ∂R) ≤ 1 := by
    rw [show (∫ ω, W ω ∂R) = (∫ ω, Real.exp (t * X ω) ∂R) * Real.exp (-c) from
      integral_mul_const _ _]
    calc
      _ ≤ Real.exp c * Real.exp (-c) := mul_le_mul_of_nonneg_right hmg (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  let D := fun ω => ENNReal.ofReal (Real.exp (l ω))
  have hDm : AEMeasurable D μ := ENNReal.measurable_ofReal.comp_aemeasurable
    (Real.measurable_exp.comp_aemeasurable hl.aemeasurable)
  have hDt : ∀ᵐ ω ∂μ, D ω < ⊤ := ae_of_all μ (fun _ => ENNReal.ofReal_lt_top)
  have hDr (ω : Ω) : (D ω).toReal = Real.exp (l ω) := ENNReal.toReal_ofReal (Real.exp_pos _).le
  have habs : Integrable (fun ω => Real.exp (l ω) * W ω) μ := by
    rw [hR] at hWI
    simpa only [hDr, smul_eq_mul] using
      (integrable_withDensity_iff_integrable_smul₀' hDm hDt).1 hWI
  have hchange : (∫ ω, Real.exp (l ω) * W ω ∂μ) = ∫ ω, W ω ∂R := by
    rw [hR]
    symm
    simpa only [hDr, smul_eq_mul] using
      integral_withDensity_eq_integral_toReal_smul₀ hDm hDt W
  have hXμ : Integrable X μ := ((integrable_const (1 : ℝ)).indicator hA).sub (integrable_const _)
  have htest := integral_mono (hl.add ((hXμ.const_mul t).sub (integrable_const c)))
    (habs.sub (integrable_const 1)) (fun ω => by
      change l ω + (t * X ω - c) ≤ Real.exp (l ω) * (Real.exp (t * X ω) * Real.exp (-c)) - 1
      rw [← Real.exp_add, ← Real.exp_add]
      simp only [sub_eq_add_neg]
      linarith [Real.add_one_le_exp (l ω + (t * X ω + -c))]
      )
  have hXm : (∫ ω, X ω ∂μ) = d := by
    rw [show (∫ ω, X ω ∂μ) = (∫ ω, f ω ∂μ) - ∫ _ : Ω, R.real A ∂μ from
      integral_sub ((integrable_const (1 : ℝ)).indicator hA) (integrable_const _), hm]
    simp [d]
  change (∫ ω, l ω + (t * X ω - c) ∂μ) ≤ ∫ ω, Real.exp (l ω) * W ω - 1 ∂μ at htest
  rw [integral_add hl (show Integrable (fun ω => t * X ω - c) μ from (hXμ.const_mul t).sub (integrable_const c)),
    integral_sub (hXμ.const_mul t) (integrable_const c), integral_const_mul,
    hXm, integral_sub habs (integrable_const 1), hchange] at htest
  simp only [integral_const, probReal_univ, one_smul] at htest
  change 2 * d^2 ≤ _
  dsimp [c, t] at htest
  nlinarith

/-- With the negative stochastic-integral sign used for the reversed drift,
the expected negative log-density is half the expected physical energy. -/
theorem expected_neg_log_stopped_density {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hM₂ : ∀ s, MemLp (M s) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun s ω => M s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) F μ)
    (h : Lp ℝ 2 (jointPredictableMeasure F μ T)) {E : Ω → ℝ} (hEI : Integrable E μ) :
    -(∫ ω, -jointItoIntegralCLM T hM₂ h ω - E ω / 2 ∂μ) = (∫ ω, E ω ∂μ) / 2 := by
  have hI := (Lp.memLp (jointItoIntegralCLM T hM₂ h)).integrable one_le_two
  rw [integral_sub (show Integrable (fun ω => -jointItoIntegralCLM T hM₂ h ω) μ from hI.neg)
    (hEI.div_const 2), integral_neg, integral_div,
    integral_jointItoIntegralCLM_eq_zero T hM₂ hM hclock h]
  ring

/-- A cap on the accumulated squared control bounds every event probability
difference by the manuscript's square-root constant. -/
theorem event_diff_le_sqrt_stopped_energy {F : Filtration ℝ≥0 m} {M : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hM₂ : ∀ s, MemLp (M s) 2 μ) (hM : Martingale M F μ)
    (hclock : Martingale (fun s ω => M s ω ^ 2 - ((min s T : ℝ≥0) : ℝ)) F μ)
    (h : Lp ℝ 2 (jointPredictableMeasure F μ T)) {E : Ω → ℝ} (hEI : Integrable E μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcap : ∀ᵐ ω ∂μ, E ω ≤ δ)
    (R : Measure Ω) [IsProbabilityMeasure R]
    (hR : R = μ.withDensity (fun ω => ENNReal.ofReal
      (Real.exp (-jointItoIntegralCLM T hM₂ h ω - E ω / 2))))
    {A : Set Ω} (hA : MeasurableSet A) :
    |R.real A - μ.real A| ≤ Real.sqrt δ / 2 := by
  have hI := (Lp.memLp (jointItoIntegralCLM T hM₂ h)).integrable one_le_two
  have hl : Integrable (fun ω => -jointItoIntegralCLM T hM₂ h ω - E ω / 2) μ :=
    hI.neg.sub (hEI.div_const 2)
  have hp := event_sq_le_log_density_cost hl R hR hA
  rw [expected_neg_log_stopped_density T hM₂ hM hclock h hEI] at hp
  have hc := integral_mono_ae hEI (integrable_const δ) hcap
  simp only [integral_const, probReal_univ, one_smul] at hc
  rw [abs_sub_comm]
  have hsq := Real.sq_sqrt hδ
  have hz := Real.sqrt_nonneg δ
  have hs := sq_abs (μ.real A - R.real A)
  nlinarith [abs_nonneg (μ.real A - R.real A),
    sq_nonneg (2 * |μ.real A - R.real A| - Real.sqrt δ)]

end RoughHeston

#print axioms RoughHeston.event_sq_le_log_density_cost
#print axioms RoughHeston.expected_neg_log_stopped_density
#print axioms RoughHeston.event_diff_le_sqrt_stopped_energy
