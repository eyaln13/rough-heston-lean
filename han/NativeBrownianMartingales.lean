import SHEStochastic.FiniteScalarIto
import FiniteHorizonLevy
import StochasticFoundation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

open SHEStochastic

variable {Ω ι : Type*} [m : MeasurableSpace Ω] [DecidableEq ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Filtration ℝ≥0 m} {H : ℝ≥0}

/-- The native coordinate law is the project's Brownian law on the
same filtration and finite horizon. -/
theorem nativeCoordinate_brownianOn (P : FiniteScalarIto.Family F μ H ι) (i : ι) :
    MathFinBridge.BrownianOn μ F H (P.W i) := by
  refine ⟨fun t => (P.adapted i t).stronglyMeasurable, ?_,
    ae_of_all _ (fun ω => (P.continuous i ω).continuousOn), ?_, ?_⟩
  · have h := BrownianCoordinates.eval_law F μ H P.W P.law i 0 zero_le
    rw [gaussianReal_zero_var] at h
    exact h.ae_eq_of_dirac
  · intro s t hst ht
    exact (BrownianCoordinates.increment_law F μ H P.W P.law i s t hst ht).map_eq
  · intro s t hst ht
    exact BrownianCoordinates.independent_increment F μ H P.W P.law i s t hst ht

private theorem nativeCoordinate_setIntegral (P : FiniteScalarIto.Family F μ H ι) (i : ι)
    (s t : ℝ≥0) (hst : s ≤ t) (ht : t ≤ H) (A : Set Ω) (hA : MeasurableSet[F s] A) :
    (∫ ω in A, P.W i s ω ∂μ) = (∫ ω in A, P.W i t ω ∂μ) ∧
      (∫ ω in A, P.W i s ω ^ 2 - (s : ℝ) ∂μ) = ∫ ω in A, P.W i t ω ^ 2 - (t : ℝ) ∂μ := by
  let d (ω : Ω) := P.W i t ω - P.W i s ω
  let a : Ω → ℝ := A.indicator (fun _ => 1)
  let x : Ω → ℝ := A.indicator (P.W i s)
  have hAμ := F.le s A hA
  have ha : Measurable[F s] a := measurable_const.indicator hA
  have hx : Measurable[F s] x := (P.adapted i s).indicator hA
  have hs₂ := BrownianCoordinates.memLp_eval F μ H P.W P.law i s (hst.trans ht) 2 (by simp)
  have ht₂ := BrownianCoordinates.memLp_eval F μ H P.W P.law i t ht 2 (by simp)
  have hd₂ := BrownianCoordinates.memLp_increment F μ H P.W P.law i s t hst ht 2 (by simp)
  have hcenter : (∫ ω in A, d ω ∂μ) = 0 := by
    rw [← integral_indicator hAμ]
    have he := BrownianCoordinates.integral_adapted_mul_increment F μ H P.W P.law i s t hst ht ha
    convert he using 1
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [a, d, hω]
  have hcross : (∫ ω in A, P.W i s ω * d ω ∂μ) = 0 := by
    rw [← integral_indicator hAμ]
    have he := BrownianCoordinates.integral_adapted_mul_increment F μ H P.W P.law i s t hst ht hx
    convert he using 1
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [x, d, hω]
  have hsecond : (∫ ω in A, d ω ^ 2 ∂μ) = μ.real A * ((t : ℝ) - (s : ℝ)) := by
    rw [← integral_indicator hAμ]
    have he := BrownianCoordinates.weighted_common_increment F μ H P.W P.law i i s t hst ht ha
    simp only [ite_true, mul_one, show (∫ ω, a ω ∂μ) = μ.real A from integral_indicator_one hAμ] at he
    convert he using 1
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [a, d, hω, pow_two]
  have hcomp : (∫ ω in A, P.W i t ω ^ 2 ∂μ) =
      (∫ ω in A, P.W i s ω ^ 2 ∂μ) + μ.real A * ((t : ℝ) - (s : ℝ)) := by
    have hcrossI : Integrable (fun ω => P.W i s ω * d ω) μ := hs₂.integrable_mul hd₂
    have hsum : Integrable (fun ω => P.W i s ω ^ 2 + 2 * (P.W i s ω * d ω)) μ :=
      hs₂.integrable_sq.add (hcrossI.const_mul 2)
    have hdI : Integrable (fun ω => d ω ^ 2) μ := hd₂.integrable_sq
    have hrewrite (ω : Ω) : P.W i t ω ^ 2 =
        (P.W i s ω ^ 2 + 2 * (P.W i s ω * d ω)) + d ω ^ 2 := by unfold d; ring
    simp_rw [hrewrite]
    rw [integral_add hsum.integrableOn hdI.integrableOn,
      integral_add hs₂.integrable_sq.integrableOn (hcrossI.const_mul 2).integrableOn,
      integral_const_mul, hcross, hsecond, mul_zero, add_zero]
  refine ⟨?_, ?_⟩
  · rw [show (∫ ω in A, d ω ∂μ) = (∫ ω in A, P.W i t ω ∂μ) - (∫ ω in A, P.W i s ω ∂μ)
      from integral_sub (ht₂.integrable one_le_two).integrableOn (hs₂.integrable one_le_two).integrableOn] at hcenter
    exact (sub_eq_zero.mp hcenter).symm
  · rw [integral_sub hs₂.integrable_sq.integrableOn (integrable_const _),
      integral_sub ht₂.integrable_sq.integrableOn (integrable_const _), setIntegral_const, setIntegral_const,
      hcomp, smul_eq_mul, smul_eq_mul]
    ring

/-- Freezing the native Brownian driver at the horizon gives the exact
square-integrable martingale and compensated clock needed by the
project's joint Itô map. -/
theorem nativeCoordinate_frozen_martingales (P : FiniteScalarIto.Family F μ H ι) (i : ι) :
    let B : ℝ≥0 → Ω → ℝ := fun t => P.W i (min t H)
    (∀ t, MemLp (B t) 2 μ) ∧ Martingale B F μ ∧
      Martingale (fun t ω => B t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ := by
  let B : ℝ≥0 → Ω → ℝ := fun t => P.W i (min t H)
  have h₂ (t : ℝ≥0) : MemLp (B t) 2 μ :=
    BrownianCoordinates.memLp_eval F μ H P.W P.law i (min t H) (min_le_right _ _) 2 (by simp)
  have hB (t : ℝ≥0) : StronglyMeasurable[F t] (B t) :=
    (P.adapted i _).stronglyMeasurable.mono (F.mono (min_le_left t H))
  refine ⟨h₂, martingale_of_past_set_integrals hB (fun t => (h₂ t).integrable one_le_two) ?_,
    martingale_of_past_set_integrals (fun t => ((hB t).pow 2).sub stronglyMeasurable_const)
      (fun t => (h₂ t).integrable_sq.sub (integrable_const _)) ?_⟩
  · intro s t hst A hA
    by_cases hs : s ≤ H
    · rw [min_eq_left hs]
      exact (nativeCoordinate_setIntegral P i s (min t H)
        (le_min hst hs) (min_le_right _ _) A hA).1
    · simp only [min_eq_right (le_of_not_ge hs), min_eq_right ((le_of_not_ge hs).trans hst)]
  · intro s t hst A hA
    change (∫ ω in A, P.W i (min s H) ω ^ 2 - ((min s H : ℝ≥0) : ℝ) ∂μ) = _
    by_cases hs : s ≤ H
    · rw [min_eq_left hs]
      exact (nativeCoordinate_setIntegral P i s (min t H)
        (le_min hst hs) (min_le_right _ _) A hA).2
    · simp only [min_eq_right (le_of_not_ge hs), min_eq_right ((le_of_not_ge hs).trans hst)]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.nativeCoordinate_brownianOn
#print axioms RoughHeston.GirsanovPort.nativeCoordinate_frozen_martingales
