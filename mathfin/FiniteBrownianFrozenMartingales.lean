import FiniteHorizonLevy
import StochasticFoundation
import Mathlib.Probability.Independence.Integration

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston
namespace GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0} {B : ℝ≥0 → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
theorem finiteBrownianOn_memLp (hB : MathFinBridge.BrownianOn μ F H B)
    (t : ℝ≥0) (ht : t ≤ H) (p : ℝ≥0∞) (hp : p ≠ ⊤) : MemLp (B t) p μ := by
  have hm (s : ℝ≥0) : Measurable (B s) := ((hB.adapted s).mono (F.le s)).measurable
  have hd : HasLaw (B t - B 0) (gaussianReal 0 (t - 0)) μ :=
    ⟨((hm t).sub (hm 0)).aemeasurable, hB.normal_increment 0 t zero_le ht⟩
  have hi : MemLp (B t - B 0) p μ := hd.memLp (memLp_id_gaussianReal' p hp)
  refine hi.ae_eq (hB.zero_at_start.mono ?_)
  intro ω hw
  change B t ω - B 0 ω = B t ω
  rw [show B 0 ω = 0 from hw, sub_zero]

omit [IsProbabilityMeasure μ] in
private theorem finiteBrownianOn_weighted_increment (hB : MathFinBridge.BrownianOn μ F H B)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ H) {φ : Ω → ℝ} (hφ : Measurable[F s] φ) :
    let d := fun ω => B t ω - B s ω
    (∫ ω, φ ω * d ω ∂μ) = 0 ∧
      (∫ ω, φ ω * (d ω) ^ 2 ∂μ) = (∫ ω, φ ω ∂μ) * ((t : ℝ) - (s : ℝ)) := by
  let d (ω : Ω) := B t ω - B s ω
  have hφm : Measurable φ := hφ.mono (F.le s) le_rfl
  have hBm (r : ℝ≥0) : Measurable (B r) := ((hB.adapted r).mono (F.le r)).measurable
  have hm : Measurable d := (hBm t).sub (hBm s)
  have hLaw : HasLaw d (gaussianReal 0 (t - s)) μ :=
    ⟨hm.aemeasurable, hB.normal_increment s t hst ht⟩
  have hIndep : IndepFun φ d μ := (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le_left (hB.independent_of_past s t hst ht).symm (Measurable.comap_le hφ))
  have h2 : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
  have hMass : (∫ ω, d ω ∂μ) = 0 := by
    simpa only [Function.comp_def, id_eq, integral_id_gaussianReal] using
      hLaw.integral_comp (f := id) measurable_id.aestronglyMeasurable
  have hSecond : (∫ ω, d ω ^ 2 ∂μ) = (t : ℝ) - (s : ℝ) := by
    have hVar := variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := t - s)
    have hx : AEMeasurable (fun x : ℝ => x) (gaussianReal 0 (t - s)) := measurable_id.aemeasurable
    rw [variance_eq_integral hx] at hVar
    simp only [integral_id_gaussianReal, sub_zero, NNReal.coe_sub hst] at hVar
    exact (hLaw.integral_comp h2.aestronglyMeasurable).trans hVar
  constructor
  · rw [hIndep.integral_fun_mul_eq_mul_integral hφm.aestronglyMeasurable hm.aestronglyMeasurable, hMass, mul_zero]
  · have h := hIndep.comp (φ := (id : ℝ → ℝ)) (ψ := fun x : ℝ => x ^ 2) measurable_id h2
    have he := h.integral_fun_mul_eq_mul_integral hφm.aestronglyMeasurable (hm.pow_const 2).aestronglyMeasurable
    simpa only [Function.comp_def, id_eq, hSecond] using he

private theorem finiteBrownianOn_setIntegral (hB : MathFinBridge.BrownianOn μ F H B)
    {s t : ℝ≥0} (hst : s ≤ t) (ht : t ≤ H) {A : Set Ω} (hA : MeasurableSet[F s] A) :
    (∫ ω in A, B s ω ∂μ) = (∫ ω in A, B t ω ∂μ) ∧
      (∫ ω in A, B s ω ^ 2 - (s : ℝ) ∂μ) = ∫ ω in A, B t ω ^ 2 - (t : ℝ) ∂μ := by
  let d (ω : Ω) := B t ω - B s ω
  let a : Ω → ℝ := A.indicator (fun _ => 1)
  let x : Ω → ℝ := A.indicator (B s)
  have hAμ := F.le s A hA
  have ha : Measurable[F s] a := measurable_const.indicator hA
  have hx : Measurable[F s] x := (hB.adapted s).measurable.indicator hA
  have hs₂ := finiteBrownianOn_memLp hB s (hst.trans ht) 2 (by simp)
  have ht₂ := finiteBrownianOn_memLp hB t ht 2 (by simp)
  have hd₂ : MemLp d 2 μ := ht₂.sub hs₂
  have hcenter : (∫ ω in A, d ω ∂μ) = 0 := by
    rw [← integral_indicator hAμ]
    convert (finiteBrownianOn_weighted_increment hB hst ht ha).1 using 2
    funext ω
    by_cases hω : ω ∈ A <;> simp [a, d, hω]
  have hcross : (∫ ω in A, B s ω * d ω ∂μ) = 0 := by
    rw [← integral_indicator hAμ]
    convert (finiteBrownianOn_weighted_increment hB hst ht hx).1 using 2
    funext ω
    by_cases hω : ω ∈ A <;> simp [x, d, hω]
  have hsecond : (∫ ω in A, d ω ^ 2 ∂μ) = μ.real A * ((t : ℝ) - (s : ℝ)) := by
    rw [← integral_indicator hAμ]
    have he := (finiteBrownianOn_weighted_increment hB hst ht ha).2
    rw [show (∫ ω, a ω ∂μ) = μ.real A from integral_indicator_one hAμ] at he
    convert he using 2
    funext ω
    by_cases hω : ω ∈ A <;> simp [a, d, hω]
  have hcomp : (∫ ω in A, B t ω ^ 2 ∂μ) =
      (∫ ω in A, B s ω ^ 2 ∂μ) + μ.real A * ((t : ℝ) - (s : ℝ)) := by
    have hcrossI : Integrable (fun ω => B s ω * d ω) μ := hs₂.integrable_mul hd₂
    have hsum : Integrable (fun ω => B s ω ^ 2 + 2 * (B s ω * d ω)) μ :=
      hs₂.integrable_sq.add (hcrossI.const_mul 2)
    have hdI : Integrable (fun ω => d ω ^ 2) μ := hd₂.integrable_sq
    have hrewrite (ω : Ω) : B t ω ^ 2 = (B s ω ^ 2 + 2 * (B s ω * d ω)) + d ω ^ 2 := by
      unfold d
      ring
    simp_rw [hrewrite]
    rw [integral_add hsum.integrableOn hdI.integrableOn,
      integral_add hs₂.integrable_sq.integrableOn (hcrossI.const_mul 2).integrableOn,
      integral_const_mul, hcross, hsecond, mul_zero, add_zero]
  refine ⟨?_, ?_⟩
  · rw [show (∫ ω in A, d ω ∂μ) = (∫ ω in A, B t ω ∂μ) - (∫ ω in A, B s ω ∂μ) from
      integral_sub (ht₂.integrable one_le_two).integrableOn (hs₂.integrable one_le_two).integrableOn] at hcenter
    exact (sub_eq_zero.mp hcenter).symm
  · rw [integral_sub hs₂.integrable_sq.integrableOn (integrable_const _),
      integral_sub ht₂.integrable_sq.integrableOn (integrable_const _), setIntegral_const, setIntegral_const,
      hcomp, smul_eq_mul, smul_eq_mul]
    ring

/-- A supplied finite-horizon Brownian law entails the frozen martingale
and square-clock inputs of the joint Itô map on that same filtration. -/
theorem finiteBrownianOn_frozen_martingales (hB : MathFinBridge.BrownianOn μ F H B) :
    let X : ℝ≥0 → Ω → ℝ := fun t => B (min t H)
    (∀ t, MemLp (X t) 2 μ) ∧ Martingale X F μ ∧
      Martingale (fun t ω => X t ω ^ 2 - ((min t H : ℝ≥0) : ℝ)) F μ := by
  let X : ℝ≥0 → Ω → ℝ := fun t => B (min t H)
  have h₂ (t : ℝ≥0) : MemLp (X t) 2 μ := finiteBrownianOn_memLp hB _ (min_le_right _ _) 2 (by simp)
  have hX (t : ℝ≥0) : StronglyMeasurable[F t] (X t) :=
    (hB.adapted _).mono (F.mono (min_le_left t H))
  refine ⟨h₂, martingale_of_past_set_integrals hX (fun t => (h₂ t).integrable one_le_two) ?_,
    martingale_of_past_set_integrals (fun t => ((hX t).pow 2).sub stronglyMeasurable_const)
      (fun t => (h₂ t).integrable_sq.sub (integrable_const _)) ?_⟩
  · intro s t hst A hA
    by_cases hs : s ≤ H
    · rw [min_eq_left hs]
      exact (finiteBrownianOn_setIntegral hB (le_min hst hs) (min_le_right _ _) hA).1
    · simp only [min_eq_right (le_of_not_ge hs), min_eq_right ((le_of_not_ge hs).trans hst)]
  · intro s t hst A hA
    change (∫ ω in A, B (min s H) ω ^ 2 - ((min s H : ℝ≥0) : ℝ) ∂μ) = _
    by_cases hs : s ≤ H
    · rw [min_eq_left hs]
      exact (finiteBrownianOn_setIntegral hB (le_min hst hs) (min_le_right _ _) hA).2
    · simp only [min_eq_right (le_of_not_ge hs), min_eq_right ((le_of_not_ge hs).trans hst)]

end GirsanovPort
end RoughHeston

#print axioms RoughHeston.GirsanovPort.finiteBrownianOn_frozen_martingales
