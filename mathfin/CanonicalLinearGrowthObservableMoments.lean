import EulerUniformFourthEnergy
import UnboundedCanonicalCoefficients

/-! Uniform moments of the untruncated test observables under the cutoff laws. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

/-- Uniform fourth state moments control the original drift to the
fourth power and original covariance to the second power. The argument
uses actual time-sample product integrability for the unbounded coefficient. -/
theorem integral_pow_canonicalCoefficientIntegral_le_of_uniform_state_fourth
    {ι : Type*} [Fintype ι] (T t : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ}
    (hc : Continuous (Function.uncurry c))
    (hCut : ∀ R : ℝ, 0 < R → ∃ B, ∀ r y, ‖c r (radialTruncation R y)‖ ≤ B)
    {n : ℕ} (hn : n = 2 ∨ n = 4) {Q H : ℝ} (hQ : 0 ≤ Q) (hH : 0 ≤ H)
    (hGrowth : ∀ r y, ‖(c r y)^n‖ ≤ Q * (1+∑ i, (y i)^4))
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ]
    (h4 : ∀ r i, Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T r p i)^4) μ)
    (hE : ∀ r, canonicalEulerStateFourthMoment T μ r ≤ H) :
    Integrable (fun p => (canonicalCoefficientIntegral T c t p)^n) μ ∧
      (∫ p, (canonicalCoefficientIntegral T c t p)^n ∂μ) ≤ Q * (T : ℝ)^n * (1+H) := by
  let P := CanonicalPath T (ι → ℝ)
  let ν := timeMeasureHorizon (min t T)
  let F (r : ℝ≥0) (p : P) := c r (canonicalPathEval T r p)
  let Y (r : ℝ≥0) (p : P) := (F r p)^n
  let Z (r : ℝ≥0) (p : P) := ∑ i, (canonicalPathEval T r p i)^4
  let C := Q*(1+H)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hFc : Continuous (Function.uncurry F) := hc.comp (continuous_fst.prodMk (continuous_joint_pathEval T))
  have hYc : Continuous (Function.uncurry Y) := hFc.pow n
  have hJc : Continuous (canonicalCoefficientIntegral T c t) :=
    continuous_canonicalCoefficientIntegral_of_bounded_truncations T t hc hCut
  have hZ (r : ℝ≥0) : Integrable (Z r) μ := integrable_finsetSum _ fun i _ => h4 r i
  have hMeanZ (r : ℝ≥0) : (∫ p, Z r p ∂μ) = canonicalEulerStateFourthMoment T μ r := by
    dsimp only [Z, canonicalEulerStateFourthMoment]
    rw [integral_finsetSum _ (fun i _ => h4 r i)]
  have hYInt (r : ℝ≥0) : Integrable (Y r) μ := by
    have hd : Integrable (fun p => (1 : ℝ)+Z r p) μ := (integrable_const _).add (hZ r)
    exact (hd.const_mul Q).mono'
      (hYc.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun p => hGrowth r (canonicalPathEval T r p))
  have hYn (r : ℝ≥0) (p : P) : 0 ≤ Y r p := by
    rcases hn with h | h <;> subst n <;> dsimp only [Y] <;> positivity
  have hYMean (r : ℝ≥0) : (∫ p, ‖Y r p‖ ∂μ) ≤ C := by
    have hd : Integrable (fun p => (1 : ℝ)+Z r p) μ := (integrable_const _).add (hZ r)
    calc
      _ ≤ ∫ p, Q*(1+Z r p) ∂μ := integral_mono (hYInt r).norm (hd.const_mul _)
        (fun p => hGrowth r (canonicalPathEval T r p))
      _ = Q * (1+canonicalEulerStateFourthMoment T μ r) := by
        rw [integral_const_mul, integral_add (integrable_const (1 : ℝ)) (hZ r), hMeanZ]
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add le_rfl (hE r)) hQ
  have hMeanI : Integrable (fun r => ∫ p, ‖Y r p‖ ∂μ) ν :=
    (integrable_const C).mono' hYc.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
        exact hYMean r)
  have hYJoint : Integrable (Function.uncurry Y) (ν.prod μ) :=
    (integrable_prod_iff hYc.stronglyMeasurable.aestronglyMeasurable).2
      ⟨Eventually.of_forall hYInt, hMeanI⟩
  have hMem (p : P) (q : ℝ≥0∞) : MemLp (fun r => F r p) q ν := by
    have hf : Continuous (fun r => F r p) := hFc.comp (continuous_id.prodMk continuous_const)
    obtain ⟨C, hC⟩ := (isCompact_Icc.image hf.norm :
      IsCompact ((fun r => ‖F r p‖) '' Icc 0 T)).bddAbove
    refine MemLp.of_bound hf.stronglyMeasurable.aestronglyMeasurable C ?_
    have hν : ∀ᵐ r ∂ν, r ∈ Ioc 0 (min t T) := ae_restrict_mem measurableSet_Ioc
    filter_upwards [hν] with r hr
    exact hC (mem_image_of_mem _ ⟨zero_le, hr.2.trans (min_le_right _ _)⟩)
  have hPoint (p : P) : (canonicalCoefficientIntegral T c t p)^n ≤
      (ν.real univ)^(n-1) * ∫ r, Y r p ∂ν := by
    rcases hn with h | h
    · subst n
      simpa only [canonicalCoefficientIntegral, F, Y, Nat.reduceSub, pow_one, ν] using
        integral_sq_le_measure_mul_sqIntegral (hMem p 2)
    · subst n
      exact integral_fourth_le_measure_cube_mul_pow_four (hMem p 4)
  have hPos (p : P) : 0 ≤ (canonicalCoefficientIntegral T c t p)^n := by
    rcases hn with h | h <;> subst n <;> positivity
  have hDI : Integrable (fun p : P => (ν.real univ)^(n-1) * ∫ r, Y r p ∂ν) μ :=
    hYJoint.integral_prod_right.const_mul _
  have hJI : Integrable (fun p : P => (canonicalCoefficientIntegral T c t p)^n) μ :=
    hDI.mono' (hJc.pow n).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [Real.norm_of_nonneg (hPos p)]; exact hPoint p)
  refine ⟨hJI, ?_⟩
  have hν₀ : 0 ≤ ν.real univ := ENNReal.toReal_nonneg
  have hMass : ν.real univ ≤ (T : ℝ) := by
    dsimp only [ν]
    rw [euler_timeMeasureHorizon_mass]
    exact NNReal.coe_le_coe.mpr (min_le_right _ _)
  have hYtime : (∫ r, ∫ p, Y r p ∂μ ∂ν) ≤ C * ν.real univ := by
    have hbound (r : ℝ≥0) : (∫ p, Y r p ∂μ) ≤ C := by
      simpa only [Real.norm_of_nonneg (hYn r _)] using hYMean r
    exact (integral_mono hYJoint.integral_prod_left (integrable_const C) hbound).trans_eq
      (by rw [integral_const, smul_eq_mul, mul_comm])
  calc
    _ ≤ ∫ p, (ν.real univ)^(n-1) * ∫ r, Y r p ∂ν ∂μ :=
      integral_mono hJI hDI hPoint
    _ = (ν.real univ)^(n-1) * ∫ r, ∫ p, Y r p ∂μ ∂ν := by
      rw [integral_const_mul, ← integral_integral_swap hYJoint]
    _ ≤ (ν.real univ)^(n-1) * (C * ν.real univ) :=
      mul_le_mul_of_nonneg_left hYtime (pow_nonneg hν₀ _)
    _ = C * (ν.real univ)^n := by
      rcases hn with h | h <;> subst n <;> norm_num <;> ring
    _ ≤ C * (T : ℝ)^n := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hν₀ hMass _) hC
    _ = _ := by dsimp [C]; ring

#print axioms RoughHeston.integral_pow_canonicalCoefficientIntegral_le_of_uniform_state_fourth

end RoughHeston
