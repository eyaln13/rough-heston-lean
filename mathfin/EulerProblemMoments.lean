import EulerObservableMoments

/-! Timewise uniform moments for the two classes of martingale-problem observables. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω ι : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}

theorem memLp_and_integral_pow_four_sub_le_of_bound [IsProbabilityMeasure μ]
    {X A : Ω → ℝ} (hX : MemLp X 4 μ) {R : ℝ}
    (hA : AEStronglyMeasurable A μ) (hR : ∀ ω, ‖A ω‖ ≤ R) :
    MemLp (X - A) 4 μ ∧
      (∫ ω, (X ω - A ω)^4 ∂μ) ≤ 8 * ((∫ ω, X ω^4 ∂μ) + R^4) := by
  have hA₄ : MemLp A 4 μ := MemLp.of_bound hA R (Eventually.of_forall hR)
  have hAInt := integrable_pow_four_of_memLp hA₄
  have hD (ω : Ω) : A ω ^4 ≤ R^4 := by
    have h := pow_le_pow_left₀ (norm_nonneg (A ω)) (hR ω) 4
    rwa [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ A ω ^4)] at h
  have hBound : (∫ ω, A ω ^4 ∂μ) ≤ R^4 :=
    (integral_mono hAInt (integrable_const _) hD).trans_eq (by simp)
  refine ⟨hX.sub hA₄, ?_⟩
  have h := integral_pow_four_add_le hX hA₄.neg
  have he : (∫ ω, (-A ω)^4 ∂μ) = ∫ ω, A ω ^4 ∂μ := by
    congr 1
    funext ω
    ring
  simp only [Pi.neg_apply, ← sub_eq_add_neg, he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hBound) (by norm_num))

theorem memLp_and_integral_sq_sub_le_of_bound [IsProbabilityMeasure μ]
    {X A : Ω → ℝ} (hX : MemLp X 2 μ) {R : ℝ}
    (hA : AEStronglyMeasurable A μ) (hR : ∀ ω, ‖A ω‖ ≤ R) :
    MemLp (X - A) 2 μ ∧
      (∫ ω, (X ω - A ω)^2 ∂μ) ≤ 2 * ((∫ ω, X ω^2 ∂μ) + R^2) := by
  have hA₂ : MemLp A 2 μ := MemLp.of_bound hA R (Eventually.of_forall hR)
  have hD (ω : Ω) : A ω ^2 ≤ R^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (A ω)) (hR ω) 2
    rwa [Real.norm_eq_abs, sq_abs] at h
  have hBound : (∫ ω, A ω ^2 ∂μ) ≤ R^2 :=
    (integral_mono hA₂.integrable_sq (integrable_const _) hD).trans_eq (by simp)
  exact ⟨hX.sub hA₂, (integral_sq_sub_le hX hA₂).trans
    (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hBound) (by norm_num))⟩

theorem norm_canonicalGridCoefficientSum_le [Fintype ι]
    (T : ℝ≥0) (grid : ℕ →o ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} {B : ℝ}
    (hB : ∀ r y, ‖c r y‖ ≤ B) (a : ℕ) (p : CanonicalPath T (ι → ℝ)) :
    ‖canonicalGridCoefficientSum T grid c a p‖ ≤ B * ((grid a : ℝ) - (grid 0 : ℝ)) := by
  induction a with
  | zero => simp [canonicalGridCoefficientSum]
  | succ a ih =>
    let d := (grid (a+1) : ℝ) - (grid a : ℝ)
    let q := c (grid a) (canonicalPathEval T (grid a) p)
    have hd : 0 ≤ d := sub_nonneg.mpr (NNReal.coe_le_coe.mpr (grid.monotone a.le_succ))
    have hSum : canonicalGridCoefficientSum T grid c (a+1) p =
        canonicalGridCoefficientSum T grid c a p + q*d := by
      simp only [canonicalGridCoefficientSum, runningSum_succ, Pi.add_apply, q, d]
    rw [hSum]
    calc
      _ ≤ ‖canonicalGridCoefficientSum T grid c a p‖ + ‖q*d‖ := norm_add_le _ _
      _ ≤ B * ((grid a : ℝ) - (grid 0 : ℝ)) + B*d := by
        rw [norm_mul, Real.norm_of_nonneg hd]
        exact add_le_add ih (mul_le_mul_of_nonneg_right (hB _ _) hd)
      _ = _ := by dsimp [d]; ring

#print axioms RoughHeston.memLp_and_integral_pow_four_sub_le_of_bound
#print axioms RoughHeston.memLp_and_integral_sq_sub_le_of_bound
#print axioms RoughHeston.norm_canonicalGridCoefficientSum_le

end RoughHeston
