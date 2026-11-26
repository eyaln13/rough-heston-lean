import CanonicalLinearGrowthObservableMoments

/-! Canonical martingale and compensated-product test moments under growth bounds. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

/-- The unbounded canonical drift-subtracted coordinate is uniformly in
L⁴ whenever the law has uniformly bounded fourth state moments. -/
theorem canonicalEulerMartingaleCoordinate_fourth_bound_of_state
    {ι : Type*} [Fintype ι] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι) (t : ℝ≥0)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hG : ∀ r y, ‖b r y i‖ ≤ L*(1+‖y‖))
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ]
    (h4 : ∀ r i, Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T r p i)^4) μ)
    (hE : ∀ r, canonicalEulerStateFourthMoment T μ r ≤ H) :
    let M := canonicalEulerMartingaleCoordinate T b x i t
    let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
    MemLp M 4 μ ∧ (∫ p, (M p)^4 ∂μ) ≤ 8*(8*(H+(x i)^4)+Q*(T : ℝ)^4*(1+H)) := by
  dsimp only
  let P := CanonicalPath T (ι → ℝ)
  let D := canonicalCoefficientIntegral T (fun r y => b r y i) t
  let X (p : P) := canonicalPathEval T t p i
  let U (p : P) := X p - x i
  let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
  have hQc : 0 ≤ Q := by dsimp [Q]; positivity
  have hCut (R : ℝ) (hR : 0 < R) : ∃ B, ∀ r y, ‖b r (radialTruncation R y) i‖ ≤ B := by
    refine ⟨L*(1+R), fun r y => ?_⟩
    exact (norm_comp_radialTruncation_le hR hL hG r y).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (min_le_left _ _)) hL)
  have hGrowth (r : ℝ≥0) (y : ι → ℝ) :
      ‖(b r y i)^4‖ ≤ Q*(1+∑ j, (y j)^4) := by
    rw [Real.norm_of_nonneg (by positivity)]
    exact growth_fourth_le (hG r y)
  have hD := integral_pow_canonicalCoefficientIntegral_le_of_uniform_state_fourth T t
    (c := fun r y => b r y i) hb hCut (Or.inr rfl : (4 : ℕ) = 2 ∨ 4 = 4) hQc hH hGrowth μ h4 hE
  have hDc := continuous_canonicalCoefficientIntegral_of_bounded_truncations T t
    (c := fun r y => b r y i) hb hCut
  have hD₄ : MemLp D 4 μ := memLp_four_of_integrable_pow_four hDc.stronglyMeasurable.aestronglyMeasurable hD.1
  have hXm : Continuous X := (continuous_apply i).comp (continuous_canonicalPathEval T t)
  have hX₄ : MemLp X 4 μ := memLp_four_of_integrable_pow_four hXm.stronglyMeasurable.aestronglyMeasurable (h4 t i)
  have hXi : (∫ p, X p^4 ∂μ) ≤ H := by
    apply le_trans _ (hE t)
    exact Finset.single_le_sum (f := fun j => ∫ p : P, (canonicalPathEval T t p j)^4 ∂μ)
      (fun _ _ => integral_nonneg fun _ => by positivity) (Finset.mem_univ i)
  have hU := memLp_and_integral_pow_four_sub_le_of_bound hX₄ (A := fun _ => x i)
    aestronglyMeasurable_const (fun _ => le_rfl)
  have hU₄ : MemLp U 4 μ := hU.1
  have hUM : (∫ p, (U p)^4 ∂μ) ≤ 8*(H+(x i)^4) := by
    have h := hU.2
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ (x i)^4)] at h
    exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hXi le_rfl) (by norm_num))
  refine ⟨hU₄.sub hD₄, ?_⟩
  have h := integral_pow_four_add_le hU₄ hD₄.neg
  have he (p : P) : (-D p)^4 = (D p)^4 := by ring
  simp only [Pi.neg_apply, ← sub_eq_add_neg, he] at h
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add hUM hD.2) (by norm_num))

theorem covariance_cross_sq_le_of_growth {ι κ : Type*} [Fintype ι] [Fintype κ]
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ} {L : ℝ}
    (hG : ∀ r y i j, ‖σ r y i j‖ ≤ L*(1+‖y‖)) (i l : ι) (r : ℝ≥0) (y : ι → ℝ) :
    (eulerCovarianceCoefficient σ i l r y)^2 ≤
      (Fintype.card κ : ℝ)^2*(8*L^4*(1+(Fintype.card ι : ℝ)))*(1+∑ j, (y j)^4) := by
  let K := (Fintype.card κ : ℝ)^2*(8*L^4*(1+(Fintype.card ι : ℝ)))*(1+∑ j, (y j)^4)
  have hII : (eulerCovarianceCoefficient σ i i r y)^2 ≤ K := covariance_sq_le_of_growth hG i r y
  have hLL : (eulerCovarianceCoefficient σ l l r y)^2 ≤ K := covariance_sq_le_of_growth hG l r y
  have hCross : (eulerCovarianceCoefficient σ i l r y)^2 ≤
      eulerCovarianceCoefficient σ i i r y * eulerCovarianceCoefficient σ l l r y := by
    simpa only [eulerCovarianceCoefficient, pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset κ) (fun j => σ r y i j) (fun j => σ r y l j))
  have hs := sq_nonneg (eulerCovarianceCoefficient σ i i r y - eulerCovarianceCoefficient σ l l r y)
  exact hCross.trans (by nlinarith [hs])

theorem canonicalEulerCompensatedProduct_sq_bound_of_state
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι) (t : ℝ≥0)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L H : ℝ} (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hB : ∀ r y i, ‖b r y i‖ ≤ L*(1+‖y‖))
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ L*(1+‖y‖))
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ]
    (h4 : ∀ r i, Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T r p i)^4) μ)
    (hE : ∀ r, canonicalEulerStateFourthMoment T μ r ≤ H) :
    let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
    let V (i : ι) := 8*(8*(H+(x i)^4)+Q*(T : ℝ)^4*(1+H))
    let C := canonicalEulerCompensatedProduct T b σ x i l t
    MemLp C 2 μ ∧ (∫ p, (C p)^2 ∂μ) ≤
      2*((V i + V l)/2 + (Fintype.card κ : ℝ)^2*Q*(T : ℝ)^2*(1+H)) := by
  dsimp only
  let Q := 8*L^4*(1+(Fintype.card ι : ℝ))
  let V (j : ι) := 8*(8*(H+(x j)^4)+Q*(T : ℝ)^4*(1+H))
  let P := CanonicalPath T (ι → ℝ)
  let A := canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i l) t
  let M (j : ι) := canonicalEulerMartingaleCoordinate T b x j t
  let D := (Fintype.card κ : ℝ)^2*Q*(T : ℝ)^2*(1+H)
  have hM (j : ι) : MemLp (M j) 4 μ ∧ (∫ p : P, (M j p)^4 ∂μ) ≤ V j :=
    canonicalEulerMartingaleCoordinate_fourth_bound_of_state x j t (hb j) hL hH
      (fun r y => hB r y j) μ h4 hE
  have hCut := eulerCovarianceCoefficient_has_bounded_truncations hL hC i l
  have hc := continuous_eulerCovarianceCoefficient hσ i l
  have hGrowth (r : ℝ≥0) (y : ι → ℝ) :
      ‖(eulerCovarianceCoefficient σ i l r y)^2‖ ≤
        (Fintype.card κ : ℝ)^2*Q*(1+∑ j, (y j)^4) := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact covariance_cross_sq_le_of_growth hC i l r y
  have hA : Integrable (fun p : P => (A p)^2) μ ∧ (∫ p : P, (A p)^2 ∂μ) ≤ D :=
    integral_pow_canonicalCoefficientIntegral_le_of_uniform_state_fourth T t hc hCut
      (Or.inl rfl : (2 : ℕ) = 2 ∨ 2 = 4) (by dsimp [Q]; positivity) hH hGrowth μ h4 hE
  have hAc := continuous_canonicalCoefficientIntegral_of_bounded_truncations T t hc hCut
  have hA₂ : MemLp A 2 μ := (memLp_two_iff_integrable_sq hAc.stronglyMeasurable.aestronglyMeasurable).2 hA.1
  have h := integral_sq_mul_le_of_four (hM i).1 (hM l).1
  refine ⟨h.1.sub hA₂, (integral_sq_sub_le h.1 hA₂).trans ?_⟩
  have hB := h.2.trans (mul_le_mul_of_nonneg_left (add_le_add (hM i).2 (hM l).2)
    (show (0 : ℝ) ≤ 1/2 by norm_num))
  simp only [Pi.mul_apply]
  linarith [hA.2]

#print axioms RoughHeston.canonicalEulerMartingaleCoordinate_fourth_bound_of_state
#print axioms RoughHeston.canonicalEulerCompensatedProduct_sq_bound_of_state

end RoughHeston
