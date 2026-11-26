import EulerSpatialTruncation

/-! Continuity and adaptedness of the original linearly growing observables. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- The canonical time integral is continuous when every radial
truncation of its coefficient is bounded. This applies to linear drift
and quadratic-growth covariance. -/
theorem continuous_canonicalCoefficientIntegral_of_bounded_truncations
    (T t : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    (hCut : ∀ R : ℝ, 0 < R → ∃ B, ∀ r y, ‖c r (radialTruncation R y)‖ ≤ B) :
    Continuous (canonicalCoefficientIntegral T c t) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let R := ‖p‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  obtain ⟨B, hB⟩ := hCut R hR
  have hcR := continuous_comp_radialTruncation hR hc
  have hCt := (continuous_canonicalCoefficientIntegral T t hcR hB).continuousAt (x := p)
  apply hCt.congr_of_eventuallyEq
  have hNear : ∀ᶠ q in 𝓝 p, ‖q‖ < R := (continuous_norm.tendsto p).eventually
    (Iio_mem_nhds (by dsimp [R]; linarith))
  filter_upwards [hNear] with q hq
  exact (canonicalCoefficientIntegral_comp_radialTruncation_eq T t hR c q
    (fun r _ => (q.norm_coe_le_norm (canonicalEvalTime T r)).trans hq.le)).symm

omit [Fintype κ] in
theorem stronglyAdapted_canonicalCoefficientIntegral_of_bounded_truncations
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    (hCut : ∀ R : ℝ, 0 < R → ∃ B, ∀ r y, ‖c r (radialTruncation R y)‖ ≤ B) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := ι → ℝ) T)
      (canonicalCoefficientIntegral T c) := by
  intro t
  rw [canonicalPathNaturalFiltration_eq_comap_stopped]
  apply Measurable.stronglyMeasurable
  have h := ((continuous_canonicalCoefficientIntegral_of_bounded_truncations T t hc hCut).measurable.comp
    (comap_measurable (canonicalStoppedPath (E := ι → ℝ) T t)))
  convert h using 1
  funext p
  exact (canonicalCoefficientIntegral_stopped T t c p).symm

omit [Fintype κ] in
theorem continuous_canonicalEulerMartingaleCoordinate_of_growth
    (T t : ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    {L : ℝ} (hL : 0 ≤ L) (hg : ∀ r y, ‖b r y i‖ ≤ L * (1+‖y‖)) :
    Continuous (canonicalEulerMartingaleCoordinate T b x i t) := by
  apply (((continuous_apply i).comp (continuous_canonicalPathEval T t)).sub continuous_const).sub
  apply continuous_canonicalCoefficientIntegral_of_bounded_truncations T t hb
  intro R hR
  refine ⟨L*(1+R), fun r y => ?_⟩
  exact (norm_comp_radialTruncation_le hR hL hg r y).trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (min_le_left _ _)) hL)

omit [Fintype κ] in
theorem stronglyAdapted_canonicalEulerMartingaleCoordinate_of_growth
    (T : ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    {L : ℝ} (hL : 0 ≤ L) (hg : ∀ r y, ‖b r y i‖ ≤ L * (1+‖y‖)) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := ι → ℝ) T)
      (canonicalEulerMartingaleCoordinate T b x i) := by
  have hA := stronglyAdapted_canonicalCoefficientIntegral_of_bounded_truncations T (c := fun r y => b r y i) hb (fun R hR => by
    refine ⟨L*(1+R), fun r y => ?_⟩
    exact (norm_comp_radialTruncation_le hR hL hg r y).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (min_le_left _ _)) hL))
  intro t
  have he : Measurable[canonicalPathNaturalFiltration (E := ι → ℝ) T t]
      (fun p => canonicalPathEval T t p i) := by
    rw [canonicalPathNaturalFiltration_eq_comap_stopped]
    have hm := ((measurable_pi_apply i).comp (continuous_canonicalPathEval T t).measurable).comp
      (comap_measurable (canonicalStoppedPath (E := ι → ℝ) T t))
    convert hm using 1
    funext p
    have he : canonicalStopTime T t (canonicalEvalTime T t) = canonicalEvalTime T t :=
      Subtype.ext (min_eq_left (min_le_left t T))
    exact congrArg (fun u : CanonicalPathTime T => p u i) he.symm
  exact (he.stronglyMeasurable.sub stronglyMeasurable_const).sub (hA t)

theorem eulerCovarianceCoefficient_has_bounded_truncations
    {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hG : ∀ r y i j, ‖σ r y i j‖ ≤ L * (1+‖y‖)) (i l : ι) :
    ∀ R : ℝ, 0 < R → ∃ B, ∀ r y,
      ‖eulerCovarianceCoefficient σ i l r (radialTruncation R y)‖ ≤ B := by
  intro R hR
  let σR (r : ℝ≥0) (y : ι → ℝ) := σ r (radialTruncation R y)
  let B := L*(1+R)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hBound (r : ℝ≥0) (y : ι → ℝ) (i : ι) (j : κ) : ‖σR r y i j‖ ≤ B :=
    (norm_comp_radialTruncation_le hR hL (fun u z => hG u z i j) r y).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (min_le_left _ _)) hL)
  exact ⟨(Fintype.card κ : ℝ)*B^2, norm_eulerCovarianceCoefficient_le hB hBound i l⟩

theorem continuous_canonicalEulerCompensatedProduct_of_growth
    (T t : ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L : ℝ} (hL : 0 ≤ L) (hB : ∀ r y i, ‖b r y i‖ ≤ L*(1+‖y‖))
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ L*(1+‖y‖)) :
    Continuous (canonicalEulerCompensatedProduct T b σ x i l t) :=
  ((continuous_canonicalEulerMartingaleCoordinate_of_growth T t x i (hb i) hL (fun r y => hB r y i)).mul
    (continuous_canonicalEulerMartingaleCoordinate_of_growth T t x l (hb l) hL (fun r y => hB r y l))).sub
      (continuous_canonicalCoefficientIntegral_of_bounded_truncations T t
        (continuous_eulerCovarianceCoefficient hσ i l)
        (eulerCovarianceCoefficient_has_bounded_truncations hL hC i l))

theorem stronglyAdapted_canonicalEulerCompensatedProduct_of_growth
    (T : ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    (x : ι → ℝ) (i l : ι)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {L : ℝ} (hL : 0 ≤ L) (hB : ∀ r y i, ‖b r y i‖ ≤ L*(1+‖y‖))
    (hC : ∀ r y i j, ‖σ r y i j‖ ≤ L*(1+‖y‖)) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := ι → ℝ) T)
      (canonicalEulerCompensatedProduct T b σ x i l) := fun t =>
  ((stronglyAdapted_canonicalEulerMartingaleCoordinate_of_growth T x i (hb i) hL (fun r y => hB r y i) t).mul
    (stronglyAdapted_canonicalEulerMartingaleCoordinate_of_growth T x l (hb l) hL (fun r y => hB r y l) t)).sub
      (stronglyAdapted_canonicalCoefficientIntegral_of_bounded_truncations T
        (continuous_eulerCovarianceCoefficient hσ i l)
        (eulerCovarianceCoefficient_has_bounded_truncations hL hC i l) t)

#print axioms RoughHeston.continuous_canonicalEulerMartingaleCoordinate_of_growth
#print axioms RoughHeston.stronglyAdapted_canonicalEulerCompensatedProduct_of_growth

end RoughHeston
