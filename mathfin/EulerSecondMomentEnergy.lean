import EulerSpatialTruncation
import BoundedEulerMartingaleProblemExistence

/-! Second-moment energy estimates for removing bounded spatial truncations. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

theorem integral_sq_le_measure_mul_sqIntegral {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] {f : Y → ℝ} (hF : MemLp f 2 ν) :
    (∫ y, f y ∂ν)^2 ≤ ν.real univ * (∫ y, f y ^ 2 ∂ν) := by
  by_cases hν : ν = 0
  · simp [hν]
  let : NeZero ν := ⟨hν⟩
  let a := ν.real univ
  let I := ∫ y, f y ∂ν
  have ha : 0 < a := measureReal_univ_pos
  have hf := hF.integrable one_le_two
  have h2 : Integrable (fun y => a^2 * f y^2) ν := hF.integrable_sq.const_mul _
  have h1 : Integrable (fun y => 2*a*I * f y) ν := hf.const_mul _
  have hD : Integrable (fun y => a^2 * f y^2 - 2*a*I*f y) ν := h2.sub h1
  have hPoly :
      (∫ y, (a*f y-I)^2 ∂ν) =
      a^2 * (∫ y, f y^2 ∂ν) - 2*a*I * I + a*I^2 := by
    calc
      _ = ∫ y, (a^2 * f y^2 - (2*a*I) * f y) + I^2 ∂ν := by
        apply integral_congr_ae
        exact Eventually.of_forall fun _ => by ring
      _ = _ := by
        rw [integral_add hD (integrable_const _), integral_sub h2 h1,
          integral_const_mul, integral_const_mul, integral_const, smul_eq_mul]
  have hn : 0 ≤ a^2 * (∫ y, f y^2 ∂ν) - 2*a*I*I + a*I^2 :=
    hPoly ▸ integral_nonneg (fun _ => sq_nonneg _)
  have hh : 0 ≤ a * (a * (∫ y, f y^2 ∂ν) - I^2) := by linarith [hn]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right hh ha)

private theorem timeMeasureHorizon_mass (t : ℝ≥0) :
    (timeMeasureHorizon t).real univ = (t : ℝ) := by
  rw [measureReal_def, timeMeasureHorizon, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, MathFin.ItoIntegralL2.timeMeasure_Ioc, NNReal.coe_zero, sub_zero,
    ENNReal.toReal_ofReal t.coe_nonneg]

/-- A bounded drift contribution has a squared-mean upper bound given
by elapsed time times the expected integral of the squared coefficient. -/
theorem integral_sq_canonicalCoefficientIntegral_le {ι : Type*} [Fintype ι]
    (T t : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B)
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ] :
    (∫ p, (canonicalCoefficientIntegral T c t p)^2 ∂μ) ≤
      (↑(min t T) : ℝ) *
        (∫ r, ∫ p, (c r (canonicalPathEval T r p))^2 ∂μ ∂timeMeasureHorizon (min t T)) := by
  let ν := timeMeasureHorizon (min t T)
  let f (r : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) := c r (canonicalPathEval T r p)
  have hET : Continuous (canonicalEvalTime T) :=
    (continuous_id.min continuous_const).subtype_mk _
  have hEval : Continuous (fun z : ℝ≥0 × CanonicalPath T (ι → ℝ) =>
      canonicalPathEval T z.1 z.2) :=
    continuous_eval.comp (continuous_snd.prodMk (hET.comp continuous_fst))
  have hf : Continuous (Function.uncurry f) := hc.comp (continuous_fst.prodMk hEval)
  have hPoint (p : CanonicalPath T (ι → ℝ)) :
      (∫ r, f r p ∂ν)^2 ≤ ν.real univ * (∫ r, (f r p)^2 ∂ν) := by
    apply integral_sq_le_measure_mul_sqIntegral
    exact MemLp.of_bound ((hf.comp (continuous_id.prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable)
      B (Eventually.of_forall fun r => hB _ _)
  have hBoundedSq (r : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) : ‖(f r p)^2‖ ≤ B^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg (f r p)) (hB r (canonicalPathEval T r p)) 2
    simpa only [norm_pow] using h
  have hJoint : Integrable (Function.uncurry (fun r p => (f r p)^2)) (ν.prod μ) :=
    (integrable_const (B^2)).mono' (hf.pow 2).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun z => hBoundedSq z.1 z.2)
  have hIntegral : Integrable (fun p => (canonicalCoefficientIntegral T c t p)^2) μ := by
    have hMeas := ((continuous_canonicalCoefficientIntegral T t hc hB).pow 2).stronglyMeasurable.aestronglyMeasurable (μ := μ)
    refine (integrable_const ((B * (↑(min t T) : ℝ))^2)).mono' hMeas (Eventually.of_forall fun p => ?_)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_canonicalCoefficientIntegral_le T t hB p) 2
  calc
    _ ≤ ∫ p, ν.real univ * (∫ r, (f r p)^2 ∂ν) ∂μ := by
      apply integral_mono hIntegral (hJoint.integral_prod_right.const_mul _)
      exact hPoint
    _ = _ := by
      rw [integral_const_mul, ← integral_integral_swap hJoint, timeMeasureHorizon_mass]

/-- The quadratic martingale identity gives the exact second moment
of the drift-subtracted coordinate in terms of expected accumulated
diagonal covariance. -/
theorem canonicalEulerMartingaleCoordinate_sq_eq_covariance
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {C : ℝ} (hC₀ : 0 ≤ C) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (i : ι)
    (hQ : Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ) (t : ℝ≥0) :
    Integrable (fun p => (canonicalEulerMartingaleCoordinate T b x i t p)^2) μ ∧
      (∫ p, (canonicalEulerMartingaleCoordinate T b x i t p)^2 ∂μ) =
        ∫ p, canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i i) t p ∂μ := by
  let A := canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i i) t
  let M := canonicalEulerMartingaleCoordinate T b x i t
  let Q := canonicalEulerCompensatedProduct T b σ x i i
  have hBound := norm_eulerCovarianceCoefficient_le hC₀ hC i i
  have hA : Integrable A μ :=
    (integrable_const (((Fintype.card κ : ℝ) * C^2) * (↑(min t T) : ℝ))).mono'
      (continuous_canonicalCoefficientIntegral T t
        (continuous_eulerCovarianceCoefficient hσ i i) hBound).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun p => norm_canonicalCoefficientIntegral_le T t hBound p)
  have hM2 : (Q t + A) = fun p => M p ^ 2 := by
    funext p
    simp [Q, A, M, canonicalEulerCompensatedProduct, pow_two, Pi.add_apply]
  have hM : Integrable (fun p => M p ^ 2) μ := by rw [← hM2]; exact (hQ.integrable t).add hA
  have hS : MeasurableSet {p | canonicalPathEval T 0 p = x} :=
    (isClosed_eq (continuous_canonicalPathEval T 0) continuous_const).measurableSet
  have hInitAE : ∀ᵐ p ∂μ, canonicalPathEval T 0 p = x := by
    apply ae_iff.2
    change μ {p | canonicalPathEval T 0 p = x}ᶜ = 0
    rw [measure_compl hS (measure_ne_top _ _), hInit, measure_univ, tsub_self]
  have hA0 (c : ℝ≥0 → (ι → ℝ) → ℝ) (p : CanonicalPath T (ι → ℝ)) :
      canonicalCoefficientIntegral T c 0 p = 0 := by
    simp [canonicalCoefficientIntegral, timeMeasureHorizon]
  have hQ0 : Q 0 =ᵐ[μ] 0 := by
    filter_upwards [hInitAE] with p hp
    simp only [Q, canonicalEulerCompensatedProduct, canonicalEulerMartingaleCoordinate,
      hA0, hp, sub_self, zero_mul, Pi.zero_apply]
  have hQt : (∫ p, Q t p ∂μ) = 0 := by
    have hEq := hQ.setIntegral_eq (show (0 : ℝ≥0) ≤ t from zero_le)
      (MeasurableSet.univ : MeasurableSet[canonicalPathNaturalFiltration (E := ι → ℝ) T 0] univ)
    rw [Measure.restrict_univ] at hEq
    exact hEq.symm.trans (by change (∫ p, Q 0 p ∂μ) = 0; rw [integral_congr_ae hQ0]; simp)
  refine ⟨hM, ?_⟩
  change (∫ p, M p^2 ∂μ) = ∫ p, A p ∂μ
  rw [← hM2]
  exact (integral_add (hQ.integrable t) hA).trans (by rw [hQt, zero_add])

/-- The canonical coordinate's second-moment energy is controlled by
its accumulated squared drift and the expected diagonal covariance. -/
theorem integral_sq_canonicalEulerState_le_energy
    {ι κ : Type*} [Fintype ι] [Fintype κ] {T : ℝ≥0}
    {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} {σ : ℝ≥0 → (ι → ℝ) → ι → κ → ℝ}
    {x : ι → ℝ} {μ : Measure (CanonicalPath T (ι → ℝ))} [IsProbabilityMeasure μ]
    (hInit : μ {p | canonicalPathEval T 0 p = x} = 1)
    (hb : ∀ i, Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    (hσ : ∀ i j, Continuous (fun z : ℝ≥0 × (ι → ℝ) => σ z.1 z.2 i j))
    {B C : ℝ} (hB : ∀ r y i, ‖b r y i‖ ≤ B)
    (hC₀ : 0 ≤ C) (hC : ∀ r y i j, ‖σ r y i j‖ ≤ C)
    (i : ι)
    (hQ : Martingale (canonicalEulerCompensatedProduct T b σ x i i)
      (canonicalPathNaturalFiltration T) μ) (t : ℝ≥0) :
    Integrable (fun p : CanonicalPath T (ι → ℝ) => (canonicalPathEval T t p i)^2) μ ∧
      (∫ p : CanonicalPath T (ι → ℝ), (canonicalPathEval T t p i)^2 ∂μ) ≤
        3 * (x i)^2 + 3 * (↑(min t T) : ℝ) *
          (∫ r, ∫ p, (b r (canonicalPathEval T r p) i)^2 ∂μ ∂timeMeasureHorizon (min t T)) +
        3 * (∫ p, canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i i) t p ∂μ) := by
  let D := canonicalCoefficientIntegral T (fun r y => b r y i) t
  let M := canonicalEulerMartingaleCoordinate T b x i t
  let X (p : CanonicalPath T (ι → ℝ)) := canonicalPathEval T t p i
  have hM := canonicalEulerMartingaleCoordinate_sq_eq_covariance hInit hσ hC₀ hC i hQ t
  have hD : Integrable (fun p => (D p)^2) μ := by
    have hMeas : AEStronglyMeasurable (fun p => (D p)^2) μ :=
      ((continuous_canonicalCoefficientIntegral T t (hb i) (fun r y => hB r y i)).pow 2).stronglyMeasurable.aestronglyMeasurable
    refine (integrable_const ((B * (↑(min t T) : ℝ))^2)).mono' hMeas (Eventually.of_forall fun p => ?_)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_canonicalCoefficientIntegral_le T t (fun r y => hB r y i) p) 2
  have hDom : Integrable (fun p => (x i)^2 + D p ^ 2 + M p ^ 2) μ :=
    ((integrable_const _).add hD).add hM.1
  have hP (p : CanonicalPath T (ι → ℝ)) :
      X p ^ 2 ≤ 3 * ((x i)^2 + (D p)^2 + (M p)^2) := by
    have h : X p = x i + D p + M p := by
      dsimp [X, D, M, canonicalEulerMartingaleCoordinate]
      ring
    rw [h]
    nlinarith [sq_nonneg (x i - D p), sq_nonneg (x i - M p), sq_nonneg (D p - M p)]
  have hXm : Continuous X := (continuous_apply i).comp (continuous_canonicalPathEval T t)
  have hX : Integrable (fun p => X p ^ 2) μ := (hDom.const_mul 3).mono'
    (hXm.pow 2).stronglyMeasurable.aestronglyMeasurable (Eventually.of_forall fun p => by
      rw [Real.norm_of_nonneg (sq_nonneg (X p))]
      exact hP p)
  refine ⟨hX, ?_⟩
  calc
    _ ≤ ∫ p, 3 * ((x i)^2 + (D p)^2 + (M p)^2) ∂μ :=
      integral_mono hX (hDom.const_mul 3) hP
    _ = 3 * ((x i)^2 + (∫ p, (D p)^2 ∂μ) + ∫ p, (M p)^2 ∂μ) := by
      have hDom' : Integrable (fun p => (x i)^2 + D p ^ 2) μ :=
        (integrable_const _).add hD
      rw [integral_const_mul, integral_add hDom' hM.1, integral_add (integrable_const _) hD]
      simp [M]
    _ ≤ _ := by
      have h := integral_sq_canonicalCoefficientIntegral_le T t (hb i) (fun r y => hB r y i) μ
      change (∫ p, (D p)^2 ∂μ) ≤ _ at h
      have he : (∫ p, (M p)^2 ∂μ) =
          ∫ p, canonicalCoefficientIntegral T (eulerCovarianceCoefficient σ i i) t p ∂μ := hM.2
      rw [he]
      linarith

#print axioms RoughHeston.integral_sq_le_measure_mul_sqIntegral
#print axioms RoughHeston.integral_sq_canonicalEulerState_le_energy
#print axioms RoughHeston.canonicalEulerMartingaleCoordinate_sq_eq_covariance
#print axioms RoughHeston.integral_sq_canonicalCoefficientIntegral_le

end RoughHeston
