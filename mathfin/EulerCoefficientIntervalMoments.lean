import EulerFourthMomentTools

/-! Squared and fourth-power coefficient differences over real time intervals. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace RoughHeston

open MathFin.ItoIntegralCLM

/-- Nonnegative-time Lebesgue measure restricted to a deterministic interval. -/
noncomputable def eulerTimeSlice (s t : ℝ≥0) : Measure ℝ≥0 :=
  MathFin.ItoIntegralL2.timeMeasure.restrict (Ioc s t)

instance (s t : ℝ≥0) : IsFiniteMeasure (eulerTimeSlice s t) := by
  constructor
  rw [eulerTimeSlice, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    MathFin.ItoIntegralL2.timeMeasure_Ioc]
  exact ENNReal.ofReal_lt_top

theorem eulerTimeSlice_mass (s t : ℝ≥0) (hst : s ≤ t) :
    (eulerTimeSlice s t).real univ = (t : ℝ) - (s : ℝ) := by
  rw [measureReal_def, eulerTimeSlice, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    MathFin.ItoIntegralL2.timeMeasure_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst))]

theorem canonicalCoefficientIntegral_sub_eq_slice {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B) (p : CanonicalPath T (ι → ℝ))
    {s t : ℝ≥0} (hst : s ≤ t) :
    canonicalCoefficientIntegral T c t p - canonicalCoefficientIntegral T c s p =
      ∫ r, c r (canonicalPathEval T r p) ∂eulerTimeSlice (min s T) (min t T) := by
  let a := min s T
  let b := min t T
  let f (r : ℝ≥0) := c r (canonicalPathEval T r p)
  let ν := MathFin.ItoIntegralL2.timeMeasure
  have hab : a ≤ b := min_le_min_right T hst
  have hf : Continuous f :=
    hc.comp (continuous_id.prodMk ((continuous_joint_pathEval T).comp (continuous_id.prodMk continuous_const)))
  have hsplit : timeMeasureHorizon b = timeMeasureHorizon a + eulerTimeSlice a b := by
    change ν.restrict (Ioc 0 b) = ν.restrict (Ioc 0 a) + ν.restrict (Ioc a b)
    rw [← Ioc_union_Ioc_eq_Ioc (zero_le : 0 ≤ a) hab,
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  have hF (τ : Measure ℝ≥0) [IsFiniteMeasure τ] : Integrable f τ :=
    (integrable_const B).mono' hf.stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun _ => hB _ _)
  change (∫ r, f r ∂timeMeasureHorizon b) - (∫ r, f r ∂timeMeasureHorizon a) =
    ∫ r, f r ∂eulerTimeSlice a b
  rw [hsplit, integral_add_measure (hF _) (hF _), add_sub_cancel_left]

theorem monotone_canonicalCoefficientIntegral_of_nonneg {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B) (hpos : ∀ r y, 0 ≤ c r y)
    (p : CanonicalPath T (ι → ℝ)) :
    Monotone (fun t => canonicalCoefficientIntegral T c t p) := by
  intro s t hst
  apply sub_nonneg.mp
  rw [canonicalCoefficientIntegral_sub_eq_slice T hc hB p hst]
  exact integral_nonneg fun _ => hpos _ _

/-- Expected powers of a bounded coefficient integral admit the
corresponding time-average estimates for powers two and four. -/
theorem integral_pow_coefficientIntegral_sub_le {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {c : ℝ≥0 → (ι → ℝ) → ℝ} (hc : Continuous (Function.uncurry c))
    {B : ℝ} (hB : ∀ r y, ‖c r y‖ ≤ B)
    (μ : Measure (CanonicalPath T (ι → ℝ))) [IsProbabilityMeasure μ]
    {s t : ℝ≥0} (hst : s ≤ t) {n : ℕ} (hn : n = 2 ∨ n = 4) :
    let D (p : CanonicalPath T (ι → ℝ)) :=
      canonicalCoefficientIntegral T c t p - canonicalCoefficientIntegral T c s p
    let ν := eulerTimeSlice (min s T) (min t T)
    Integrable (fun p => D p^n) μ ∧
    (∫ p, D p^n ∂μ) ≤ (ν.real univ)^(n-1) *
      (∫ r, ∫ p, (c r (canonicalPathEval T r p))^n ∂μ ∂ν) := by
  dsimp only
  let ν := eulerTimeSlice (min s T) (min t T)
  let f (r : ℝ≥0) (p : CanonicalPath T (ι → ℝ)) := c r (canonicalPathEval T r p)
  let D (p : CanonicalPath T (ι → ℝ)) :=
    canonicalCoefficientIntegral T c t p - canonicalCoefficientIntegral T c s p
  have hf : Continuous (Function.uncurry f) := hc.comp (continuous_fst.prodMk (continuous_joint_pathEval T))
  have hfm (p : CanonicalPath T (ι → ℝ)) : Continuous (fun r => f r p) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hD (p : CanonicalPath T (ι → ℝ)) : D p = ∫ r, f r p ∂ν :=
    canonicalCoefficientIntegral_sub_eq_slice T hc hB p hst
  have hDnorm (p : CanonicalPath T (ι → ℝ)) : ‖D p‖ ≤ B * ν.real univ := by
    rw [hD]
    exact norm_integral_le_of_norm_le_const (Eventually.of_forall fun _ => hB _ _)
  have hDm : Continuous D :=
    (continuous_canonicalCoefficientIntegral T t hc hB).sub (continuous_canonicalCoefficientIntegral T s hc hB)
  have hDmI : Integrable (fun p => D p^n) μ :=
    (integrable_const ((B * ν.real univ)^n)).mono' (hDm.pow n).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun p => by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hDnorm p) n)
  have hfMemLp (p : CanonicalPath T (ι → ℝ)) (q : ℝ≥0∞) : MemLp (fun r => f r p) q ν :=
    MemLp.of_bound (hfm p).stronglyMeasurable.aestronglyMeasurable B
      (Eventually.of_forall fun _ => hB _ _)
  have hJensen (p : CanonicalPath T (ι → ℝ)) :
      (D p)^n ≤ (ν.real univ)^(n-1) * ∫ r, (f r p)^n ∂ν := by
    rw [hD]
    rcases hn with h | h
    · subst n
      simpa only [Nat.reduceSub, pow_one] using integral_sq_le_measure_mul_sqIntegral (hfMemLp p 2)
    · subst n
      exact integral_fourth_le_measure_cube_mul_pow_four (hfMemLp p 4)
  have hJoint : Integrable (Function.uncurry (fun r p => (f r p)^n)) (ν.prod μ) :=
    (integrable_const (B^n)).mono' (hf.pow n).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        change ‖(f r.1 r.2)^n‖ ≤ B^n
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hB _ _) n)
  refine ⟨hDmI, ?_⟩
  calc
    _ ≤ ∫ p, (ν.real univ)^(n-1) * ∫ r, (f r p)^n ∂ν ∂μ :=
      integral_mono hDmI (hJoint.integral_prod_right.const_mul _) hJensen
    _ = _ := by rw [integral_const_mul, ← integral_integral_swap hJoint]

#print axioms RoughHeston.canonicalCoefficientIntegral_sub_eq_slice
#print axioms RoughHeston.integral_pow_coefficientIntegral_sub_le

end RoughHeston
