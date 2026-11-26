import EulerWeakLawExtraction
import MathFin.Probability.Brownian.Ito.ItoIntegralHorizonDense

/-! Bounded drift and covariance integrals on finite-dimensional canonical paths. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

open MathFin.ItoIntegralCLM

variable {E : Type*} [NormedAddCommGroup E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

private theorem continuous_canonicalEvalTime (T : ℝ≥0) :
    Continuous (canonicalEvalTime T) :=
  (continuous_id.min continuous_const).subtype_mk _

/-- Integrate the deterministic coefficient evaluated along the canonical
coordinate process, up to the earlier of the time and the horizon. -/
noncomputable def canonicalCoefficientIntegral (T : ℝ≥0) (b : ℝ≥0 → E → ℝ) (t : ℝ≥0)
    (p : CanonicalPath T E) : ℝ :=
  ∫ r, b r (canonicalPathEval T r p) ∂timeMeasureHorizon (min t T)

private theorem continuous_coefficient_along_path (T : ℝ≥0) {b : ℝ≥0 → E → ℝ}
    (hb : Continuous (Function.uncurry b)) (p : CanonicalPath T E) :
    Continuous (fun r => b r (canonicalPathEval T r p)) :=
  hb.comp (continuous_id.prodMk (p.continuous.comp (continuous_canonicalEvalTime T)))

/-- Drift and covariance time integrals are continuous in the uniform
canonical path topology as soon as the coefficient is continuous and bounded. -/
theorem continuous_canonicalCoefficientIntegral (T t : ℝ≥0) {b : ℝ≥0 → E → ℝ}
    (hb : Continuous (Function.uncurry b)) {B : ℝ} (hB : ∀ r x, ‖b r x‖ ≤ B) :
    Continuous (canonicalCoefficientIntegral T b t) := by
  apply continuous_of_dominated (bound := fun _ => B)
  · intro p
    exact (continuous_coefficient_along_path T hb p).stronglyMeasurable.aestronglyMeasurable
  · intro p
    exact Eventually.of_forall fun r => hB _ _
  · exact integrable_const _
  · apply Eventually.of_forall
    intro r
    exact hb.comp (continuous_const.prodMk (continuous_canonicalPathEval T r))

private theorem timeMeasureHorizon_real_univ (t : ℝ≥0) :
    (timeMeasureHorizon t).real univ = (t : ℝ) := by
  rw [measureReal_def, timeMeasureHorizon, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, MathFin.ItoIntegralL2.timeMeasure_Ioc]
  simpa only [NNReal.coe_zero, sub_zero] using ENNReal.toReal_ofReal t.coe_nonneg

theorem norm_canonicalCoefficientIntegral_le (T t : ℝ≥0) {b : ℝ≥0 → E → ℝ}
    {B : ℝ} (hB : ∀ r x, ‖b r x‖ ≤ B) (p : CanonicalPath T E) :
    ‖canonicalCoefficientIntegral T b t p‖ ≤ B * (↑(min t T) : ℝ) := by
  unfold canonicalCoefficientIntegral
  simpa only [timeMeasureHorizon_real_univ] using
    (norm_integral_le_of_norm_le_const (μ := timeMeasureHorizon (min t T))
      (Eventually.of_forall fun r => hB r (canonicalPathEval T r p)))

theorem canonicalCoefficientIntegral_stopped (T t : ℝ≥0) (b : ℝ≥0 → E → ℝ)
    (p : CanonicalPath T E) :
    canonicalCoefficientIntegral T b t (canonicalStoppedPath T t p) =
      canonicalCoefficientIntegral T b t p := by
  unfold canonicalCoefficientIntegral
  apply integral_congr_ae
  have h : ∀ᵐ r ∂timeMeasureHorizon (min t T), r ∈ Ioc 0 (min t T) :=
    ae_restrict_mem measurableSet_Ioc
  filter_upwards [h] with r hr
  congr 1
  change p (canonicalStopTime T t (canonicalEvalTime T r)) = p (canonicalEvalTime T r)
  exact congrArg p (Subtype.ext (min_eq_left ((min_le_left r T).trans (hr.2.trans (min_le_left _ _)))))

/-- The coefficient integral is adapted to the natural filtration of the
canonical coordinate process. -/
theorem stronglyAdapted_canonicalCoefficientIntegral (T : ℝ≥0) {b : ℝ≥0 → E → ℝ}
    (hb : Continuous (Function.uncurry b)) {B : ℝ} (hB : ∀ r x, ‖b r x‖ ≤ B) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := E) T) (canonicalCoefficientIntegral T b) := by
  intro t
  rw [canonicalPathNaturalFiltration_eq_comap_stopped]
  apply Measurable.stronglyMeasurable
  have h := ((continuous_canonicalCoefficientIntegral T t hb hB).measurable.comp
    (comap_measurable (canonicalStoppedPath (E := E) T t)))
  convert h using 1
  funext p
  exact (canonicalCoefficientIntegral_stopped T t b p).symm

/-- The drift-subtracted coordinate observable used in finite-dimensional
martingale problem tests. -/
noncomputable def canonicalEulerMartingaleCoordinate {ι : Type*} [Fintype ι]
    (T : ℝ≥0) (b : ℝ≥0 → (ι → ℝ) → ι → ℝ) (x : ι → ℝ) (i : ι) (t : ℝ≥0)
    (p : CanonicalPath T (ι → ℝ)) : ℝ :=
  canonicalPathEval T t p i - x i -
    canonicalCoefficientIntegral T (fun r y => b r y i) t p

theorem continuous_canonicalEulerMartingaleCoordinate {ι : Type*} [Fintype ι]
    (T t : ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    {B : ℝ} (hB : ∀ r y, ‖b r y i‖ ≤ B) :
    Continuous (canonicalEulerMartingaleCoordinate T b x i t) :=
  (((continuous_apply i).comp (continuous_canonicalPathEval T t)).sub continuous_const).sub
    (continuous_canonicalCoefficientIntegral T t hb hB)

theorem stronglyAdapted_canonicalEulerMartingaleCoordinate {ι : Type*} [Fintype ι]
    (T : ℝ≥0) {b : ℝ≥0 → (ι → ℝ) → ι → ℝ} (x : ι → ℝ) (i : ι)
    (hb : Continuous (fun z : ℝ≥0 × (ι → ℝ) => b z.1 z.2 i))
    {B : ℝ} (hB : ∀ r y, ‖b r y i‖ ≤ B) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := ι → ℝ) T)
      (canonicalEulerMartingaleCoordinate T b x i) := by
  intro t
  have h := stronglyAdapted_canonicalCoefficientIntegral T hb hB t
  have he : Measurable[canonicalPathNaturalFiltration (E := ι → ℝ) T t]
      (fun p => canonicalPathEval T t p i) := by
    rw [canonicalPathNaturalFiltration_eq_comap_stopped]
    have hm := ((measurable_pi_apply i).comp (continuous_canonicalPathEval T t).measurable).comp
      (comap_measurable (canonicalStoppedPath (E := ι → ℝ) T t))
    convert hm using 1
    funext p
    change p (canonicalEvalTime T t) i = p (canonicalStopTime T t (canonicalEvalTime T t)) i
    have ht : canonicalStopTime T t (canonicalEvalTime T t) = canonicalEvalTime T t :=
      Subtype.ext (min_eq_left (min_le_left t T))
    exact congrArg (fun u : CanonicalPathTime T => p u i) ht.symm
  exact (he.stronglyMeasurable.sub stronglyMeasurable_const).sub h

#print axioms RoughHeston.continuous_canonicalCoefficientIntegral
#print axioms RoughHeston.stronglyAdapted_canonicalCoefficientIntegral
#print axioms RoughHeston.norm_canonicalCoefficientIntegral_le
#print axioms RoughHeston.continuous_canonicalEulerMartingaleCoordinate
#print axioms RoughHeston.stronglyAdapted_canonicalEulerMartingaleCoordinate

end RoughHeston
