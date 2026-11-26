import FractionalSmoothRowMomentData
import CanonicalMartingalePushforward
import CanonicalPathIntegrals

/-! Projection to the fixed path space of physical variances and
their normalized residual martingales. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

open MathFin.ItoIntegralCLM

set_option maxHeartbeats 1100000

abbrev CoupledPhysicalState (ι : Type*) := (Option ι → ℝ) × (Option ι → ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {T : ℝ≥0} {α κ σ : ℝ} {n : ℕ} {v : Option ι → ℝ} {β : Option ι → ℝ≥0 → ℝ}

def canonicalPhysicalVariance (T : ℝ≥0) (i : Option ι) (t : ℝ≥0)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  (canonicalPathEval T t p).1 i

def canonicalPhysicalResidual (T : ℝ≥0) (i : Option ι) (t : ℝ≥0)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : ℝ :=
  (canonicalPathEval T t p).2 i

noncomputable def canonicalPhysicalCompensator (T : ℝ≥0) (σ : ℝ) (i j : Option ι) :=
  canonicalCoefficientIntegral T (fun _ (z : CoupledPhysicalState ι) => physicalCouplingDensity σ i j z.1)

theorem continuous_canonicalPhysicalCompensator (T : ℝ≥0) (σ : ℝ) (i j : Option ι) (t : ℝ≥0) :
    Continuous (canonicalPhysicalCompensator T σ i j t) := by
  let g : C(CoupledPhysicalState ι, ℝ) := ⟨fun z => physicalCouplingDensity σ i j z.1,
    (continuous_physicalCouplingDensity σ i j).comp continuous_fst⟩
  have hT : Continuous (canonicalEvalTime T) := (continuous_id.min continuous_const).subtype_mk _
  have h := (continuous_weighted_path_integral (ν := timeMeasureHorizon (min t T))
    hT.measurable (integrable_const (1 : ℝ))).comp (ContinuousMap.continuous_postcomp g)
  convert h using 1
  funext p
  simp only [canonicalPhysicalCompensator, canonicalCoefficientIntegral, Function.comp_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, g, one_mul, canonicalPathEval]

theorem stronglyAdapted_canonicalPhysicalCompensator (T : ℝ≥0) (σ : ℝ) (i j : Option ι) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T)
      (canonicalPhysicalCompensator T σ i j) :=
  stronglyAdapted_canonical_of_stoppedPath (continuous_canonicalPhysicalCompensator T σ i j)
    (fun _ p => canonicalCoefficientIntegral_stopped T _ _ p)

theorem stronglyAdapted_canonicalPhysicalResidual (T : ℝ≥0) (i : Option ι) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T)
      (canonicalPhysicalResidual T i) := by
  have ha : StronglyAdapted (canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T)
      (canonicalPathEval T) := Filtration.stronglyAdapted_natural (fun t =>
        (ContinuousMap.measurable_eval (canonicalEvalTime T t)).stronglyMeasurable)
  exact fun t => ((continuous_apply i).comp continuous_snd).comp_stronglyMeasurable (ha t)

namespace FractionalCoupledSmoothLaw

variable (L : FractionalCoupledSmoothLaw T α n κ σ v β)
  {B : ℝ} (hB : 0 ≤ B) (hβ : ∀ i, Measurable (β i)) (hβB : ∀ i t, ‖β i t‖ ≤ B)

/-- Record all the focal rows, the initial cluster and Y, jointly. -/
noncomputable def fixedPhysicalPath (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
    CanonicalPath T (CoupledPhysicalState ι) where
  toFun t := (fun i => L.variance i t p, fun i => L.residual i t p)
  continuous_toFun := ((continuous_pi fun i => L.variance_continuous_time i hB hβ hβB p).prodMk
    (continuous_pi fun i => L.residual_continuous_time i hB hβ hβB p)).comp continuous_subtype_val

private theorem canonicalPathEval_min (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) (t : ℝ≥0) :
    canonicalPathEval T (min t T) p = canonicalPathEval T t p := by
  unfold canonicalPathEval
  congr 1
  apply Subtype.ext
  exact min_eq_left (min_le_right _ _)

theorem canonicalPathEval_fixedPhysicalPath (t : ℝ≥0)
    (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
    canonicalPathEval T t (L.fixedPhysicalPath hB hβ hβB p) =
      (fun i => L.variance i t p, fun i => L.residual i t p) := by
  have ht : min (min t T) T = min t T := min_eq_left (min_le_right _ _)
  have h := canonicalPathEval_min p t
  apply Prod.ext <;> funext i
  · simp only [canonicalPathEval, fixedPhysicalPath, ContinuousMap.coe_mk]
    change L.variance i (min t T) p = L.variance i t p
    have hg : smoothCoupledImmigrationPrimitive (η := Fin (fractionalApproximationOrder n)) T
        (fractionalExponentialApproximation α n 0) β (min t T) =
      smoothCoupledImmigrationPrimitive T (fractionalExponentialApproximation α n 0) β t := by
      funext k
      simp only [smoothCoupledImmigrationPrimitive, ht]
    simp only [variance, fractionalCoupledSmoothPath, smoothCoupledPath, translatedCanonicalState, h, hg]
  · simp only [canonicalPathEval, fixedPhysicalPath, ContinuousMap.coe_mk]
    change L.residual i (min t T) p = L.residual i t p
    simp only [residual, smoothCoupledMartingale, canonicalEulerMartingaleCoordinate,
      canonicalCoefficientIntegral, ht, h]

theorem stronglyAdapted_physical_pair :
    StronglyAdapted (canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T)
      (fun t p => (fun i => L.variance i t p, fun i => L.residual i t p)) := by
  have hV := stronglyAdapted_translatedCanonicalState T
    (smoothCoupledImmigrationPrimitive (η := Fin (fractionalApproximationOrder n)) T
      (fractionalExponentialApproximation α n 0) β)
  intro t
  let : MeasurableSpace (CanonicalPath T (FractionalCoupledSmoothState ι n)) :=
    canonicalPathNaturalFiltration T t
  apply StronglyMeasurable.prodMk
  · have h : Measurable[canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T t]
        (fun p i => L.variance i t p) := by
      apply Measurable.of_eval
      intro i
      exact ((continuous_apply (i, none)).comp_stronglyMeasurable (hV t)).measurable
    exact h.stronglyMeasurable
  · have h : Measurable[canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T t]
        (fun p i => L.residual i t p) := by
      apply Measurable.of_eval
      intro i
      exact ((L.residual_martingale i).stronglyAdapted t).measurable
    exact h.stronglyMeasurable

theorem measurable_fixedPhysicalPath : Measurable (L.fixedPhysicalPath hB hβ hβB) := by
  apply measurable_canonicalPath_of_evaluations
  intro t
  have h := (L.stronglyAdapted_physical_pair t).measurable
  exact h.mono ((canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T).le t) le_rfl

theorem filtration_measurable_fixedPhysicalPath (t : ℝ≥0) :
    Measurable[canonicalPathNaturalFiltration (E := FractionalCoupledSmoothState ι n) T t,
      canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T t] (L.fixedPhysicalPath hB hβ hβB) := by
  apply filtration_measurable_canonicalPath_of_adapted
  intro s
  simp_rw [L.canonicalPathEval_fixedPhysicalPath hB hβ hβB]
  exact (L.stronglyAdapted_physical_pair s).measurable

/-- The law now lives on a single fixed-dimensional path space for all n. -/
noncomputable def fixedPhysicalLaw : ProbabilityMeasure (CanonicalPath T (CoupledPhysicalState ι)) :=
  ProbabilityMeasure.map L.law (L.fixedPhysicalPath hB hβ hβB)

theorem fixedPhysical_residual_martingale (i : Option ι) :
    Martingale (canonicalPhysicalResidual T i) (canonicalPathNaturalFiltration T)
      (L.fixedPhysicalLaw hB hβ hβB : Measure _) := by
  apply martingale_measure_map_of_filtration_measurable (L.measurable_fixedPhysicalPath hB hβ hβB)
    (L.filtration_measurable_fixedPhysicalPath hB hβ hβB) (stronglyAdapted_canonicalPhysicalResidual T i)
  simp_rw [canonicalPhysicalResidual, L.canonicalPathEval_fixedPhysicalPath hB hβ hβB]
  exact L.residual_martingale i

theorem fixedPhysical_compensatedProduct_martingale
    (hK : fractionalExponentialApproximation α n 0 ≠ 0) (i j : Option ι) :
    Martingale (fun t => canonicalPhysicalResidual T i t * canonicalPhysicalResidual T j t -
      canonicalPhysicalCompensator T σ i j t) (canonicalPathNaturalFiltration T)
      (L.fixedPhysicalLaw hB hβ hβB : Measure _) := by
  have hMeas : StronglyAdapted (canonicalPathNaturalFiltration (E := CoupledPhysicalState ι) T)
      (fun t => canonicalPhysicalResidual T i t * canonicalPhysicalResidual T j t -
        canonicalPhysicalCompensator T σ i j t) :=
    fun t => ((stronglyAdapted_canonicalPhysicalResidual T i t).mul
      (stronglyAdapted_canonicalPhysicalResidual T j t)).sub
      (stronglyAdapted_canonicalPhysicalCompensator T σ i j t)
  apply martingale_measure_map_of_filtration_measurable (L.measurable_fixedPhysicalPath hB hβ hβB)
    (L.filtration_measurable_fixedPhysicalPath hB hβ hβB) hMeas
  have hPull (t : ℝ≥0) (p : CanonicalPath T (FractionalCoupledSmoothState ι n)) :
      canonicalPhysicalCompensator T σ i j t (L.fixedPhysicalPath hB hβ hβB p) =
        L.compensator i j t p := by
    simp_rw [canonicalPhysicalCompensator, canonicalCoefficientIntegral, compensator,
      L.canonicalPathEval_fixedPhysicalPath hB hβ hβB]
  simp_rw [Pi.sub_apply, Pi.mul_apply, canonicalPhysicalResidual, hPull,
    L.canonicalPathEval_fixedPhysicalPath hB hβ hβB]
  exact L.compensatedProduct_martingale hK i j

end FractionalCoupledSmoothLaw

#print axioms RoughHeston.FractionalCoupledSmoothLaw.fixedPhysical_residual_martingale
#print axioms RoughHeston.FractionalCoupledSmoothLaw.fixedPhysical_compensatedProduct_martingale

end RoughHeston
