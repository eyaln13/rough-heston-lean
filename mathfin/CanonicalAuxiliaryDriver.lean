import CommonDriverLimit
import MathFin.Probability.Brownian.BrownianMartingale

/-!
The canonical construction supplies the auxiliary unit-clock martingale
for the independent enlargement.
-/

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory ProbabilityTheory NNReal

namespace RoughHeston

/-- The natural filtration of the canonical Brownian motion under
`ProbabilityTheory.gaussianLimit`. -/
noncomputable def canonicalAuxiliaryFiltration :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) :=
  Filtration.natural brownian (fun t => (measurable_brownian t).stronglyMeasurable)

/-- The canonical Brownian motion, frozen at `T`, has the unit clock
up to `T` and continuous paths. -/
theorem canonical_auxiliary_driver (T : ℝ≥0) :
    let W (t : ℝ≥0) := brownian (min t T)
    Martingale W canonicalAuxiliaryFiltration gaussianLimit ∧
    (∀ t, MemLp (W t) 2 gaussianLimit) ∧
    (W 0 =ᵐ[gaussianLimit] 0) ∧
    (∀ ω, Continuous (fun t => W t ω)) ∧
    Martingale (fun t ω => W t ω ^ 2 - ((min t T : ℝ≥0) : ℝ))
      canonicalAuxiliaryFiltration gaussianLimit := by
  have hB := isBrownianReal_brownian.toIsPreBrownianReal
  let _ : IsFilteredPreBrownian brownian canonicalAuxiliaryFiltration gaussianLimit :=
    hB.isFilteredPreBrownian measurable_brownian
  have hm := IsPreBrownianReal.isMartingale brownian canonicalAuxiliaryFiltration gaussianLimit
  have hsq := IsFilteredPreBrownian.squareSubTime_isMartingale
    (X := brownian) (𝓕 := canonicalAuxiliaryFiltration) (P := gaussianLimit)
  refine ⟨martingale_freeze_at hm T, fun t => ?_, ?_, fun ω => ?_,
    martingale_freeze_at hsq T⟩
  · exact hasLaw_brownian_eval.memLp (memLp_id_gaussianReal 2)
  · filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
    change brownian (min 0 T) ω = 0
    rw [min_eq_left (show 0 ≤ T from zero_le), hω]
  · exact (continuous_brownian ω).comp (continuous_id.min continuous_const)

end RoughHeston

#print axioms RoughHeston.canonical_auxiliary_driver
