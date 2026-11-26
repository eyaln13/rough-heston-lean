import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Probability.Process.Adapted
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! The natural past of a canonical continuous path is encoded by its
stopped path, a continuous map on the canonical path space. -/

open Set MeasureTheory MeasurableSpace TopologicalSpace
open scoped NNReal

namespace RoughHeston

/-- The time interval indexing the canonical continuous paths. -/
abbrev CanonicalPathTime (T : ℝ≥0) := Icc (0 : ℝ≥0) T

/-- Canonical continuous path space. Taking a product-valued state gives
the canonical space of two continuous coordinate paths. -/
abbrev CanonicalPath (T : ℝ≥0) (E : Type*) [TopologicalSpace E] :=
  C(CanonicalPathTime T, E)

/-- An observation time is held fixed at the horizon after it ends. -/
def canonicalEvalTime (T t : ℝ≥0) : CanonicalPathTime T :=
  ⟨min t T, ⟨zero_le, min_le_right _ _⟩⟩

/-- Stop a time within the horizon at the deterministic time s. -/
def canonicalStopTime (T s : ℝ≥0) : C(CanonicalPathTime T, CanonicalPathTime T) where
  toFun t := ⟨min t.val s, ⟨zero_le, (min_le_left _ _).trans t.property.2⟩⟩
  continuous_toFun := (continuous_subtype_val.min continuous_const).subtype_mk _

variable {E : Type*} [TopologicalSpace E]

/-- The canonical coordinate process, extended constantly after the horizon. -/
def canonicalPathEval (T t : ℝ≥0) (p : CanonicalPath T E) : E :=
  p (canonicalEvalTime T t)

theorem continuous_canonicalPathEval (T t : ℝ≥0) :
    Continuous (canonicalPathEval (E := E) T t) :=
  continuous_eval_const (canonicalEvalTime T t)

/-- The statistic recording the path up to s and then holding it constant. -/
def canonicalStoppedPath (T s : ℝ≥0) (p : CanonicalPath T E) : CanonicalPath T E :=
  p.comp (canonicalStopTime T s)

theorem continuous_canonicalStoppedPath (T s : ℝ≥0) :
    Continuous (canonicalStoppedPath (E := E) T s) :=
  ContinuousMap.continuous_precomp (canonicalStopTime T s)

variable [MetrizableSpace E] [SecondCountableTopology E] [RegularSpace E]
  [MeasurableSpace E] [BorelSpace E]

/-- Natural filtration of the canonical coordinate process. -/
def canonicalPathNaturalFiltration (T : ℝ≥0) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace (CanonicalPath T E)) :=
  Filtration.natural (canonicalPathEval T) (fun t =>
    (ContinuousMap.measurable_eval (canonicalEvalTime T t)).stronglyMeasurable)

/-- The natural filtration at s is the σ-algebra pulled back along the
stopped canonical path. -/
theorem canonicalPathNaturalFiltration_eq_comap_stopped (T s : ℝ≥0) :
    canonicalPathNaturalFiltration (E := E) T s =
      MeasurableSpace.comap (canonicalStoppedPath (E := E) T s) inferInstance := by
  change (⨆ j ≤ s, MeasurableSpace.comap (canonicalPathEval (E := E) T j) inferInstance) = _
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.comap_iSup]
  simp only [MeasurableSpace.comap_comp, Function.comp_def]
  apply le_antisymm
  · refine iSup₂_le fun j hj => ?_
    refine le_iSup_of_le (canonicalEvalTime T j) ?_
    have he : (fun p : CanonicalPath T E => canonicalStoppedPath T s p (canonicalEvalTime T j)) =
        canonicalPathEval T j := by
      funext p
      exact congrArg p (Subtype.ext (min_eq_left ((min_le_left j T).trans hj)))
    rw [he]
  · refine iSup_le fun t => ?_
    let j := min t.val s
    have he : (fun p : CanonicalPath T E => canonicalStoppedPath T s p t) =
        canonicalPathEval T j := by
      funext p
      exact congrArg p (Subtype.ext (min_eq_left ((min_le_left t.val s).trans t.property.2)).symm)
    rw [he]
    exact le_iSup₂_of_le j (min_le_right _ _) le_rfl

end RoughHeston

#print axioms RoughHeston.continuous_canonicalStoppedPath
#print axioms RoughHeston.canonicalPathNaturalFiltration_eq_comap_stopped
#print axioms RoughHeston.continuous_canonicalPathEval
