import CanonicalPairPath
import Verification

/-! Uniform separation is a closed event on canonical pair paths and
passes to weak limits under a uniform positive probability bound. -/

open MeasureTheory Filter Set
open scoped MeasureTheory Topology NNReal ENNReal

namespace RoughHeston

private def pairDifference : C(ℝ × ℝ, ℝ) :=
  ⟨fun x => x.1 - x.2, continuous_fst.sub continuous_snd⟩

/-- The sup norm of the difference of the two coordinate paths. -/
noncomputable def canonicalPairGap (T : ℝ≥0) (p : CanonicalPath T (ℝ × ℝ)) : ℝ :=
  ‖pairDifference.comp p‖

theorem canonicalPairGap_eq_iSup (T : ℝ≥0) (p : CanonicalPath T (ℝ × ℝ)) :
    canonicalPairGap T p = ⨆ t : CanonicalPathTime T, |(p t).1 - (p t).2| := by
  rw [canonicalPairGap, ContinuousMap.norm_eq_iSup_norm]
  simp only [ContinuousMap.comp_apply, pairDifference, ContinuousMap.coe_mk, Real.norm_eq_abs]

theorem continuous_canonicalPairGap (T : ℝ≥0) : Continuous (canonicalPairGap T) :=
  continuous_norm.comp (ContinuousMap.continuous_postcomp pairDifference)

/-- Uniform separation at a fixed level is a closed set. -/
theorem isClosed_canonicalPairSeparation (T : ℝ≥0) (ℓ : ℝ) :
    IsClosed {p : CanonicalPath T (ℝ × ℝ) | ℓ ≤ canonicalPairGap T p} :=
  isClosed_le continuous_const (continuous_canonicalPairGap T)

/-- A strictly positive uniform separation forces a time where the
two canonical coordinates differ. -/
theorem exists_time_different_of_canonicalPairGap {T : ℝ≥0} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {p : CanonicalPath T (ℝ × ℝ)} (hp : ℓ ≤ canonicalPairGap T p) :
    ∃ t : ℝ≥0, t ≤ T ∧ (canonicalPathEval T t p).1 ≠ (canonicalPathEval T t p).2 := by
  by_contra h
  push Not at h
  have hz : pairDifference.comp p = 0 := by
    ext t
    have he : canonicalEvalTime T t.val = t := Subtype.ext (min_eq_left t.property.2)
    change (p t).1 - (p t).2 = 0
    apply sub_eq_zero.mpr
    have ht := h t.val t.property.2
    change (p (canonicalEvalTime T t.val)).1 = (p (canonicalEvalTime T t.val)).2 at ht
    rwa [he] at ht
  have he : canonicalPairGap T p = 0 := by rw [canonicalPairGap, hz, norm_zero]
  exact (not_le_of_gt hℓ) (he ▸ hp)

/-- A probability bound for a fixed closed separation event passes to
the canonical weak limit. -/
theorem canonicalPairSeparation_of_weak_limit {T : ℝ≥0}
    {Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    {P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    (hweak : Tendsto Pn atTop (𝓝 P)) {ℓ : ℝ} {p : ENNReal}
    (hp : ∀ n, p ≤ (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {q | ℓ ≤ canonicalPairGap T q}) :
    p ≤ (P : Measure (CanonicalPath T (ℝ × ℝ))) {q | ℓ ≤ canonicalPairGap T q} := by
  exact separation_of_weak_limit
    ((ProbabilityMeasure.toFiniteMeasure_continuous.tendsto P).comp hweak)
    (continuous_canonicalPairGap T) hp

/-- A uniform positive gap in the approximations implies positive
pathwise separation in the weak limit. -/
theorem canonicalPairDifferent_of_weak_limit {T : ℝ≥0}
    {Pn : ℕ → ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    {P : ProbabilityMeasure (CanonicalPath T (ℝ × ℝ))}
    (hweak : Tendsto Pn atTop (𝓝 P)) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {p : ENNReal} (hp₀ : 0 < p)
    (hp : ∀ n, p ≤ (Pn n : Measure (CanonicalPath T (ℝ × ℝ)))
      {q | ℓ ≤ canonicalPairGap T q}) :
    0 < (P : Measure (CanonicalPath T (ℝ × ℝ)))
      {q | ∃ t : ℝ≥0, t ≤ T ∧ (canonicalPathEval T t q).1 ≠ (canonicalPathEval T t q).2} :=
  hp₀.trans_le ((canonicalPairSeparation_of_weak_limit hweak hp).trans
    (measure_mono fun _ hq => exists_time_different_of_canonicalPairGap hℓ hq))

end RoughHeston

#print axioms RoughHeston.canonicalPairGap_eq_iSup
#print axioms RoughHeston.isClosed_canonicalPairSeparation
#print axioms RoughHeston.exists_time_different_of_canonicalPairGap
#print axioms RoughHeston.canonicalPairSeparation_of_weak_limit
#print axioms RoughHeston.canonicalPairDifferent_of_weak_limit
