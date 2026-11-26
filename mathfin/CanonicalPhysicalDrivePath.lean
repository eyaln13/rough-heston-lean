import FractionalCoupledPathLaw

/-! Canonical continuous path primitives and the cumulative physical
drive, with the deterministic measurable immigration kept explicit. -/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology Interval

namespace RoughHeston

set_option maxHeartbeats 700000

/-- The time primitive of a canonical scalar path on the same horizon. -/
noncomputable def canonicalScalarPrimitive (T : ℝ≥0) (p : CanonicalPath T ℝ) : CanonicalPath T ℝ where
  toFun t := ∫ r in (0 : ℝ)..(t.val : ℝ), p (realTimeOnHorizon T r)
  continuous_toFun := by
    have h := (intervalIntegral.differentiable_integral_of_continuous (a := 0)
      (p.continuous.comp (realTimeOnHorizon T).continuous)).continuous
    exact h.comp (NNReal.continuous_coe.comp continuous_subtype_val)

theorem continuous_canonicalScalarPrimitive (T : ℝ≥0) :
    Continuous (canonicalScalarPrimitive T) := by
  let : Nonempty (CanonicalPathTime T) := ⟨canonicalEvalTime T 0⟩
  refine LipschitzWith.continuous (K := T) (LipschitzWith.of_dist_le_mul ?_)
  intro p q
  apply (ContinuousMap.dist_le_iff_of_nonempty).2
  intro t
  let f (r : ℝ) := p (realTimeOnHorizon T r)
  let g (r : ℝ) := q (realTimeOnHorizon T r)
  have hf : Continuous f := p.continuous.comp (realTimeOnHorizon T).continuous
  have hg : Continuous g := q.continuous.comp (realTimeOnHorizon T).continuous
  change dist (∫ r in (0 : ℝ)..(t.val : ℝ), f r)
    (∫ r in (0 : ℝ)..(t.val : ℝ), g r) ≤ (T : ℝ)*dist p q
  rw [dist_eq_norm, ← intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  have hB (r : ℝ) : ‖f r-g r‖ ≤ dist p q := by
    rw [← dist_eq_norm]
    exact ContinuousMap.dist_apply_le_dist (realTimeOnHorizon T r)
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ))
    (b := (t.val : ℝ)) (f := fun r => f r-g r) (C := dist p q) (fun r _ => hB r)
  refine hi.trans ?_
  rw [sub_zero, abs_of_nonneg t.val.coe_nonneg, mul_comm (dist p q)]
  exact mul_le_mul_of_nonneg_right (NNReal.coe_le_coe.mpr t.property.2) dist_nonneg

/-- Bounded measurable deterministic forcing has a continuous primitive
and can be stored as a fixed canonical path. -/
noncomputable def canonicalForcingPrimitive (T : ℝ≥0) {b : ℝ≥0 → ℝ} {B : ℝ}
    (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B) : CanonicalPath T ℝ where
  toFun t := ∫ r in (0 : ℝ)..(t.val : ℝ), b r.toNNReal
  continuous_toFun := by
    have hi (a c : ℝ) : IntervalIntegrable (fun r : ℝ => b r.toNNReal) volume a c := by
      rw [intervalIntegrable_iff]
      have hconst : IntervalIntegrable (fun _ : ℝ => B) volume a c := intervalIntegrable_const
      rw [intervalIntegrable_iff] at hconst
      exact hconst.mono' (hb.comp continuous_real_toNNReal.measurable).stronglyMeasurable.aestronglyMeasurable
        (Eventually.of_forall fun r => hB r.toNNReal)
    exact (intervalIntegral.continuous_primitive hi 0).comp
      (NNReal.continuous_coe.comp continuous_subtype_val)

variable {ι : Type*} [Fintype ι]

def canonicalPhysicalVariancePath (T : ℝ≥0) (i : Option ι) :
    CanonicalPath T (CoupledPhysicalState ι) → CanonicalPath T ℝ :=
  ContinuousMap.comp ⟨fun z => z.1 i, (continuous_apply i).comp continuous_fst⟩

def canonicalPhysicalResidualPath (T : ℝ≥0) (i : Option ι) :
    CanonicalPath T (CoupledPhysicalState ι) → CanonicalPath T ℝ :=
  ContinuousMap.comp ⟨fun z => z.2 i, (continuous_apply i).comp continuous_snd⟩

theorem continuous_canonicalPhysicalVariancePath (T : ℝ≥0) (i : Option ι) :
    Continuous (canonicalPhysicalVariancePath T i) := ContinuousMap.continuous_postcomp _

theorem continuous_canonicalPhysicalResidualPath (T : ℝ≥0) (i : Option ι) :
    Continuous (canonicalPhysicalResidualPath T i) := ContinuousMap.continuous_postcomp _

/-- The cumulative drive is the nominal continuous martingale plus the
known immigration primitive minus the mean-reversion primitive. -/
noncomputable def canonicalPhysicalDrivePath (T : ℝ≥0) (κ : ℝ) (i : Option ι)
    {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    (p : CanonicalPath T (CoupledPhysicalState ι)) : CanonicalPath T ℝ :=
  canonicalPhysicalResidualPath T i p + canonicalForcingPrimitive T hb hB -
    κ • canonicalScalarPrimitive T (canonicalPhysicalVariancePath T i p)

theorem continuous_canonicalPhysicalDrivePath (T : ℝ≥0) (κ : ℝ) (i : Option ι)
    {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B) :
    Continuous (canonicalPhysicalDrivePath T κ i hb hB) :=
  ((continuous_canonicalPhysicalResidualPath T i).add continuous_const).sub
    ((continuous_canonicalScalarPrimitive T).comp (continuous_canonicalPhysicalVariancePath T i) |>.const_smul κ)

theorem canonicalPhysicalDrivePath_apply (T : ℝ≥0) (κ : ℝ) (i : Option ι)
    {b : ℝ≥0 → ℝ} {B : ℝ} (hb : Measurable b) (hB : ∀ t, ‖b t‖ ≤ B)
    (p : CanonicalPath T (CoupledPhysicalState ι)) (t : CanonicalPathTime T) :
    canonicalPhysicalDrivePath T κ i hb hB p t =
      canonicalPhysicalResidual T i t p +
        ∫ r in (0 : ℝ)..(t.val : ℝ), (b r.toNNReal - κ*canonicalPhysicalVariance T i r.toNNReal p) := by
  let f (r : ℝ) := b r.toNNReal
  let g (r : ℝ) := canonicalPhysicalVariance T i r.toNNReal p
  have hf : IntervalIntegrable f volume 0 (t.val : ℝ) := by
    rw [intervalIntegrable_iff]
    have hconst : IntervalIntegrable (fun _ : ℝ => B) volume 0 (t.val : ℝ) := intervalIntegrable_const
    rw [intervalIntegrable_iff] at hconst
    exact hconst.mono' (hb.comp continuous_real_toNNReal.measurable).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall fun r => hB r.toNNReal)
  have hg : Continuous g := ((continuous_apply i).comp continuous_fst).comp
    (p.continuous.comp (realTimeOnHorizon T).continuous)
  have hgi : IntervalIntegrable (fun r => κ*g r) volume 0 (t.val : ℝ) :=
    (continuous_const.mul hg).intervalIntegrable _ _
  change (p t).2 i + (∫ r in (0 : ℝ)..(t.val : ℝ), f r) -
    κ*(∫ r in (0 : ℝ)..(t.val : ℝ), g r) =
      canonicalPhysicalResidual T i t p + ∫ r in (0 : ℝ)..(t.val : ℝ), (f r-κ*g r)
  rw [intervalIntegral.integral_sub hf hgi, intervalIntegral.integral_const_mul]
  have ht : canonicalEvalTime T t = t := Subtype.ext (min_eq_left t.property.2)
  simp only [canonicalPhysicalResidual, canonicalPathEval, ht]
  ring

#print axioms RoughHeston.continuous_canonicalScalarPrimitive
#print axioms RoughHeston.continuous_canonicalPhysicalDrivePath
#print axioms RoughHeston.canonicalPhysicalDrivePath_apply

end RoughHeston
