import FractionalKernelL1
import CanonicalPairPath

open MeasureTheory Set
open scoped MeasureTheory NNReal Topology

namespace RoughHeston

private theorem integrable_weight_mul_path_eval
    {S I : Type*} [MeasurableSpace S] [TopologicalSpace I] [CompactSpace I]
    [MeasurableSpace I] [OpensMeasurableSpace I] {ν : Measure S}
    {q : S → I} (hq : Measurable q) {w : S → ℝ} (hw : Integrable w ν)
    (p : C(I, ℝ)) : Integrable (fun s => w s * p (q s)) ν := by
  apply (hw.norm.mul_const (dist p (ContinuousMap.const I 0))).mono
    (hw.aestronglyMeasurable.mul (p.continuous.measurable.comp hq).aestronglyMeasurable)
  apply ae_of_all
  intro s
  change ‖w s * p (q s)‖ ≤ ‖‖w s‖ * dist p (ContinuousMap.const I 0)‖
  have h := ContinuousMap.dist_apply_le_dist (f := p) (g := ContinuousMap.const I 0) (q s)
  rw [ContinuousMap.const_apply, dist_zero_right] at h
  rw [norm_mul, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) dist_nonneg)]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg _)

/-- A fixed (L^1) time weight gives a continuous linear functional
in the uniform topology on paths. -/
theorem continuous_weighted_path_integral
    {S I : Type*} [MeasurableSpace S] [TopologicalSpace I] [CompactSpace I]
    [MeasurableSpace I] [OpensMeasurableSpace I] {ν : Measure S}
    {q : S → I} (hq : Measurable q) {w : S → ℝ} (hw : Integrable w ν) :
    Continuous (fun p : C(I, ℝ) => ∫ s, w s * p (q s) ∂ν) := by
  refine LipschitzWith.continuous (K := Real.toNNReal (∫ s, ‖w s‖ ∂ν)) ?_
  refine LipschitzWith.of_dist_le_mul fun p r => ?_
  change dist (∫ s, w s * p (q s) ∂ν) (∫ s, w s * r (q s) ∂ν) ≤
    ((Real.toNNReal (∫ s, ‖w s‖ ∂ν)) : ℝ) * dist p r
  rw [Real.coe_toNNReal', max_eq_left (integral_nonneg fun s => norm_nonneg (w s)), Real.dist_eq,
    ← integral_sub (integrable_weight_mul_path_eval hq hw p)
      (integrable_weight_mul_path_eval hq hw r), ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ s, ‖w s * p (q s) - w s * r (q s)‖ ∂ν :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ s, ‖w s‖ * dist p r ∂ν := by
      apply integral_mono ((integrable_weight_mul_path_eval hq hw p).sub
        (integrable_weight_mul_path_eval hq hw r)).norm (hw.norm.mul_const _)
      intro s
      change ‖w s * p (q s) - w s * r (q s)‖ ≤ ‖w s‖ * dist p r
      rw [← mul_sub, norm_mul]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Real.dist_eq, Real.norm_eq_abs] using
        (ContinuousMap.dist_apply_le_dist (f := p) (g := r) (q s))
    _ = _ := by rw [integral_mul_const]

/-- Evaluate a finite-horizon path at a real time, clamping that time
to the observed interval. -/
def realTimeOnHorizon (T : ℝ≥0) : C(ℝ, CanonicalPathTime T) where
  toFun s := canonicalEvalTime T s.toNNReal
  continuous_toFun := (continuous_real_toNNReal.min continuous_const).subtype_mk _

/-- The reconstructed martingale at a fixed time is a continuous
functional of the variance path in the uniform topology. -/
noncomputable def recoveredVarianceMartingale (T : ℝ≥0)
    (α v₀ κ θ t : ℝ) (p : CanonicalPath T ℝ) : ℝ :=
  (∫ s in Ioc (0 : ℝ) t, fractionalL α (t - s) * (p (realTimeOnHorizon T s) - v₀)) -
    κ * θ * t + κ * (∫ s in Ioc (0 : ℝ) t, p (realTimeOnHorizon T s))

theorem continuous_recoveredVarianceMartingale (T : ℝ≥0)
    {α : ℝ} (hα : α < 1) (v₀ κ θ : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Continuous (recoveredVarianceMartingale T α v₀ κ θ t) := by
  let q := realTimeOnHorizon T
  let offset : C(ℝ, ℝ) := ⟨fun x => x - v₀, continuous_id.sub continuous_const⟩
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  have hw : Integrable (fun s : ℝ => fractionalL α (t - s)) ν :=
    fractionalL_reflected_integrableOn_Ioc hα ht
  have hv : Integrable (fun _ : ℝ => (1 : ℝ)) ν := integrable_const _
  have hfirst := (continuous_weighted_path_integral q.continuous.measurable hw).comp
    (ContinuousMap.continuous_postcomp offset :
      Continuous (offset.comp : CanonicalPath T ℝ → CanonicalPath T ℝ))
  have hsecond := continuous_weighted_path_integral q.continuous.measurable hv
  convert (hfirst.sub (continuous_const (y := κ * θ * t))).add
      ((continuous_const (y := κ)).mul hsecond) using 1
  funext p
  simp only [recoveredVarianceMartingale, Function.comp_def, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, ν, offset, q, one_mul]

/-- The time integral of any continuous function of the two coordinates
is continuous on the pair path space. This includes the three rank-one
compensators. -/
theorem continuous_pair_path_time_integral (T : ℝ≥0)
    (t : ℝ) (f : C(ℝ × ℝ, ℝ)) :
    Continuous (fun p : CanonicalPath T (ℝ × ℝ) =>
      ∫ s in Ioc (0 : ℝ) t, f (p (realTimeOnHorizon T s))) := by
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  have hv : Integrable (fun _ : ℝ => (1 : ℝ)) ν := integrable_const _
  simpa only [Function.comp_def, ContinuousMap.comp_apply, ν, one_mul] using
    (continuous_weighted_path_integral (realTimeOnHorizon T).continuous.measurable hv).comp
      (ContinuousMap.continuous_postcomp f :
        Continuous (f.comp : CanonicalPath T (ℝ × ℝ) → CanonicalPath T ℝ))

private theorem canonicalStoppedPath_realTime_eq
    {E : Type*} [TopologicalSpace E] {T t : ℝ≥0}
    (p : CanonicalPath T E) {s : ℝ} (hs : s ≤ (t : ℝ)) :
    canonicalStoppedPath T t p (realTimeOnHorizon T s) = p (realTimeOnHorizon T s) := by
  apply congrArg p
  apply Subtype.ext
  have hst : s.toNNReal ≤ t := by
    simpa only [Real.toNNReal_coe] using (Real.toNNReal_mono hs)
  exact min_eq_left ((min_le_left s.toNNReal T).trans hst)

variable {E : Type*} [MetricSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

/-- A continuous functional depends measurably on the canonical past
when it is unchanged by stopping the path at the observation time. -/
theorem stronglyAdapted_canonical_of_stoppedPath {T : ℝ≥0}
    {F : ℝ≥0 → CanonicalPath T E → ℝ} (hc : ∀ t, Continuous (F t))
    (heq : ∀ t p, F t (canonicalStoppedPath T t p) = F t p) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := E) T) F := by
  intro t
  let g := canonicalPathNaturalFiltration (E := E) T
  let m : MeasurableSpace (CanonicalPath T E) := inferInstance
  have hg : @Measurable _ _ (g t) m (canonicalStoppedPath T t) := by
    have hgp : g t = m.comap (canonicalStoppedPath T t) :=
      canonicalPathNaturalFiltration_eq_comap_stopped T t
    rw [hgp]
    exact comap_measurable _
  have hm := (hc t).measurable.comp hg
  have he : F t ∘ canonicalStoppedPath T t = F t := funext (heq t)
  rw [he] at hm
  exact hm.stronglyMeasurable

/-- Time integration of continuous functions of the path gives an
adapted process on the canonical filtration. -/
theorem stronglyAdapted_pair_path_time_integral (T : ℝ≥0) (f : C(ℝ × ℝ, ℝ)) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := ℝ × ℝ) T)
      (fun t p => ∫ s in Ioc (0 : ℝ) (t : ℝ), f (p (realTimeOnHorizon T s))) := by
  refine stronglyAdapted_canonical_of_stoppedPath
    (fun t => continuous_pair_path_time_integral T t f) ?_
  intro t p
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  exact congrArg f (canonicalStoppedPath_realTime_eq p hs.2)

/-- Each of the two inverse-path martingale candidates is adapted to
the joint canonical filtration. -/
theorem stronglyAdapted_pair_recoveredVarianceMartingale (T : ℝ≥0)
    {α : ℝ} (hα : α < 1) (v₀ κ θ : ℝ) (f : C(ℝ × ℝ, ℝ)) :
    StronglyAdapted (canonicalPathNaturalFiltration (E := ℝ × ℝ) T)
      (fun t p => recoveredVarianceMartingale T α v₀ κ θ t (f.comp p)) := by
  refine stronglyAdapted_canonical_of_stoppedPath
    (fun t => (continuous_recoveredVarianceMartingale T hα v₀ κ θ t.prop).comp
      (ContinuousMap.continuous_postcomp f)) ?_
  intro t p
  unfold recoveredVarianceMartingale
  congr 2 <;> (apply setIntegral_congr_fun measurableSet_Ioc; intro s hs
               simp only [ContinuousMap.comp_apply, canonicalStoppedPath_realTime_eq p hs.2])

end RoughHeston

#print axioms RoughHeston.continuous_weighted_path_integral
#print axioms RoughHeston.continuous_recoveredVarianceMartingale
#print axioms RoughHeston.continuous_pair_path_time_integral

#print axioms RoughHeston.stronglyAdapted_canonical_of_stoppedPath
#print axioms RoughHeston.stronglyAdapted_pair_path_time_integral
#print axioms RoughHeston.stronglyAdapted_pair_recoveredVarianceMartingale
