import StochasticFoundation
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open MeasureTheory Filter Set
open scoped MeasureTheory BoundedContinuousFunction Topology

namespace RoughHeston

variable {Ω ι I : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
  {𝒢 : Filtration ι mΩ} {M : ι → Ω → ℝ}

/-- Removing a deterministic path from a martingale leaves an explicit
error in each bounded past test. -/
theorem integral_weighted_increment_of_deterministic_shift
    {μ : Measure Ω} [IsFiniteMeasure μ] {d : ι → ℝ}
    (hM : Martingale (fun t ω => M t ω + d t) 𝒢 μ)
    {s t : ι} (hst : s ≤ t) {W : Ω → ℝ} {B : ℝ}
    (hW : StronglyMeasurable[𝒢 s] W) (hbound : ∀ ω, ‖W ω‖ ≤ B) :
    (∫ ω, (M t ω - M s ω) * W ω ∂μ) =
      (d s - d t) * ∫ ω, W ω ∂μ := by
  let N (r : ι) (ω : Ω) := M r ω + d r
  let Z := N t - N s
  have hZ : Integrable Z μ := (hM.integrable t).sub (hM.integrable s)
  have hWa := (hW.mono (𝒢.le s)).aestronglyMeasurable (μ := μ)
  have hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ B := Eventually.of_forall hbound
  have hWint : Integrable W μ := (integrable_const B).mono' hWa hWb
  have hWZ : Integrable (W * Z) μ := hZ.bdd_mul hWa hWb
  have hcond : μ[W * Z | 𝒢 s] =ᵐ[μ] (0 : Ω → ℝ) := by
    have he := (condExp_mul_of_stronglyMeasurable_left hW hWZ hZ).trans
      (EventuallyEq.rfl.mul (conditional_mean_martingale_increment hM hst))
    simpa only [mul_zero] using he
  have hzero : (∫ ω, (W * Z) ω ∂μ) = 0 := by
    calc
      _ = ∫ ω, μ[W * Z | 𝒢 s] ω ∂μ := (integral_condExp (𝒢.le s)).symm
      _ = _ := by simp only [integral_congr_ae hcond, Pi.zero_apply, integral_zero]
  have hMi (r : ι) : Integrable (M r) μ := by
    have hm := (hM.integrable r).sub (integrable_const (d r))
    exact hm.congr (Eventually.of_forall fun ω => by simp only [Pi.sub_apply, add_sub_cancel_right])
  have hmain : Integrable (fun ω => (M t ω - M s ω) * W ω) μ :=
    ((hMi t).sub (hMi s)).mul_bdd hWa hWb
  have hshift : Integrable (fun ω => (d t - d s) * W ω) μ :=
    hWint.const_mul _
  have heq : (∫ ω, (M t ω - M s ω) * W ω ∂μ) +
      (d t - d s) * (∫ ω, W ω ∂μ) = 0 := by
    rw [← integral_const_mul, ← integral_add hmain hshift, ← hzero]
    exact integral_congr_ae (Eventually.of_forall fun ω => by
      simp only [Pi.mul_apply, Pi.sub_apply, Z, N]
      ring)
  rw [show (d s - d t) * (∫ ω, W ω ∂μ) =
    -((d t - d s) * (∫ ω, W ω ∂μ)) by ring]
  linarith

/-- Bounded past tests of the unshifted process converge to zero as
the deterministic shifts vanish. -/
theorem tendsto_weighted_increment_tests_of_deterministic_shift
    {Pn : I → ProbabilityMeasure Ω} {l : Filter I} {d : I → ι → ℝ}
    (hd : ∀ r, Tendsto (fun i => d i r) l (𝓝 0))
    (hM : ∀ i, Martingale (fun t ω => M t ω + d i t) 𝒢 (Pn i : Measure Ω))
    {s t : ι} (hst : s ≤ t) {W : Ω → ℝ} {B : ℝ}
    (hW : StronglyMeasurable[𝒢 s] W) (hbound : ∀ ω, ‖W ω‖ ≤ B) :
    Tendsto (fun i => ∫ ω, (M t ω - M s ω) * W ω ∂(Pn i : Measure Ω)) l (𝓝 0) := by
  have hsmall : Tendsto (fun i => ‖d i s - d i t‖) l (𝓝 0) := by
    have h := ((hd s).sub (hd t)).norm
    change Tendsto (fun i => ‖d i s - d i t‖) l (𝓝 ‖(0 : ℝ) - 0‖) at h
    simpa only [sub_zero, norm_zero] using h
  have hlim : Tendsto (fun i => ‖d i s - d i t‖ * B) l (𝓝 0) := by
    have h := hsmall.mul (tendsto_const_nhds (x := B))
    change Tendsto (fun i => ‖d i s - d i t‖ * B) l (𝓝 (0 * B)) at h
    simpa only [zero_mul] using h
  apply tendsto_iff_dist_tendsto_zero.2
  simp only [dist_zero_right]
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) hlim
  have hB : ‖∫ ω, W ω ∂(Pn i : Measure Ω)‖ ≤ B := by
    simpa using (norm_integral_le_of_norm_le_const (μ := (Pn i : Measure Ω))
      (Eventually.of_forall hbound))
  rw [integral_weighted_increment_of_deterministic_shift (hM i) hst hW hbound, norm_mul]
  exact mul_le_mul_of_nonneg_left hB (norm_nonneg _)

/-- The bounded-continuous past tests needed by the weak-limit
martingale theorem hold for deterministic shifts of martingales. -/
theorem tendsto_boundedContinuous_past_tests_of_deterministic_shift
    {E : Type*} [TopologicalSpace E] [mE : MeasurableSpace E] [OpensMeasurableSpace E]
    {Pn : I → ProbabilityMeasure Ω} {l : Filter I} {d : I → ι → ℝ}
    (hd : ∀ r, Tendsto (fun i => d i r) l (𝓝 0))
    (hM : ∀ i, Martingale (fun t ω => M t ω + d i t) 𝒢 (Pn i : Measure Ω))
    {past : ι → Ω → E} (hpastAlg : ∀ s, 𝒢 s = mE.comap (past s)) :
    ∀ s t, s ≤ t → ∀ f : E →ᵇ ℝ,
      Tendsto (fun i => ∫ ω, (M t ω - M s ω) * f (past s ω) ∂(Pn i : Measure Ω)) l (𝓝 0) := by
  intro s t hst f
  have hs : @Measurable Ω E (𝒢 s) mE (past s) := by
    rw [hpastAlg s]
    exact comap_measurable (past s)
  have hf : StronglyMeasurable[𝒢 s] (fun ω => f (past s ω)) :=
    (f.continuous.measurable.comp hs).stronglyMeasurable
  exact tendsto_weighted_increment_tests_of_deterministic_shift hd hM hst hf
    (fun ω => f.norm_coe_le_norm (past s ω))

end RoughHeston

#print axioms RoughHeston.integral_weighted_increment_of_deterministic_shift
#print axioms RoughHeston.tendsto_weighted_increment_tests_of_deterministic_shift
#print axioms RoughHeston.tendsto_boundedContinuous_past_tests_of_deterministic_shift
