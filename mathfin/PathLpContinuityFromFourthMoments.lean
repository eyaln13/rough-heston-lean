import FractionalFixedMeshLaw
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! Pointwise path continuity and a uniform fourth moment imply
continuity of the associated L² variance trajectory. -/

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace RoughHeston

set_option maxHeartbeats 1100000

theorem unifIntegrable_two_of_uniform_eLpNorm_four {Ω I : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : I → Ω → ℝ} (hm : ∀ i, AEStronglyMeasurable (X i) μ)
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hB : ∀ i, eLpNorm (X i) 4 μ ≤ C) :
    UnifIntegrable X 2 μ := by
  unfold UnifIntegrable
  have hh : Tendsto (fun δ : ℝ≥0∞ => C*δ^(1/4:ℝ)) (𝓝 0) (𝓝 0) := by
    have h1 := ENNReal.continuous_rpow_const (y := (1/4:ℝ))
    have h2 : Continuous (fun δ : ℝ≥0∞ => C*δ^(1/4:ℝ)) := (ENNReal.continuous_const_mul hC).comp h1
    simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos (by norm_num : 0 < (1/4:ℝ)),
      mul_zero] using h2.tendsto 0
  apply tendsto_nhds_bot_mono hh
  refine Eventually.of_forall fun δ => ?_
  apply iSup_le
  intro i
  apply iSup_le
  intro s
  apply iSup_le
  intro hs
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s)
      (f := X i) (p := 2) (q := 4) (by norm_num) ((hm i).mono_measure Measure.restrict_le_self)
  rw [Measure.restrict_apply_univ] at h
  have he : (1 / (2:ℝ≥0∞).toReal - 1/(4:ℝ≥0∞).toReal) = (1/4:ℝ) := by norm_num
  rw [he] at h
  exact h.trans (mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hB i))
    (ENNReal.rpow_le_rpow hs (by norm_num)))

/-- The L² path can be constructed using timewise variance fourth moments;
no square-integrable samplewise supremum is needed for this step. -/
theorem continuous_toLp_two_of_continuous_paths_uniform_fourth {Ω I : Type*}
    [MeasurableSpace Ω] [TopologicalSpace I] [FirstCountableTopology I]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : I → Ω → ℝ}
    (hX : ∀ i, MemLp (X i) 2 μ)
    (hPath : ∀ᵐ ω ∂μ, Continuous (fun i => X i ω))
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (h₄ : ∀ i, eLpNorm (X i) 4 μ ≤ C) :
    Continuous (fun i => (hX i).toLp (X i)) := by
  rw [continuous_iff_continuousAt]
  intro i
  apply tendsto_nhds_iff_seq_tendsto.2
  intro u hu
  apply tendsto_iff_edist_tendsto_0.mpr
  simp only [Function.comp_apply, Lp.edist_toLp_toLp]
  apply tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top
    (fun n => (hX (u n)).aestronglyMeasurable) (hX i)
    (unifIntegrable_two_of_uniform_eLpNorm_four (fun n => (hX (u n)).aestronglyMeasurable)
      hC (fun n => h₄ (u n)))
  exact hPath.mono fun ω hω => (hω.tendsto i).comp hu

#print axioms RoughHeston.unifIntegrable_two_of_uniform_eLpNorm_four
#print axioms RoughHeston.continuous_toLp_two_of_continuous_paths_uniform_fourth

end RoughHeston
