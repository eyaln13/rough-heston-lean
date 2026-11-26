import StoppedControl
import ProductKernelEnergy
import HestonFubiniKernel
import JointHestonWeights

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 m} {H b : ℝ≥0} {Y D : ℝ≥0 → Ω → ℝ}

noncomputable def stoppedAffineTestRow (k : ℝ≥0 → ℝ) (D Y : ℝ≥0 → Ω → ℝ)
    (b : ℝ≥0) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if b < t ∧ t ≤ τ ω then min 1 (max 0 (D t ω)) * (k t * Real.sqrt (Y t ω)) else 0

omit [IsFiniteMeasure μ] in
/-- The Brownian row of a stopped Laplace test is supported after
birth, before the stop, and on strictly positive competitor variance. -/
theorem stoppedAffineTestRow_active {k : ℝ≥0 → ℝ} {τ : Ω → ℝ≥0}
    (t : ℝ≥0) (ω : Ω) (hf : stoppedAffineTestRow k D Y b τ t ω ≠ 0) :
    b < t ∧ t ≤ τ ω ∧ 0 < Y t ω := by
  by_cases ht : b < t ∧ t ≤ τ ω
  · refine ⟨ht.1, ht.2, ?_⟩
    by_contra! hn
    exact hf (by simp [stoppedAffineTestRow, ht, Real.sqrt_eq_zero_of_nonpos hn])
  · exact False.elim (hf (by simp [stoppedAffineTestRow, ht]))

theorem stoppedAffineTestRow_predictable {k : ℝ≥0 → ℝ} (hk : Measurable k)
    {τ : Ω → ℝ≥0} (ht : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hD : IsStronglyPredictable F D) (hY : IsStronglyPredictable F Y) :
    IsStronglyPredictable F (stoppedAffineTestRow k D Y b τ) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let h (t : ℝ≥0) (ω : Ω) :=
    if b < t then min 1 (max 0 (D t ω)) * (k t * Real.sqrt (Y t ω)) else 0
  have hfst := measurable_fst_jointPredictable F
  have hP : IsStronglyPredictable F h :=
    (Measurable.ite (measurableSet_lt measurable_const hfst)
      ((measurable_const.min (measurable_const.max hD.measurable)).mul
        ((hk.comp hfst).mul hY.measurable.sqrt)) measurable_const).stronglyMeasurable
  have he : stoppedAffineTestRow k D Y b τ = controlThrough h τ := by
    funext t ω
    by_cases hb : b<t <;> by_cases hτ : t≤τ ω <;> simp [stoppedAffineTestRow, controlThrough, h, hb, hτ]
  rw [he]
  exact controlThrough_predictable ht hP

/-- Square integrability of the actual stopped row needs only the
uniform first moment under the measure in which transport is used. -/
theorem stoppedAffineTestRow_memLp {k : ℝ≥0 → ℝ}
    (hk : Measurable k) (hk₂ : MemLp k 2 (hestonTimeMeasure H))
    {τ : Ω → ℝ≥0} (ht : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hD : IsStronglyPredictable F D) (hY : IsStronglyPredictable F Y)
    (hY₀ : ∀ t ω, 0 ≤ Y t ω) (hYi : ∀ t, Integrable (Y t) μ)
    {A : ℝ} (hMean : ∀ t, (∫ ω, Y t ω ∂μ) ≤ A) :
    MemLp (Function.uncurry (stoppedAffineTestRow k D Y b τ)) 2 (jointPredictableMeasure F μ H) := by
  have hp := stoppedAffineTestRow_predictable (b := b) hk ht hD hY
  have hbase := memLp_kernel_mul_sqrt_of_uniform_mean hk₂
    (hY.mono F.predictable_le_prod).measurable hY₀ hYi hMean
  have hL : MemLp (Function.uncurry (stoppedAffineTestRow k D Y b τ)) 2 ((hestonTimeMeasure H).prod μ) := by
    refine hbase.mono (hp.mono F.predictable_le_prod).aestronglyMeasurable ?_
    refine ae_of_all _ fun p => ?_
    by_cases h : b < p.1 ∧ p.1 ≤ τ p.2
    · simp only [Function.uncurry, stoppedAffineTestRow, ite_eq_left h, norm_mul]
      apply mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      have h₀ : 0 ≤ min (1 : ℝ) (max 0 (D p.1 p.2)) := le_min zero_le_one (le_max_left _ _)
      rw [Real.norm_of_nonneg h₀]
      exact min_le_left _ _
    · change ‖stoppedAffineTestRow k D Y b τ p.1 p.2‖ ≤ _
      rw [stoppedAffineTestRow, ite_eq_right h, norm_zero]
      exact norm_nonneg _
  exact (le_of_eq (eLpNorm_jointPredictableMeasure_eq_product H hp)).trans_lt hL

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.stoppedAffineTestRow_active
#print axioms RoughHeston.GirsanovPort.stoppedAffineTestRow_predictable
#print axioms RoughHeston.GirsanovPort.stoppedAffineTestRow_memLp
