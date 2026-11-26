import StoppedBoundaryOccupation
import StoppedClusterEnvelope
import StoppedEntropyBound

/-! Probability of a focal burst with a zero competing variance from the
stopped-energy and terminal occupation estimates. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

theorem measurable_finite_stop {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0))) : Measurable τ := by
  apply measurable_of_Ioi
  intro s
  have hf : MeasurableSet {ω | τ ω ≤ s} := by
    simpa only [WithTop.coe_le_coe] using F.le s _ (hτ s)
  convert hf.compl using 1
  ext ω
  change s < τ ω ↔ ¬ τ ω ≤ s
  exact lt_iff_not_ge

/-- A burst is lost only if the envelope fails, the stopped energy reaches
its budget, or the competitor is positive at the horizon before stopping.
The last two events use a single application of total variation. -/
theorem stopped_burst_with_zero_probability
    {Q R : Measure Ω} [IsProbabilityMeasure Q] [IsProbabilityMeasure R]
    {H : ℝ≥0} {δ p failure mean occupation tv : ℝ} (hδ : 0 < δ)
    {γ τ : Ω → ℝ≥0} (hτ : Measurable τ) {Y E : Ω → ℝ} (hY : Measurable Y)
    (hY₀ : ∀ ω, 0 ≤ Y ω) (hE : Measurable E) (hE₀ : ∀ᵐ ω ∂R, 0 ≤ E ω)
    (hi : Integrable E R) (hmean : (∫ ω, E ω ∂R) ≤ mean)
    (hexit : ∀ ω, τ ω < H → H ≤ γ ω → δ ≤ E ω)
    (henv : Q.real {ω | γ ω < H} ≤ failure)
    (hocc : R.real {ω | H ≤ τ ω ∧ 0 < Y ω} ≤ occupation)
    (hTV : ∀ A, MeasurableSet A → |R.real A - Q.real A| ≤ tv)
    {burst : Set Ω} (hburst : p ≤ Q.real burst) :
    p - failure - mean / δ - occupation - tv ≤ Q.real (burst ∩ {ω | Y ω = 0}) := by
  let cap := {ω | δ ≤ E ω}
  let active := {ω | H ≤ τ ω ∧ 0 < Y ω}
  let bad := {ω | γ ω < H} ∪ (cap ∪ active)
  have hcap : R.real cap ≤ mean / δ := by
    apply (le_div_iff₀ hδ).mpr
    simpa [cap, mul_comm] using (mul_meas_ge_le_integral_of_nonneg hE₀ hi δ).trans hmean
  have hm : MeasurableSet (cap ∪ active) := (measurableSet_le measurable_const hE).union
    ((measurableSet_le measurable_const hτ).inter (measurableSet_lt measurable_const hY))
  have hdiff := (abs_le.mp (hTV (cap ∪ active) hm)).1
  have hR : R.real (cap ∪ active) ≤ mean / δ + occupation :=
    (measureReal_union_le cap active).trans (add_le_add hcap hocc)
  have hbad : Q.real bad ≤ failure + (mean / δ + occupation + tv) :=
    (measureReal_union_le _ _).trans (add_le_add henv (by linarith))
  have hsub : burst \ bad ⊆ burst ∩ {ω | Y ω = 0} := by
    rintro ω ⟨hb, hn⟩
    refine ⟨hb, le_antisymm (le_of_not_gt fun hy => ?_) (hY₀ ω)⟩
    apply hn
    by_cases hγ : γ ω < H
    · exact Or.inl hγ
    · by_cases h : τ ω < H
      · exact Or.inr (Or.inl (hexit ω h (le_of_not_gt hγ)))
      · exact Or.inr (Or.inr ⟨le_of_not_gt h, hy⟩)
  have h := (le_measureReal_sdiff (μ := Q) (s₁ := burst) (measure_ne_top Q bad)).trans
    (measureReal_mono hsub)
  linarith

#print axioms measurable_finite_stop
#print axioms stopped_burst_with_zero_probability

end RoughHeston
