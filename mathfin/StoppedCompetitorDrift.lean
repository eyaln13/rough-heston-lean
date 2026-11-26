import StoppedEnergyClock

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

noncomputable def competitorAfterBirth (b : ℝ≥0) (σ : ℝ)
    (U Z X Y : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) : ℝ :=
  if b < s then competitorControl σ (U s ω) (Z s ω) (X s ω) (Y s ω) else 0

theorem competitorAfterBirth_predictable {b : ℝ≥0} {σ : ℝ} {U Z X Y : ℝ≥0 → Ω → ℝ}
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y) :
    IsStronglyPredictable F (competitorAfterBirth b σ U Z X Y) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (Measurable.ite (measurableSet_lt measurable_const (measurable_fst_jointPredictable F))
    (StronglyMeasurable.measurable (competitorControl_predictable σ hu hz hx hy))
    measurable_const).stronglyMeasurable

theorem stopped_competitor_sq_integrable (H b : ℝ≥0) {σ : ℝ} {U Z X Y : ℝ≥0 → Ω → ℝ}
    {γ : Ω → ℝ≥0} (hg : IsStoppingTime F (fun ω => (γ ω : WithTop ℝ≥0)))
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y) (ω : Ω)
    (huc : ContinuousOn (fun s => U s ω) (Icc 0 H))
    (hzc : ContinuousOn (fun s => Z s ω) (Icc 0 H))
    (hzpos : ∀ s ≤ H, 0 < Z s ω) (hun : ∀ s ≤ H, 0 ≤ U s ω)
    (hux : ∀ s ≤ H, U s ω ≤ X s ω) :
    Integrable (fun s => controlThrough (competitorAfterBirth b σ U Z X Y) γ s ω ^ 2)
      (hestonTimeMeasure H) := by
  let h := controlThrough (competitorAfterBirth b σ U Z X Y) γ
  have hp : IsStronglyPredictable F h := controlThrough_predictable hg
    (competitorAfterBirth_predictable hu hz hx hy)
  let φ := fun s => σ ^ 2 * U s ω / Z s ω ^ 2
  have hc : ContinuousOn φ (Icc 0 H) := (continuousOn_const.mul huc).div (hzc.pow 2)
    (fun s hs => pow_ne_zero 2 (hzpos s hs.2).ne')
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (show (0 : ℝ≥0) ≤ H from zero_le)) hc
  have hfi : IsFiniteMeasure (hestonTimeMeasure H) := by
    rw [hestonTimeMeasure_eq_horizon]; infer_instance
  have hmeas : Measurable (fun s => h s ω) :=
    (StronglyMeasurable.measurable (StronglyMeasurable.mono hp F.predictable_le_prod)).comp
      (measurable_id.prodMk measurable_const)
  refine (integrable_const (φ v)).mono' (hmeas.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [ae_time_lt_hestonTimeMeasure H] with s hs
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  apply le_trans _ (hmax (show s ∈ Icc 0 H from ⟨zero_le, hs.le⟩))
  have hpos : 0 ≤ φ s := div_nonneg (mul_nonneg (sq_nonneg _) (hun s hs.le)) (sq_nonneg _)
  by_cases h₁ : s ≤ γ ω <;> by_cases h₂ : b < s
  · simpa [controlThrough, competitorAfterBirth, h₁, h₂, φ] using
      competitorControl_sq_le (σ := σ) (Y := Y s ω) (hun s hs.le) (hux s hs.le) (hzpos s hs.le)
  all_goals simpa [controlThrough, competitorAfterBirth, h₁, h₂] using hpos

/-- Both cutoffs act on the actual competitor drift. The final stop is
the minimum of the envelope failure and the budget time. -/
theorem exists_stopped_competitor_control (H b : ℝ≥0) {δ σ : ℝ} (hδ : 0 ≤ δ)
    {U Z X Y : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0}
    (hg : IsStoppingTime F (fun ω => (γ ω : WithTop ℝ≥0)))
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (huc : ∀ ω, ContinuousOn (fun s => U s ω) (Icc 0 H))
    (hzc : ∀ ω, ContinuousOn (fun s => Z s ω) (Icc 0 H))
    (hzpos : ∀ s ≤ H, ∀ ω, 0 < Z s ω) (hun : ∀ s ≤ H, ∀ ω, 0 ≤ U s ω)
    (hux : ∀ s ≤ H, ∀ ω, U s ω ≤ X s ω) :
    let h := competitorAfterBirth b σ U Z X Y
    ∃ τ : Ω → ℝ≥0, IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      (∀ ω, τ ω ≤ H ∧ τ ω ≤ γ ω) ∧ IsStronglyPredictable F (controlThrough h τ) ∧
      (∀ ω, τ ω < H → H ≤ γ ω → δ ≤ controlEnergyClock H (controlThrough h γ) H ω) ∧
      ∀ ω, Integrable (fun s => controlThrough h τ s ω ^ 2) (hestonTimeMeasure H) ∧
        (∫ s, controlThrough h τ s ω ^ 2 ∂hestonTimeMeasure H) =
          min δ (controlEnergyClock H (controlThrough h γ) H ω) := by
  dsimp only
  let h := competitorAfterBirth b σ U Z X Y
  have hp : IsStronglyPredictable F h := competitorAfterBirth_predictable hu hz hx hy
  have hi := fun ω => stopped_competitor_sq_integrable (σ := σ) H b hg hu hz hx hy ω (huc ω) (hzc ω)
    (fun s hs => hzpos s hs ω) (fun s hs => hun s hs ω) (fun s hs => hux s hs ω)
  obtain ⟨ρ, hrH, hr, _, hexit, hbudget⟩ := exists_stopped_control_at_budget H hδ
    (controlThrough_predictable hg hp) hi
  let τ := fun ω => min (ρ ω) (γ ω)
  have ht : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) := by
    simpa only [τ, WithTop.coe_min] using hr.min hg
  refine ⟨τ, ht, fun ω => ⟨(min_le_left _ _).trans (hrH ω), min_le_right _ _⟩,
    controlThrough_predictable ht hp, ?_, fun ω => ⟨?_, ?_⟩⟩
  · intro ω hτ hgH
    apply hexit ω
    exact lt_of_not_ge fun h => hτ.not_ge (le_min h hgH)
  · exact stopped_competitor_sq_integrable H b ht hu hz hx hy ω (huc ω) (hzc ω)
      (fun s hs => hzpos s hs ω) (fun s hs => hun s hs ω) (fun s hs => hux s hs ω)
  · convert hbudget ω using 2
    ext s
    by_cases hr' : s ≤ ρ ω <;> by_cases hg' : s ≤ γ ω <;>
      simp [controlThrough, τ, h, hr', hg']

end RoughHeston

#print axioms RoughHeston.competitorAfterBirth_predictable
#print axioms RoughHeston.stopped_competitor_sq_integrable
#print axioms RoughHeston.exists_stopped_competitor_control
