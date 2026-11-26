import StoppedControl

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

/-- Time integral of squared exposure up to the observation, measured
on the fixed finite horizon. -/
noncomputable def controlEnergyClock (H : ℝ≥0) (h : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) (ω : Ω) :=
  ∫ v in Iic s, h v ω ^ 2 ∂hestonTimeMeasure H

private instance horizonFinite (H : ℝ≥0) : IsFiniteMeasure (hestonTimeMeasure H) := by
  rw [hestonTimeMeasure_eq_horizon]
  infer_instance

private instance horizonNoAtoms (H : ℝ≥0) : NullSingletonClass (hestonTimeMeasure H) where
  measure_singleton t := by
    rw [hestonTimeMeasure_eq_horizon, MathFin.ItoIntegralCLM.timeMeasureHorizon]
    exact le_antisymm ((Measure.restrict_le_self _).trans_eq (MathFin.ItoIntegralL2.timeMeasure_singleton t)) bot_le

omit m in
theorem controlEnergyClock_continuous (H : ℝ≥0) (h : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hi : Integrable (fun v => h v ω ^ 2) (hestonTimeMeasure H)) :
    Continuous (fun s => controlEnergyClock H h s ω) := by
  let f := fun v => h v ω ^ 2
  let g := fun (s : ℝ≥0) => (Iic s).indicator f
  have he (s : ℝ≥0) : controlEnergyClock H h s ω = ∫ v, g s v ∂hestonTimeMeasure H :=
    (integral_indicator measurableSet_Iic).symm
  simp_rw [he]
  apply continuous_iff_continuousAt.2
  intro a
  apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖f v‖)
    (.of_forall fun s => hi.aestronglyMeasurable.indicator measurableSet_Iic)
    (.of_forall fun s => ae_of_all _ fun v => norm_indicator_le_norm_self _ _) hi.norm
  filter_upwards [(hestonTimeMeasure H).ae_ne a] with v hv
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  rcases lt_or_gt_of_ne hv with hv | hv
  · filter_upwards [lt_mem_nhds hv] with s hs
    simp [g, f, hv.le, hs.le]
  · filter_upwards [gt_mem_nhds hv] with s hs
    simp [g, not_le.mpr hv, not_le.mpr hs]

omit m in
theorem controlEnergyClock_monotone (H : ℝ≥0) (h : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (hi : Integrable (fun v => h v ω ^ 2) (hestonTimeMeasure H)) :
    Monotone (fun s => controlEnergyClock H h s ω) := fun _ _ hst =>
  setIntegral_mono_set hi.integrableOn (ae_of_all _ fun _ => sq_nonneg _)
    (ae_of_all _ fun _ h => h.trans hst)

theorem controlEnergyClock_adapted (H : ℝ≥0) {h : ℝ≥0 → Ω → ℝ} (hh : IsStronglyPredictable F h) :
    StronglyAdapted F (controlEnergyClock H h) := by
  intro s
  let ν : Measure (Iic s) := (hestonTimeMeasure H).comap Subtype.val
  let : MeasurableSpace Ω := F s
  have hprog := (hh.isStronglyProgressive s).pow (2 : ℕ)
  have hi := hprog.integral_prod_left' (μ := ν)
  convert hi using 1
  ext ω
  exact (integral_subtype_comap measurableSet_Iic (fun v => h v ω ^ 2)).symm

omit m in
theorem controlEnergyClock_zero (H : ℝ≥0) (h : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    controlEnergyClock H h 0 ω = 0 := by
  rw [controlEnergyClock, show Iic (0 : ℝ≥0) = {0} by ext t; simp]
  simp

omit m in
theorem controlThrough_energy (H : ℝ≥0) (h : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (ω : Ω) :
    (∫ s, controlThrough h τ s ω ^ 2 ∂hestonTimeMeasure H) = controlEnergyClock H h (τ ω) ω := by
  rw [controlEnergyClock, ← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    by_cases hs : s ≤ τ ω <;> simp [controlThrough, Set.indicator, hs]

/-- The actual energy clock gives a stopping time on the joint filtration.
The physical energy of the stopped drift is the uncapped energy truncated at δ. -/
theorem exists_stopped_control_at_budget (H : ℝ≥0) {δ : ℝ} (hδ : 0 ≤ δ)
    {h : ℝ≥0 → Ω → ℝ} (hh : IsStronglyPredictable F h)
    (hi : ∀ ω, Integrable (fun s => h s ω ^ 2) (hestonTimeMeasure H)) :
    ∃ τ : Ω → ℝ≥0, (∀ ω, τ ω ≤ H) ∧ IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      IsStronglyPredictable F (controlThrough h τ) ∧
      (∀ ω, τ ω < H → δ ≤ controlEnergyClock H h H ω) ∧ ∀ ω,
        (∫ s, controlThrough h τ s ω ^ 2 ∂hestonTimeMeasure H) =
          min δ (controlEnergyClock H h H ω) := by
  let A := controlEnergyClock H h
  let τ := budgetStop H δ A
  have hc := fun ω => controlEnergyClock_continuous H h ω (hi ω)
  have hm := fun ω => controlEnergyClock_monotone H h ω (hi ω)
  have ht := budgetStop_isStoppingTime H δ (controlEnergyClock_adapted H hh) hc hm
  refine ⟨τ, budgetStop_le_horizon H δ A, ht, controlThrough_predictable ht hh,
    fun ω => budgetStop_early_exit (hc ω) (hm ω), fun ω => ?_⟩
  rw [controlThrough_energy]
  exact budgetStop_energy_eq_min H hδ ω (controlEnergyClock_zero H h ω) (hc ω) (hm ω)

end RoughHeston

#print axioms RoughHeston.controlEnergyClock_continuous
#print axioms RoughHeston.controlEnergyClock_monotone
#print axioms RoughHeston.controlEnergyClock_adapted
#print axioms RoughHeston.controlThrough_energy
#print axioms RoughHeston.exists_stopped_control_at_budget
