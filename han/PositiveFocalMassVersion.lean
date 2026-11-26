import ActualAgePulseStoppedLaw
import SHE.ContinuousPredictable

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {μ Q R : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 m} [F.IsComplete μ] {r : ℝ≥0} {Z U : ℝ≥0 → Ω → ℝ}

/-- Modify the focal mass only on its single exceptional sample set
to obtain a positive predictable version on the complete trace. -/
theorem exists_everywhere_positive_focal_mass
    (hZ : Martingale Z F μ) (hZc : ∀ ω, Continuous (fun t => Z t ω))
    (hPos : ∀ᵐ ω ∂μ, ∀ t, 0<Z t ω) :
    ∃ W : ℝ≥0 → Ω → ℝ, Martingale W F μ ∧ IsStronglyPredictable F W ∧
      (∀ ω, Continuous (fun t => W t ω)) ∧ (∀ t ω, 0<W t ω) ∧
      (∀ᵐ ω ∂μ, ∀ t, W t ω=Z t ω) := by
  classical
  let E : Set Ω := {ω | ¬∀ t, 0<Z t ω}
  have hE₀ : μ E=0 := ae_iff.mp hPos
  have hE : MeasurableSet[F 0] E := Filtration.IsComplete.measurableSet_of_null hE₀ 0
  let W (t : ℝ≥0) (ω : Ω) := if ω∈E then 1 else Z t ω
  have hWa (t : ℝ≥0) : StronglyMeasurable[F t] (W t) :=
    stronglyMeasurable_const.ite (F.mono zero_le E hE) (hZ.stronglyAdapted t)
  have hWc (ω : Ω) : Continuous (fun t => W t ω) := by
    by_cases h : ω∈E
    · simpa only [W,ite_eq_left h] using (@continuous_const ℝ≥0 ℝ _ _ 1)
    · simpa only [W,ite_eq_right h] using hZc ω
  have hW₀ (t : ℝ≥0) (ω : Ω) : 0<W t ω := by
    by_cases h : ω∈E
    · simp [W,h]
    · have ha : ∀ t, 0<Z t ω := by simpa only [E,mem_ofPred_eq,not_not] using h
      simp only [W,ite_eq_right h]
      exact ha t
  have hWZ : ∀ᵐ ω ∂μ, ∀ t,W t ω=Z t ω := by
    filter_upwards [hPos] with ω hω t
    simp [W,E,hω]
  exact ⟨W,hZ.congr hWa (fun t => hWZ.mono fun _ h => (h t).symm),
    SHE.ContinuousPredictable.stronglyMeasurable _ _ hWa hWc,hWc,hW₀,hWZ⟩

omit [IsProbabilityMeasure μ] [F.IsComplete μ] in
/-- A change of the envelope on a null set can be absorbed by observing
at the terminal clock there, leaving the stopped estimate unchanged. -/
noncomputable def PulseStoppedLaw_change_envelope
    {δ mBudget oBudget : ℝ} {env env' : Ω → ℝ≥0} {Y : Ω → ℝ}
    (law : PulseStoppedLaw Q R r δ mBudget oBudget env' Y)
    (he : Measurable env) (he' : Measurable env')
    (hEq : env=ᵐ[Q] env') (hRQ : R≪Q) :
    PulseStoppedLaw Q R r δ mBudget oBudget env Y := by
  classical
  let stop (ω : Ω) := if env ω=env' ω then law.stop ω else r
  have hm : Measurable stop := Measurable.ite (measurableSet_eq_fun he he') law.stop_measurable measurable_const
  have hsame : stop =ᵐ[R] law.stop := by
    filter_upwards [hRQ.ae_eq hEq] with ω hω
    simp [stop,hω]
  refine ⟨stop,law.energy,hm,law.energy_measurable,law.energy_nonnegative,law.energy_integrable,
    law.energy_mean,?_,?_,law.total_variation⟩
  · intro ω hstop henv
    by_cases hh : env ω=env' ω
    · exact law.exit ω (by simpa only [stop,ite_eq_left hh] using hstop) (hh ▸ henv)
    · exact False.elim (lt_irrefl r (by simpa only [stop,ite_eq_right hh] using hstop))
  · have hset : {ω | r≤stop ω ∧ 0<Y ω} =ᵐ[R] {ω | r≤law.stop ω ∧ 0<Y ω} := by
      filter_upwards [hsame] with ω hω
      rw [hω]
    have heq : R.real {ω | r≤stop ω ∧ 0<Y ω} = R.real {ω | r≤law.stop ω ∧ 0<Y ω} :=
      congrArg ENNReal.toReal (measure_congr hset)
    rw [heq]
    exact law.stopped_occupation

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.exists_everywhere_positive_focal_mass
#print axioms RoughHeston.GirsanovPort.PulseStoppedLaw_change_envelope
