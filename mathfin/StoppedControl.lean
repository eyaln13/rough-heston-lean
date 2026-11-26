import JointHestonWeights
import BrownianMotion.StochasticIntegral.Predictable
import Verification

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}

/-- The coefficient used to reverse the competitor drift on the stochastic
interval through the stopping time. The value of the ratio at zero is zero. -/
noncomputable def competitorControl (σ U Z X Y : ℝ) : ℝ :=
  if 0 < Y then σ * U / (Z * Real.sqrt X) else 0

theorem competitorControl_sq_le {σ U Z X Y : ℝ} (hu : 0 ≤ U) (hx : U ≤ X)
    (hz : 0 < Z) : competitorControl σ U Z X Y ^ 2 ≤ σ^2 * U / Z^2 := by
  unfold competitorControl
  split_ifs
  · rcases (hu.trans hx).eq_or_lt with he | hp
    · have hu0 : U = 0 := le_antisymm (hx.trans he.ge) hu
      simp [hu0]
    · exact tilt_cost_bound hu hx hp hz
  · simp only [zero_pow (by decide : 2 ≠ 0)]
    positivity

theorem competitorControl_residual (σ U Z X Y : ℝ) :
    Real.sqrt Y * (σ * U / (Z * Real.sqrt X) - competitorControl σ U Z X Y) = 0 := by
  unfold competitorControl
  by_cases hy : 0 < Y
  · simp [hy]
  · simp [hy, Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hy)]

theorem competitorControl_predictable (σ : ℝ) {U Z X Y : ℝ≥0 → Ω → ℝ}
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y) :
    IsStronglyPredictable F (fun s ω => competitorControl σ (U s ω) (Z s ω) (X s ω) (Y s ω)) := by
  let : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  exact (Measurable.ite (measurableSet_lt measurable_const (StronglyMeasurable.measurable hy))
    ((measurable_const.mul (StronglyMeasurable.measurable hu)).div
      ((StronglyMeasurable.measurable hz).mul (StronglyMeasurable.measurable hx).sqrt))
    measurable_const).stronglyMeasurable

noncomputable def controlThrough (h : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (s : ℝ≥0) (ω : Ω) :=
  if s ≤ τ ω then h s ω else 0

theorem controlThrough_predictable {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0))) {h : ℝ≥0 → Ω → ℝ}
    (hh : IsStronglyPredictable F h) : IsStronglyPredictable F (controlThrough h τ) := by
  let a := fun (s : ℝ≥0) => {ω : Ω | s ≤ τ ω}.indicator (fun _ => (1 : ℝ))
  have ha : IsStronglyPredictable F a := by
    apply StronglyAdapted.isStronglyPredictable_of_leftContinuous
    · intro s
      apply stronglyMeasurable_const.indicator
      simpa only [WithTop.coe_le_coe] using hτ.measurableSet_ge s
    · intro ω s
      change ContinuousWithinAt ({t : ℝ≥0 | t ≤ τ ω}.indicator (fun _ => (1 : ℝ))) (Iio s) s
      simpa only [WithTop.coe_le_coe] using
        continuousWithinAt_indicator_coe_le (τ ω : WithTop ℝ≥0) (1 : ℝ) s
  have he : Function.uncurry (controlThrough h τ) = (Function.uncurry a) * Function.uncurry h := by
    ext ⟨s, ω⟩
    by_cases hs : s ≤ τ ω <;> simp [Function.uncurry, controlThrough, a, Set.indicator, hs]
  change StronglyMeasurable[F.predictable] _
  rw [he]
  exact StronglyMeasurable.mul ha hh

/-- Stop at the first time the nondecreasing accumulated cost reaches the
cap, with the horizon included even if the cap is never reached. -/
noncomputable def budgetStop (H : ℝ≥0) (δ : ℝ) (A : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 :=
  sInf ({H} ∪ {s : ℝ≥0 | δ ≤ A s ω})

omit m in
private theorem budgetStop_mem (H : ℝ≥0) (δ : ℝ) {A : ℝ≥0 → Ω → ℝ} (ω : Ω)
    (hc : Continuous (fun s => A s ω)) :
    budgetStop H δ A ω = H ∨ δ ≤ A (budgetStop H δ A ω) ω := by
  exact ((isClosed_singleton.union (isClosed_le continuous_const hc)).csInf_mem
    (show ({H} ∪ {s : ℝ≥0 | δ ≤ A s ω}).Nonempty from ⟨H, Or.inl rfl⟩) (OrderBot.bddBelow _))

omit m in
theorem budgetStop_le_horizon (H : ℝ≥0) (δ : ℝ) (A : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    budgetStop H δ A ω ≤ H := csInf_le (OrderBot.bddBelow _) (Or.inl rfl)

omit m in
theorem budgetStop_early_exit {H : ℝ≥0} {δ : ℝ} {A : ℝ≥0 → Ω → ℝ} {ω : Ω}
    (hc : Continuous (fun s => A s ω)) (hm : Monotone (fun s => A s ω))
    (h : budgetStop H δ A ω < H) : δ ≤ A H ω := by
  rcases budgetStop_mem H δ ω hc with he | he
  · exact (h.ne he).elim
  · exact he.trans (hm h.le)

theorem budgetStop_isStoppingTime (H : ℝ≥0) (δ : ℝ) {A : ℝ≥0 → Ω → ℝ}
    (ha : StronglyAdapted F A) (hc : ∀ ω, Continuous (fun s => A s ω))
    (hm : ∀ ω, Monotone (fun s => A s ω)) :
    IsStoppingTime F (fun ω => (budgetStop H δ A ω : WithTop ℝ≥0)) := by
  intro s
  by_cases hs : H ≤ s
  · convert (MeasurableSet.univ : MeasurableSet[F s] (univ : Set Ω)) using 1
    ext ω
    simp only [mem_ofPred_eq, mem_univ, iff_true, WithTop.coe_le_coe]
    exact (budgetStop_le_horizon H δ A ω).trans hs
  · convert measurableSet_le (measurable_const (a := δ)) (ha s).measurable using 1
    ext ω
    change ((budgetStop H δ A ω : WithTop ℝ≥0) ≤ s) ↔ δ ≤ A s ω
    rw [WithTop.coe_le_coe]
    constructor
    · intro h
      rcases budgetStop_mem H δ ω (hc ω) with e | e
      · exact (hs (e ▸ h)).elim
      · exact e.trans (hm ω h)
    · intro h
      exact csInf_le (OrderBot.bddBelow _) (Or.inr h)

omit m in
theorem budgetStop_energy_eq_min (H : ℝ≥0) {δ : ℝ} (hδ : 0 ≤ δ)
    {A : ℝ≥0 → Ω → ℝ} (ω : Ω) (hzero : A 0 ω = 0)
    (hc : Continuous (fun s => A s ω)) (hm : Monotone (fun s => A s ω)) :
    A (budgetStop H δ A ω) ω = min δ (A H ω) := by
  let τ := budgetStop H δ A ω
  have hτH : τ ≤ H := budgetStop_le_horizon H δ A ω
  have hcap : A τ ω ≤ δ := by
    by_contra! hgt
    have hin : δ ∈ Icc (A 0 ω) (A τ ω) := ⟨hzero ▸ hδ, hgt.le⟩
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc (a := 0) (b := τ) zero_le hc.continuousOn hin
    have hτv : τ ≤ v := csInf_le (OrderBot.bddBelow _) (Or.inr he.ge)
    exact (not_lt_of_ge (he ▸ hm hτv : A τ ω ≤ δ)) hgt
  apply le_antisymm (le_min hcap (hm hτH))
  rcases budgetStop_mem H δ ω hc with h | h
  · simp [τ, h]
  · exact (min_le_left _ _).trans h

end RoughHeston

#print axioms RoughHeston.competitorControl_sq_le
#print axioms RoughHeston.competitorControl_residual
#print axioms RoughHeston.competitorControl_predictable
#print axioms RoughHeston.controlThrough_predictable
#print axioms RoughHeston.budgetStop_isStoppingTime
#print axioms RoughHeston.budgetStop_energy_eq_min

#print axioms RoughHeston.budgetStop_early_exit
