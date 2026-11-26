import StoppedBurstSeparation

/-! The occupation bound in the age variable integrated against the actual
stopped competitor drift in Brownian time. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}
  {R : Measure Ω} [IsProbabilityMeasure R]

private theorem normalized_envelope_eq {r s γ : ℝ} (hr : 0 < r) (hs : 0 < s) (C : ℝ) :
    (C * r^(3*γ)) / s^(1+3*γ) = C * (s⁻¹ * (r/s)^(3*γ)) := by
  rw [Real.rpow_add hs, Real.rpow_one, Real.div_rpow hr.le hs.le]
  ring

/-- The expected energy of the tangible stopped drift on the age interval
is at most C D H^η/(η−3γ), given the stopped occupancy of the competitor. -/
theorem competitor_stopped_energy_of_occupation {H : ℝ≥0} (hH : 0 < H)
    {γ η C D σ : ℝ} (hgap : 3*γ < η) (hC : 0 ≤ C) (hD : 0 ≤ D)
    {U Z X Y : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0}
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (ht : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (henv : ∀ ω s, 0 < s → s ≤ τ ω →
      (competitorAfterBirth 0 σ U Z X Y s ω)^2 ≤ (C*(H:ℝ)^(3*γ))/(s:ℝ)^(1+3*γ))
    (hocc : ∀ s ∈ Ioc (0 : ℝ≥0) H, R.real {ω | s ≤ τ ω ∧ 0 < Y s ω} ≤ D*(s:ℝ)^η) :
    let g := controlThrough (competitorAfterBirth 0 σ U Z X Y) τ
    let E (ω : Ω) := ∫ s, (g s ω)^2 ∂hestonTimeMeasure H
    Measurable E ∧ Integrable E R ∧ (∫ ω, E ω ∂R) ≤ C*D*(H:ℝ)^η/(η-3*γ) := by
  dsimp only
  let g := controlThrough (competitorAfterBirth 0 σ U Z X Y) τ
  have hg := controlThrough_predictable ht (competitorAfterBirth_predictable (σ := σ)
    (b := 0) hu hz hx hy)
  have hpair : Measurable (fun z : ℝ × Ω => (z.1.toNNReal,z.2)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd
  have hy' := StronglyMeasurable.measurable (StronglyMeasurable.mono hy F.predictable_le_prod)
  have hg' := StronglyMeasurable.measurable (StronglyMeasurable.mono hg F.predictable_le_prod)
  let cost (s : ℝ) (ω : Ω) := (g s.toNNReal ω)^2
  let J := {z : ℝ × Ω | z.1.toNNReal ≤ τ z.2 ∧ 0 < Y z.1.toNNReal z.2}
  have hJ : MeasurableSet J := (measurableSet_le
    (continuous_real_toNNReal.measurable.comp measurable_fst) ((measurable_finite_stop ht).comp measurable_snd)).inter
    (measurableSet_lt measurable_const (hy'.comp hpair))
  have hm : Measurable (Function.uncurry cost) := (hg'.comp hpair).pow_const 2
  obtain ⟨hI, hbound⟩ := stopped_occupation_cost_bound (μ := R) (r := (H:ℝ))
    (show 0 < (H:ℝ) from hH) hgap hC hD hJ hm (fun _ _ _ => sq_nonneg _) (by
      intro s hs ω
      have hs' : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
      by_cases hτ : s.toNNReal ≤ τ ω
      · by_cases hY : 0 < Y s.toNNReal ω
        · rw [Set.indicator_of_mem (show ω ∈ {ω' | (s,ω') ∈ J} from ⟨hτ,hY⟩)]
          have h := henv ω s.toNNReal hs' hτ
          rw [Real.coe_toNNReal s hs.1.le, normalized_envelope_eq (r := (H:ℝ)) (γ := γ) (by exact_mod_cast hH) hs.1 C] at h
          simpa [occupationEnvelope,cost,g,controlThrough,hτ] using h
        · have hnot : (s,ω) ∉ J := fun h => hY h.2
          rw [Set.indicator_of_notMem (show ω ∉ {ω' | (s,ω') ∈ J} from hnot)]
          simp [cost, g, controlThrough, competitorAfterBirth, competitorControl,hY]
      · have hnot : (s,ω) ∉ J := fun h => hτ h.1
        rw [Set.indicator_of_notMem (show ω ∉ {ω' | (s,ω') ∈ J} from hnot)]
        simp [cost,g,controlThrough,hτ]) (by
      intro s hs
      have hs' : s.toNNReal ∈ Ioc (0:ℝ≥0) H := ⟨Real.toNNReal_pos.mpr hs.1,
        (Real.toNNReal_le_iff_le_coe).mpr hs.2⟩
      simpa [J,Real.coe_toNNReal s hs.1.le] using hocc s.toNNReal hs')
  have he (ω : Ω) : (∫ s, g s ω ^ 2 ∂hestonTimeMeasure H) =
      ∫ s in Ioc (0:ℝ) H, cost s ω := by
    have hh : Measurable (fun s => g s ω ^ 2) :=
      (hg'.comp (measurable_id.prodMk measurable_const)).pow_const 2
    rw [hestonTimeMeasure,integral_map continuous_real_toNNReal.measurable.aemeasurable
      hh.aestronglyMeasurable, restrict_Ioo_eq_restrict_Ioc]
  have e : (fun ω => ∫ s, g s ω ^ 2 ∂hestonTimeMeasure H) =
    (fun ω => ∫ s in Ioc (0:ℝ) H, cost s ω) := funext he
  change Measurable (fun ω => ∫ s, g s ω ^ 2 ∂hestonTimeMeasure H) ∧ _
  rw [e]
  exact ⟨hm.stronglyMeasurable.integral_prod_left'.measurable,
    hI.integral_prod_right, hbound⟩

#print axioms competitor_stopped_energy_of_occupation

end RoughHeston
