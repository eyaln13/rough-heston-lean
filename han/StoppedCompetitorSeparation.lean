import StoppedTransformOccupation
import StoppedPhysicalOccupation

/-! Applying Han's transported stopped law to competitors observed at a fixed age. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {F : Filtration ℝ≥0 m}
  {Q : Measure Ω} [IsProbabilityMeasure Q] {B : ℝ≥0 → Ω → ℝ} {H : ℝ≥0}
  {hB₂ : ∀ t, MemLp (B t) 2 Q}

/-- Laplace tests transported under the actual change of measure give
stopped occupation from the bound on their conditional values at birth. -/
theorem stopped_occupation_from_affine_tests {birth s : ℝ≥0} {δ d : ℝ}
    {R : Measure Ω} {N g Y : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0}
    (hc : IsStoppedDriftChange (F := F) (H := H) birth δ g hB₂ R N) (ht : Measurable τ)
    (hy : Measurable (Y s)) (hy₀ : ∀ ω, 0 ≤ Y s ω)
    {test a A : ℕ → Ω → ℝ} {f : ℕ → ℝ≥0 × Ω → ℝ}
    (v : ℕ → Lp ℝ 2 (jointPredictableMeasure F Q H))
    (w : ℕ → Lp ℝ 2 (jointPredictableMeasure F R H))
    (hv : ∀ n, v n =ᵐ[jointPredictableMeasure F Q H] f n)
    (hw : ∀ n, v n =ᵐ[jointPredictableMeasure F Q H] w n)
    (ha : ∀ n, StronglyMeasurable[F birth] (a n)) (hai : ∀ n, Integrable (a n) R)
    (hrep : ∀ n, test n =ᵐ[Q] fun ω =>
      a n ω + jointItoIntegralCLM H hB₂ (v n) ω + A n ω)
    (hcost : ∀ n, A n =ᵐ[Q] fun ω => ∫ r, f n (r, ω) * g r ω ∂hestonTimeMeasure H)
    (hn : ∀ n, ∀ᵐ ω ∂R, 0 ≤ test n ω)
    (hterminal : ∀ n, ∀ᵐ ω ∂R, s ≤ τ ω → test n ω = 1 - Real.exp (-(n:ℝ)*Y s ω))
    (hborn : ∀ n, (∫ ω, a n ω ∂Q) ≤ d) :
    R.real {ω | s ≤ τ ω ∧ 0 < Y s ω} ≤ d := by
  let _ : IsProbabilityMeasure R := hc.choose
  let S := {ω | s ≤ τ ω}
  have hS : MeasurableSet S := measurableSet_le measurable_const ht
  have hmean n := stopped_test_mean_under_change hc (v n) (w n) (hv n) (hw n)
    (ha n) (hai n) (hrep n) (hcost n)
  have h : (R.restrict S).real {ω | 0 < Y s ω} ≤ d := by
    apply positive_probability_of_laplace_bounds hy hy₀
    intro n
    have he : (fun ω => 1 - Real.exp (-(n:ℝ)*Y s ω)) =ᵐ[R.restrict S] test n := by
      filter_upwards [ae_restrict_mem hS, ae_restrict_of_ae (hterminal n)] with ω hs he
      exact (he hs).symm
    rw [integral_congr_ae he]
    exact (setIntegral_le_integral (hmean n).1 (hn n)).trans ((hmean n).2.le.trans (hborn n))
  rw [measureReal_restrict_apply (measurableSet_lt measurable_const hy), inter_comm] at h
  exact h

/-- Quantitative birth-age burst estimate in Q for the physical stopped
Girsanov law. The original burst, the envelope-failure probability and
the conditional occupation estimate are model-specific inputs. -/
theorem stopped_competitor_burst_separates {R : Measure Ω} {N : ℝ≥0 → Ω → ℝ}
    {U Z X Y : ℝ≥0 → Ω → ℝ} {τ γstop : Ω → ℝ≥0}
    {σ δ η γ C D p failure : ℝ} (hH : 0 < H) (hδ : 0 < δ)
    (hgap : 3*γ < η) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hu : IsStronglyPredictable F U) (hz : IsStronglyPredictable F Z)
    (hx : IsStronglyPredictable F X) (hy : IsStronglyPredictable F Y)
    (hY₀ : ∀ ω, 0 ≤ Y H ω) (ht : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0)))
    (hc : IsStoppedDriftChange (F := F) (H := H) 0 δ
      (controlThrough (competitorAfterBirth 0 σ U Z X Y) τ) hB₂ R N)
    (hcancel : ∀ ω, τ ω < H → H ≤ γstop ω → δ ≤
      controlEnergyClock H (controlThrough (competitorAfterBirth 0 σ U Z X Y) γstop) H ω)
    (hbudget : ∀ ω, (∫ s, controlThrough (competitorAfterBirth 0 σ U Z X Y) τ s ω ^ 2
      ∂hestonTimeMeasure H) =
      min δ (controlEnergyClock H (controlThrough (competitorAfterBirth 0 σ U Z X Y) γstop) H ω))
    (henv : ∀ ω s, 0 < s → s ≤ τ ω →
      (competitorAfterBirth 0 σ U Z X Y s ω)^2 ≤ (C*(H:ℝ)^(3*γ))/(s:ℝ)^(1+3*γ))
    (hfail : Q.real {ω | γstop ω < H} ≤ failure)
    (hocc : ∀ s ∈ Ioc (0:ℝ≥0) H, R.real {ω | s ≤ τ ω ∧ 0 < Y s ω} ≤ D*(s:ℝ)^η)
    {burst : Set Ω} (hb : p ≤ Q.real burst) :
    p - failure - C*D*(H:ℝ)^η/(η-3*γ)/δ - D*(H:ℝ)^η - Real.sqrt δ/2 ≤
      Q.real (burst ∩ {ω | Y H ω = 0}) := by
  obtain ⟨hR, _, _, _, _, tv, -⟩ := hc
  let _ : IsProbabilityMeasure R := hR
  obtain ⟨hme,hi,hmean⟩ := competitor_stopped_energy_of_occupation hH hgap hC hD
    hu hz hx hy ht henv hocc
  have hYm := StronglyMeasurable.measurable (StronglyMeasurable.mono hy F.predictable_le_prod)
  apply stopped_burst_with_zero_probability hδ (measurable_finite_stop ht)
    (hYm.comp (measurable_const.prodMk measurable_id)) hY₀ hme
    (ae_of_all _ fun ω => integral_nonneg fun s => sq_nonneg _) hi hmean ?_ hfail
    (hocc H ⟨hH,le_rfl⟩) tv hb
  intro ω hs hg
  rw [hbudget ω, min_eq_left (hcancel ω hs hg)]

#print axioms stopped_occupation_from_affine_tests
#print axioms stopped_competitor_burst_separates

end RoughHeston.GirsanovPort
