import StoppedCompetitorGirsanov
import StoppedBoundaryOccupation

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

namespace RoughHeston.GirsanovPort

variable {Ω : Type*} [m : MeasurableSpace Ω] {Q : Measure Ω} [IsProbabilityMeasure Q]
  {R : Measure Ω} {F : Filtration ℝ≥0 m} {H birth : ℝ≥0} {δ : ℝ}
  {B N : ℝ≥0 → Ω → ℝ} {g : ℝ≥0 → Ω → ℝ} {hB₂ : ∀ s, MemLp (B s) 2 Q}

private theorem integral_eq_at_birth [IsProbabilityMeasure R]
    (hp : ∀ A, MeasurableSet[F birth] A → R.real A = Q.real A) {a : Ω → ℝ}
    (ha : StronglyMeasurable[F birth] a) : (∫ ω, a ω ∂R) = ∫ ω, a ω ∂Q := by
  have he : R.trim (F.le birth) = Q.trim (F.le birth) := by
    refine @Measure.ext Ω (F birth) _ _ ?_
    intro A hA
    rw [trim_measurableSet_eq (F.le birth) hA, trim_measurableSet_eq (F.le birth) hA]
    have h := congrArg ENNReal.ofReal (hp A hA)
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using h
  rw [integral_trim (μ := R) (F.le birth) ha, he, ← integral_trim (μ := Q) (F.le birth) ha]

omit m in
/-- Up to the stop, a Brownian row supported on positive competing
variance has zero residual drift. -/
theorem drift_pairing_through_stop {σ : ℝ} {U Z X Y : ℝ≥0 → Ω → ℝ}
    {τ : Ω → ℝ≥0} {f : ℝ≥0 × Ω → ℝ}
    (hactive : ∀ t ω, f (t, ω) ≠ 0 → birth < t ∧ t ≤ τ ω ∧ 0 < Y t ω) (ω : Ω) :
    (∫ s, f (s, ω) * (σ * U s ω / (Z s ω * Real.sqrt (X s ω))) ∂hestonTimeMeasure H) =
      ∫ s, f (s, ω) * controlThrough (competitorAfterBirth birth σ U Z X Y) τ s ω
        ∂hestonTimeMeasure H := by
  apply integral_congr_ae
  exact ae_of_all _ fun s => by
    by_cases hf : f (s, ω) = 0
    · simp [hf]
    · obtain ⟨hb, ht, hy⟩ := hactive s ω hf
      simp [controlThrough, competitorAfterBirth, competitorControl, ht, hb, hy]

/-- Transport of a stopped transform with its original noise row. Its
initial expectation is taken under Q on the full birth sigma-algebra. -/
theorem stopped_test_mean_under_change
    (hc : IsStoppedDriftChange (F := F) (H := H) birth δ g hB₂ R N)
    {f : ℝ≥0 × Ω → ℝ} (v : Lp ℝ 2 (jointPredictableMeasure F Q H))
    (w : Lp ℝ 2 (jointPredictableMeasure F R H)) (hv : v =ᵐ[jointPredictableMeasure F Q H] f)
    (hw : v =ᵐ[jointPredictableMeasure F Q H] w)
    {test a A : Ω → ℝ} (ha : StronglyMeasurable[F birth] a) (hai : Integrable a R)
    (hrep : test =ᵐ[Q] fun ω => a ω + jointItoIntegralCLM H hB₂ v ω + A ω)
    (hcost : A =ᵐ[Q] fun ω => ∫ s, f (s, ω) * g s ω ∂hestonTimeMeasure H) :
    Integrable test R ∧ (∫ ω, test ω ∂R) = ∫ ω, a ω ∂Q := by
  obtain ⟨hR, _, hRQ, _, hPast, _, _, _, hN₂, hNm, hclock, _, _, hTransport⟩ := hc
  let _ : IsProbabilityMeasure R := hR
  have he : test =ᵐ[R] fun ω => a ω + jointItoIntegralCLM H hN₂ w ω := by
    filter_upwards [hRQ.ae_eq hrep, hRQ.ae_eq hcost, hTransport v w f hv hw] with ω ht hA hI
    rw [ht, hA, hI, add_assoc]
  have hi := (Lp.memLp (jointItoIntegralCLM H hN₂ w)).integrable one_le_two
  refine ⟨(hai.add hi).congr he.symm, ?_⟩
  rw [integral_congr_ae he, integral_add hai hi, integral_jointItoIntegralCLM_eq_zero H hN₂ hNm hclock,
    add_zero, integral_eq_at_birth hPast ha]

end RoughHeston.GirsanovPort

#print axioms RoughHeston.GirsanovPort.drift_pairing_through_stop
#print axioms RoughHeston.GirsanovPort.stopped_test_mean_under_change
