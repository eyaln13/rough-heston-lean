import JointHestonWeights
import ClusterKernelMoment

/-! Energy profiles in physical time for arbitrary predictable L² rows. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace RoughHeston

variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {H : ℝ≥0}

/-- A representative in the joint predictable L² space is also the
representative on a.e. time section for a.e. sample. -/
theorem joint_predictable_ae_on_time_sections {u f : ℝ≥0 × Ω → ℝ}
    (hu : u =ᵐ[jointPredictableMeasure F P H] f) :
    ∀ᵐ ω ∂P, ∀ᵐ t ∂hestonTimeMeasure H, u (t,ω)=f (t,ω) := by
  have hp : u =ᵐ[(MathFin.ItoIntegralCLM.timeMeasureHorizon H).prod P] f :=
    ae_eq_of_ae_eq_trim (hm := F.predictable_le_prod) hu
  have hs := (Measure.measurePreserving_swap (μ := P)
    (ν := MathFin.ItoIntegralCLM.timeMeasureHorizon H)).quasiMeasurePreserving.ae hp
  rw [hestonTimeMeasure_eq_horizon]
  exact Measure.ae_ae_of_ae_prod hs

/-- Exact energy for the Brownian noise row σ k(t) √U_t of one variance
coordinate. The deterministic weight may also be a kernel difference. -/
theorem joint_sqrt_row_lintegral_energy {σ : ℝ} {k : ℝ≥0 → ℝ} {U : ℝ≥0 → Ω → ℝ}
    (u : Lp ℝ 2 (jointPredictableMeasure F P H))
    (hu : u =ᵐ[jointPredictableMeasure F P H] (fun z => σ*k z.1*Real.sqrt (U z.1 z.2)))
    (hn : ∀ᵐ ω ∂P, ∀ᵐ t ∂hestonTimeMeasure H, 0 ≤ U t ω) :
    ∀ᵐ ω ∂P, (∫⁻ t, ENNReal.ofReal (‖u (t,ω)‖^2) ∂hestonTimeMeasure H) =
      ∫⁻ t, ENNReal.ofReal ((σ*k t)^2) * ENNReal.ofReal (U t ω) ∂hestonTimeMeasure H := by
  filter_upwards [joint_predictable_ae_on_time_sections hu,hn] with ω hω hn
  apply lintegral_congr_ae
  filter_upwards [hω,hn] with t ht hu
  rw [ht, Real.norm_eq_abs, sq_abs]
  change ENNReal.ofReal ((σ*k t*Real.sqrt (U t ω))^2) = _
  rw [mul_pow, Real.sq_sqrt hu, ENNReal.ofReal_mul (sq_nonneg _)]

#print axioms joint_predictable_ae_on_time_sections
#print axioms joint_sqrt_row_lintegral_energy

end RoughHeston
